(*
 * This module provides an interface to Ensemble
 * jobs.  Currently, there is only one local job.
 *)

open Refiner.Refiner.RefineError

open Thread_refiner_sig

module MakeThreadRefiner (Arg : ThreadRefinerArgSig) (Remote : RemoteSig) =
struct
   (************************************************************************
    * TYPES                                                                *
    ************************************************************************)

   (*
    * The types of values.
    *)
   type extract = Arg.extract

   (*
    * The tactic computes a tree of jobs to perform.
    *)
   type 'term t =
      Value of 'term list * extract
    | All1 of 'term tactic * 'term tactic * 'term
    | All2 of 'term tactic * 'term tactic list * 'term
    | AllF of 'term tactic * ('term list -> 'term t list) * 'term
    | First of 'term tactic list * 'term

   and 'term tactic = 'term -> 'term t

   (*
    * We make a fifo specifically for this module,
    * so we can make search easier.
    *)
   type 'a fifo =
      { mutable fifo_head : 'a list;
        mutable fifo_tail : 'a list
      }

   (*
    * The process keeps a flag for whether it is working
    * on an "and" or "or" job.
    *)
   type current =
      AndEntry
    | OrEntry

   (*
    * A job queue contains three parts.
    * The middle contains jobs that have not yet been
    * processed.
    *
    * Jobs can processed from the from or the back of
    * the queue.  In general, the oldest jobs will be in
    * the back of the queue.
    *
    * The front and back contains jobs that have been
    * completed, or jobs that are running either locally
    * or remotely.
    *)
   type 'term issued =
      Local of 'term tactic * 'term
    | Remote of 'term tactic * 'term * Remote.t
    | Complete of 'term list * extract
    | Rejected of exn

   type 'term queue =
      { queue_current : extract option;
        mutable queue_front : 'term issued list;
        mutable queue_pending : ('term tactic * 'term) fifo;
        mutable queue_back : 'term issued list
      }

   (*
    * The result of an evaluation can be success, or
    * failure for several reasons:
    *     1. the parent may have failed or canceled the job
    *     2. the job was fully explored and it failed
    *)
   type 'term eval_result =
      Success of 'term list * extract
    | Canceled
    | Failed of exn

   (*
    * A Process is either normal, or it has been canceled.
    *)
   type proc_state =
      ProcNormal
    | ProcCanceled

   (*
    * The Restart exception is used to restart the process after
    * an interrupt.  When the process is interrupted, control
    * returns the the main eval, and the job queue is reanalyzed
    * to see what has changed.
    *
    * The canceled exception occurs when a remote parent dies.
    *)
   exception ProcessRestart
   exception ProcessCanceled

   (*
    * A handle is issued to the server to track the thread state.
    *    Each handle has an owner, which may be a remote
    *    job, or it may be the current process.  The parent
    *    can cancel the entire job either by failing, or
    *    by explicit cancelation.
    *
    *    The process has a job queue, which may contain handles
    *    to jobs that have been farmed out to remote processes.
    *)
   type 'term process =
      { proc_parent : Remote.t option;
        proc_self : Remote.t;
        mutable proc_state : proc_state;
        mutable proc_queue : 'term queue list
      }

   type 'term handle = 'term process

   (*
    * The type of processors.
    * The server functions take two arguments,
    * the first of type 'a, and the second of type 'b,
    * and they produce a value of type 'c.
    *
    * The serve_handles is a list of processes to be evaluated.
    * The first process always gets service first.
    *
    * There are two threads:
    *   1. a local thread, which does almost all process management.
    *   2. an Ensemble thread which just does the communication.
    *      When Ensemble receives a message it does some minimal
    *      operation on the server, and the local thread does the
    *      cleanup.
    *
    * We assume assignment to serve_interrupt is atomic.
    *
    * The mutex is for serve_notify, which is the only
    * shared queue.
    *)
   and 'term server =
      { serve_mutex : Mutex.t;
        mutable serve_interrupt : bool;
        serve_notify : (Remote.t * 'term eval_result) list ref;
        mutable serve_processes : 'term process list;

        (* Ensemble info *)
        serve_server : ('term list * extract, 'term eval_result) Remote.server
      }

   (************************************************************************
    * FIFO OPERATIONS                                                      *
    ************************************************************************)

   (*
    * Spreader functions pair up items in lists.
    *)
   let spread_many_one args arg =
      List.map (function arg' -> arg', arg) args

   let spread_one_many arg args =
      List.map (function arg' -> arg, arg') args

   let rec spread_many_many args1 args2 =
      match args1, args2 with
         arg1 :: args1, arg2 :: args2 ->
            (arg1, arg2) :: spread_many_many args1 args2
       | [], [] ->
            []
       | _ ->
            raise (RefineError ("spread_many_many", StringError "argument lists do not have the same length"))

   let rec spread_ignore args2 t =
      match args2 with
         arg2 :: args2 ->
            ((fun _ -> arg2), t) :: spread_ignore args2 t
       | [] ->
            []

   (*
    * Pop the first element from the fifo.
    *)
   let fifo_pop_front fifo =
      match fifo with
         { fifo_head = x :: head } ->
            fifo.fifo_head <- head;
            x
       | { fifo_tail = tail } ->
            match List.rev tail with
               x :: tail ->
                  fifo.fifo_head <- tail;
                  fifo.fifo_tail <- [];
                  x
             | [] ->
                  raise (Invalid_argument "fifo_pop_front")

   (*
    * Prepend the items to the fifo.
    *)
   let fifo_prepend_front_many_one_pop fifo tacs arg =
      match tacs with
         tac :: tacs ->
            let rec collect = function
               tac :: tacs ->
                  (tac, arg) :: collect tacs
             | [] ->
                  fifo.fifo_head
            in
               fifo.fifo_head <- collect tacs;
               tac, arg
       | [] ->
            raise (Failure "fifo_prepend_front_many_one_pop")

   (************************************************************************
    * IMPLEMENTATION                                                       *
    ************************************************************************)

   (*
    * The Ensemble notifier.
    *)
   let notify lock queue msgs =
      Mutex.lock lock;
      queue := !queue @ msgs;
      Mutex.unlock lock

   (*
    * Create a factory with some number of initial threads.
    *)
   let create _ =
      let mutex = Mutex.create () in
      let notify_queue = ref [] in
      let serve =
         { serve_mutex = Mutex.create ();
           serve_interrupt = false;
           serve_notify = notify_queue;
           serve_processes = [];
           serve_server = Remote.create_server (notify mutex notify_queue)
         }
      in
         serve

   (*
    * Create a process with a single job.
    *)
   let create_process info parent =
      { proc_parent = parent;
        proc_self = Remote.create info.serve_server;
        proc_state = ProcNormal;
        proc_queue = []
      }

   (*
    * Append a new process with the identifier,
    * and start it in the args as an and-choice.
    *)
   let append_process info proc remote arg1 arg2 =
      let queue =
         { queue_current = None;
           queue_front = [Local (arg1, arg2)];
           queue_pending = { fifo_head = []; fifo_tail = [] };
           queue_back = []
         }
      in
      let proc =
         { proc_parent = Some proc.proc_self;
           proc_self = remote;
           proc_state = ProcNormal;
           proc_queue = [queue]
         }
      in
         info.serve_processes <- info.serve_processes @ [proc]

   (*
    * Process queue management.
    *)
   let add_process info proc =
      info.serve_processes <- proc :: info.serve_processes

   let remove_process info proc =
      info.serve_processes <- List_util.removeq proc info.serve_processes

   (*
    * Queues with initialized entries.
    *)
   let create_queue spread tacs current args =
      match spread tacs args with
         (arg1, arg2) :: head ->
            { queue_current = current;
              queue_front = [Local (arg1, arg2)];
              queue_pending = { fifo_head = head; fifo_tail = [] };
              queue_back = []
            }
       | [] ->
            { queue_current = current;
              queue_front = [];
              queue_pending = { fifo_head = []; fifo_tail = [] };
              queue_back = []
            }

   let create_queue_one_many tacs current args =
      create_queue spread_one_many tacs current args

   let create_queue_many_many tacs current args =
      create_queue spread_many_many tacs current args

   let create_queue_many_one tacs current args =
      create_queue spread_many_one tacs current args

   let create_queue_fun t current args =
      create_queue spread_ignore t current args

   (************************************************************************
    * INTERRUPT MANAGEMENT                                                 *
    ************************************************************************)

   (*
    * Cancel all remote jobs in the queues.
    *)
   let cancel_remote_jobs info proc queues =
      let cancel_remote = function
         Remote (_, _, remote) ->
            Remote.cancel info.serve_server remote
       | _ ->
            ()
      in
      let cancel_queue { queue_front = front; queue_back = back } =
         List.iter cancel_remote front;
         List.iter cancel_remote back
      in
         List.iter cancel_queue queues

   (*
    * Replace a remote value with the actual value.
    * We search all the queues until the remote is found.
    *)
   let replace_remote info remote newval =
      let rec replace_list = function
         Remote (_, _, remote') :: tl when Remote.eq remote' remote ->
            newval :: tl
       | entry :: tl ->
            entry :: replace_list tl
       | [] ->
            raise Not_found
      in
      let replace_queue queue =
         let { queue_front = front; queue_back = back } = queue in
            try
               queue.queue_front <- replace_list front;
               true
            with
               Not_found ->
                  try
                     queue.queue_back <- replace_list back;
                     true
                  with
                     Not_found ->
                        false
      in
      let replace_process proc =
         List.exists replace_queue proc.proc_queue
      in
         List.exists replace_process info.serve_processes

   (*
    * When a cancelation occurs, that means that some process died
    * because of a processor or network failure.  We first check
    * if the remote job is the parent of a process, in which case we
    * delete the entire process.  Otherwise, if the remote job
    * is a child, then we queue the goal as a new process in
    * the local processor.
    *)
   let handle_process_cancelation info proc remote =
      let rec search_queue = function
         Remote (arg1, arg2, remote') :: tl when Remote.eq remote' remote ->
            arg1, arg2
       | entry :: tl ->
            search_queue tl
       | [] ->
            raise Not_found
      in
      let rec search queue =
         let { queue_front = front; queue_back = back } = queue in
            try
               let arg1, arg2 = search_queue front in
                  append_process info proc remote arg1 arg2;
                  true
            with
               Not_found ->
                  try
                     let arg1, arg2 = search_queue back in
                        append_process info proc remote arg1 arg2;
                        true
                  with
                     Not_found ->
                        false
      in
         List.exists search proc.proc_queue

   let handle_cancelation info remote =
      let cancel_parent proc =
         match proc.proc_parent with
            Some parent ->
               if Remote.eq parent remote then
                  begin
                     cancel_remote_jobs info proc proc.proc_queue;
                     proc.proc_queue <- [];
                     proc.proc_state <- ProcCanceled
                  end
          | None ->
               ()
      in
      let processes = info.serve_processes in
         List.iter cancel_parent info.serve_processes;
         List.exists (fun proc -> handle_process_cancelation info proc remote) processes

   (*
    * Handle a single notification from Ensemble.
    *)
   let handle_notification info (remote, message) =
      let _ =
         match message with
            Success (args, ext) ->
               replace_remote info remote (Complete (args, ext))
          | Failed exn ->
               replace_remote info remote (Rejected exn)
          | Canceled ->
               handle_cancelation info remote
      in
         ()

   (*
    * Interrupt management.
    * An interrupt occurs because Ensemble has returned a value
    * for some of the remote jobs.  We look through all the job
    * queues and see what has completed.
    *)
   let handle_interrupt info proc =
      Mutex.lock info.serve_mutex;
      List.iter (handle_notification info) !(info.serve_notify);
      info.serve_notify := [];
      Mutex.unlock info.serve_mutex;
      raise ProcessRestart

   (************************************************************************
    * SEARCH                                                               *
    ************************************************************************)

   (*
    * Wait for remote processes.
    * Right now this is not implemented.
    *)
   let wait info proc queue =
      raise (Failure "wait")

   (*
    * An and-queue is complete if the fifo is empty,
    * and if the front and back are all completed.
    *)
   let is_and_queue_complete queue =
      match queue with
         { queue_front = front;
           queue_pending = { fifo_head = []; fifo_tail = [] };
           queue_back = back
         } ->
            let is_complete = function
               Complete _ ->
                  true
             | _ ->
                  false
            in
               List.for_all is_complete front & List.for_all is_complete back
       | _ ->
            false

   (*
    * An or-queue is complete if the first entry in the front
    * has been solved.
    *)
   let is_or_queue_complete { queue_front = front } =
      let rec search = function
         [Complete _] ->
            true
       | _ :: t ->
            search t
       | [] ->
            false
      in
         search front

   (*
    * Or-queue is false if all jobs have failed.
    *)
   let is_or_queue_false queue =
      match queue with
         { queue_front = front;
           queue_pending = { fifo_head = []; fifo_tail = [] }
         } ->
            let rec search = function
               Rejected _ :: t ->
                  search t
             | _ :: t ->
                  false
             | [] ->
                  true
            in
               search front
       | _ ->
            false

   (*
    * Collect all the results in the and-queue.
    * We assume the queue is complete.
    *)
   let flatten_and_queue { queue_current = current;
                           queue_front = front;
                           queue_back = back
       } =
      let rec collect_back = function
         Complete (args, ext) :: tl ->
            let argsl, extl = collect_back tl in
               args @ argsl, ext :: extl
       | [] ->
            [], []
       | _ ->
            raise (Failure "flatten_and_queue")
      in
      let rec collect_front = function
         Complete (args, ext) :: tl ->
            let argsl, extl = collect_front tl in
               args @ argsl, ext :: extl
       | [] ->
            collect_back back
       | _ ->
            raise (Failure "flatten_and_queue")
      in
      let args, extl = collect_front front in
         match current with
            Some ext ->
               args, Arg.compose ext extl
          | None ->
               raise (Invalid_argument "flatten_and_queue")

   (*
    * Cleanup the and-queue.
    * If there are no remote jobs, return the result of the evaluation.
    *)
   let cleanup_and info proc =
      let queue = List.hd proc.proc_queue in
         if is_and_queue_complete queue then
            flatten_and_queue queue
         else
            wait info proc queue

   let cleanup_or info proc =
      let queue = List.hd proc.proc_queue in
         match queue.queue_front with
            [Complete (args, ext)] ->
               args, ext
          | _ ->
               wait info proc queue

   (*
    * Process all the jobs in the queue.
    *)
   let rec compute_and info proc queue front (fifo : ('term tactic * 'term) fifo) arg1 arg2 =
      queue.queue_front <- Local (arg1, arg2) :: front;
      if info.serve_interrupt then
         handle_interrupt info proc;
      let args, ext =
         match arg1 arg2 with
            Value (args, ext) ->
               args, ext
          | All1 (tac1, tac2, arg) ->
               compute_and1 info proc tac1 tac2 arg
          | All2 (tac1, tacs2, arg) ->
               compute_and2 info proc tac1 tacs2 arg
          | AllF (tac1, tacf, arg) ->
               compute_andf info proc tac1 tacf arg
          | First (tacs, arg) ->
               compute_first info proc tacs arg
      in
      let front = Complete (args, ext) :: front in
         queue.queue_front <- front;
         match queue.queue_pending with
            { fifo_head = []; fifo_tail = [] } ->
               cleanup_and info proc
          | fifo ->
               let arg1, arg2 = fifo_pop_front fifo in
                  compute_and info proc queue front fifo arg1 arg2

   (*
    * Compute the disjunction with the assumption that there
    * are no remote jobs in this queue (this will be the common
    * case).  This means that the first jobs to succeed is good
    * enough.
    *)
   and compute_or info proc queue front
       (fifo : ('term tactic * 'term) fifo)
       (arg1 : 'term tactic) (arg2 : 'term) =
      queue.queue_front <- Local (arg1, arg2) :: front;
      if info.serve_interrupt then
         handle_interrupt info proc;
      try
         let args, ext =
            match arg1 arg2 with
               Value (args, ext) ->
                  (* Success *)
                  args, ext
             | All1 (tac1, tac2, arg) ->
                  compute_and1 info proc tac1 tac2 arg
             | All2 (tac1, tacs2, arg) ->
                  compute_and2 info proc tac1 tacs2 arg
             | AllF (tac1, tacf, arg) ->
                  compute_andf info proc tac1 tacf arg
             | First (tacs, arg2) ->
                  (* Just fold the subgoals inline *)
                  let arg1, arg2 = fifo_prepend_front_many_one_pop fifo tacs arg2 in
                     compute_or info proc queue front fifo arg1 arg2
         in
            queue.queue_front <- Complete (args, ext) :: front;
            cleanup_or info proc
      with
         (RefineError _) as exn ->
            queue.queue_front <- front;
            match fifo with
               { fifo_head = []; fifo_tail = [] } ->
                  raise exn
             | fifo ->
                  let arg1, arg2 = fifo_pop_front fifo in
                     compute_or info proc queue front fifo arg1 arg2

   (*
    * Run the first tactic, then apply the second tactic
    * to all the subgoals.
    *)
   and compute_new_and info proc tac1 create arg =
      let args, ext =
         match tac1 arg with
            Value (args, ext) ->
               args, ext
          | All1 (tac1, tac2, arg) ->
               compute_and1 info proc tac1 tac2 arg
          | All2 (tac1, tacs2, arg) ->
               compute_and2 info proc tac1 tacs2 arg
          | AllF (tac1, tacf, arg) ->
               compute_andf info proc tac1 tacf arg
          | First (tacs, arg2) ->
               compute_first info proc tacs arg2
      in
      let queue = create (Some ext) args in
         match queue with
            { queue_front = Local (arg1, arg2) :: front; queue_pending = fifo } ->
               proc.proc_queue <- queue :: proc.proc_queue;
               compute_and info proc queue front fifo arg1 arg2
          | { queue_front = [] } ->
               (* No jobs were submitted *)
               raise (RefineError ("compute_new_and", StringError "no jobs"))
          | _ ->
               raise (Failure "compute_new_and")

   and compute_and1 info proc tac1 tac2 arg =
      compute_new_and info proc tac1 (create_queue_one_many tac2) arg

   and compute_and2 info proc tac1 tacs2 arg =
      compute_new_and info proc tac1 (create_queue_many_many tacs2) arg

   and compute_andf info proc tac1 tacf arg =
      let args, ext =
         match tac1 arg with
            Value (args, ext) ->
               args, ext
          | All1 (tac1, tac2, arg) ->
               compute_and1 info proc tac1 tac2 arg
          | All2 (tac1, tacs2, arg) ->
               compute_and2 info proc tac1 tacs2 arg
          | AllF (tac1, tacf, arg) ->
               compute_andf info proc tac1 tacf arg
          | First (tacs, arg2) ->
               compute_first info proc tacs arg2
      in
      (* We use List.hd args, but we just need any term to make typing work *)
      let queue = create_queue_fun (tacf args) (Some ext) (List.hd args) in
         match queue with
            { queue_front = Local (arg1, arg2) :: front; queue_pending = fifo } ->
               proc.proc_queue <- queue :: proc.proc_queue;
               compute_and info proc queue front fifo arg1 arg2
          | { queue_front = [] } ->
               (* No jobs were submitted *)
               raise (RefineError ("compute_new_and", StringError "no jobs"))
          | _ ->
               raise (Failure "compute_new_and")

   and compute_first info proc tacs arg =
      let queue = create_queue_many_one tacs None arg in
         match queue with
            { queue_front = Local (arg1, arg2) :: front; queue_pending = fifo } ->
               proc.proc_queue <- queue :: proc.proc_queue;
               compute_or info proc queue front fifo arg1 arg2
          | { queue_front = [] } ->
               (* No jobs were submitted *)
               raise (RefineError ("compute_first", StringError "no jobs"))
          | _ ->
               raise (Failure "compute_first")

   (************************************************************************
    * RESTART                                                              *
    ************************************************************************)

   let rec restart_and info proc queues =
      let rec search = function
         Rejected exn :: _ ->
            raise exn
       | _ :: t ->
            search t
       | [] ->
            ()
      in
         match queues with
            { queue_front = Local (arg1, arg2) :: front;
              queue_pending = fifo;
              queue_back = back
            } as queue :: queues ->
               search front;
               search back;
               proc.proc_queue <- queue :: proc.proc_queue;
               if queues = [] then
                  compute_and info proc queue front fifo arg1 arg2
               else
                  begin
                     let args, extl = restart_queue info proc queues in
                        queue.queue_front <- front;
                        match queue.queue_pending with
                           { fifo_head = []; fifo_tail = [] } ->
                              cleanup_and info proc
                         | fifo ->
                              let arg1, arg2 = fifo_pop_front fifo in
                                 compute_and info proc queue front fifo arg1 arg2
                  end

          | queue :: queues ->
               (* This queue is complete, or remote jobs are pending *)
               cancel_remote_jobs info proc queues;
               if is_and_queue_complete queue then
                  flatten_and_queue queue
               else
                  wait info proc queue

          | [] ->
               raise (Failure "restart_and")

   and restart_or info proc queues =
      let rec search = function
         [Complete (args, ext)] ->
            args, ext
       | h :: t ->
            search t
       | [] ->
            raise Not_found
      in
         match queues with
            { queue_front = Local (arg1, arg2) :: front;
              queue_pending = fifo
            } as queue :: queues ->
               begin
                  try
                     let args_ext = search front in
                        cancel_remote_jobs info queue queues;
                        args_ext
                  with
                     Not_found ->
                        proc.proc_queue <- queue :: proc.proc_queue;
                        if queues = [] then
                           compute_or info proc queue front fifo arg1 arg2
                        else
                           try
                              let args, ext = restart_queue info proc queues in
                                 queue.queue_front <- Complete (args, ext) :: front;
                                 cleanup_or info proc
                           with
                              (RefineError _) as exn ->
                                 queue.queue_front <- front;
                                 match fifo with
                                    { fifo_head = []; fifo_tail = [] } ->
                                       raise exn
                                  | fifo ->
                                       let arg1, arg2 = fifo_pop_front fifo in
                                          compute_or info proc queue front fifo arg1 arg2
               end
          | { queue_front = Rejected exn :: _ } as queue :: queues ->
               if is_or_queue_false queue then
                  raise exn
               else if is_or_queue_complete queue then
                  cleanup_or info proc
               else
                  wait info proc queue
          | _ ->
               raise (Failure "restart_queue_or")

   and restart_queue info proc = function
      (queue :: _) as queues ->
         if queue.queue_current = None then
            restart_or info proc queues
         else
            restart_and info proc queues
    | [] ->
         raise (Invalid_argument "restart_queue")

   let rec restart_process info proc =
      let queue = List.rev proc.proc_queue in
         proc.proc_queue <- [];
         try restart_queue info proc queue with
            ProcessRestart ->
               restart_process info proc
          | exn ->
               remove_process info proc;
               raise exn

   (************************************************************************
    * IMPLEMENTATION                                                       *
    ************************************************************************)

   (*
    * The constructors just note the construction.
    *)
   let create_value args ext =
      Value (args, ext)

   let first tacs p =
      First (tacs, p)

   let compose1 tac1 tac2 p =
      All1 (tac1, tac2, p)

   let compose2 tac1 tacs2 p =
      All2 (tac1, tacs2, p)

   let composef tac1 tacf p =
      AllF (tac1, tacf, p)

   (*
    * Evaluate a thread.
    * Create a new process to serve the thread.
    *)
   let eval info prog =
      let proc = create_process info None in
      let args, ext =
         try
            match prog with
               Value (arg, ext) ->
                  arg, ext
             | All1 (tac1, tac2, arg) ->
                  compute_and1 info proc tac1 tac2 arg
             | All2 (tac1, tacs2, arg) ->
                  compute_and2 info proc tac1 tacs2 arg
             | AllF (tac1, tacf, arg) ->
                  compute_andf info proc tac1 tacf arg
             | First (tacs, arg2) ->
                  compute_first info proc tacs arg2
         with
            ProcessRestart ->
               restart_process info proc
          | exn ->
               remove_process info proc;
               raise exn
      in
         remove_process info proc;
         args, ext
end

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
