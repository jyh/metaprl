(*
 * This is the null thread implementation.
 *)

open Printf
open Nl_debug

open Refiner.Refiner.RefineError

open Thread_refiner_sig

let debug_strategy =
   create_debug (**)
      { debug_name = "strategy";
        debug_description = "Show tactic strategy";
        debug_value = false
      }

module MakeThreadRefiner (Arg : ThreadRefinerArgSig) =
struct
   (************************************************************************
    * TYPES                                                                *
    ************************************************************************)

   type extract = Arg.extract

   type 'term t =
      Value of 'term list * extract
    | All1 of 'term tactic * 'term tactic * 'term
    | All2 of 'term tactic * 'term tactic list * 'term
    | AllF of 'term tactic * ('term list -> 'term t list) * 'term
    | First of 'term tactic list * 'term

   and 'term tactic = 'term -> 'term t

   type 'term server = out_channel -> 'term -> unit

   (*
    * We keep a stack of goals.
    *)
   type 'term entry =
      AndEntryThen1 of 'term tactic * 'term tactic * 'term
    | AndEntryThen2 of 'term tactic * 'term tactic list * 'term
    | AndEntryThenF of 'term tactic * ('term list -> 'term t list) * 'term
    | AndEntry1 of 'term tactic * 'term list * extract * ('term list * extract) list
    | AndEntry2 of 'term tactic list * 'term list * extract * ('term list * extract) list
    | AndEntryF of 'term t list * extract * ('term list * extract) list
    | OrEntry of 'term tactic list * 'term
    | ValueEntry of 'term list * extract

   (************************************************************************
    * IMPLEMENTATION                                                       *
    ************************************************************************)

   (*
    * No info for server.
    *)
   let create printer =
      printer

   (*
    * Constructors.
    *)
   let create_value args ext =
      Value (args, ext)

   let first tacs arg =
      First (tacs, arg)

   let compose1 tac1 tac2 arg =
      All1 (tac1, tac2, arg)

   let compose2 tac1 tacs2 arg =
      All2 (tac1, tacs2, arg)

   let composef tac1 tacf arg =
      AllF (tac1, tacf, arg)

   (*
    * Printing.
    *)
   let print_term_list debug_print out terms =
      let print_term t =
         fprintf out "\t\targ = << %a >>%t" debug_print t eflush
      in
         List.iter print_term terms

   let print_stack_entry debug_print = function
      AndEntryThen1 (_, _, arg) ->
         eprintf "\tAndEntryThen1: %a%t" debug_print arg eflush
    | AndEntryThen2 (_, _, arg) ->
         eprintf "\tAndEntryThen2: %a%t" debug_print arg eflush
    | AndEntryThenF (_, _, arg) ->
         eprintf "\tAndEntryThenF: %a%t" debug_print arg eflush
    | AndEntry1 (_, args, _, _) ->
         eprintf "\tAndEntry1:\n%a" (print_term_list debug_print) args
    | AndEntry2 (_, args, _, _) ->
         eprintf "\tAndEntry2:\n%a" (print_term_list debug_print) args
    | AndEntryF _ ->
         eprintf "\tAndEntryF%t" eflush
    | OrEntry (_, arg) ->
         eprintf "\tOrEntry: %a%t" debug_print arg eflush
    | ValueEntry (args, _) ->
         eprintf "\tValueEntry:\n%a" (print_term_list debug_print) args

   let print_stack printer stack =
      eprintf "Stack:%t" eflush;
      List.iter (print_stack_entry printer) stack

   (*
    * Pop the stack until the next choice goal,
    * or until the stack is empty.
    *)
   let rec pop_failure exn = function
      (entry :: stack) as stack' ->
         begin
            match entry with
               AndEntry1 _
             | AndEntry2 _
             | AndEntryF _
             | AndEntryThen1 _
             | AndEntryThen2 _
             | AndEntryThenF _
             | OrEntry ([], _) ->
                  pop_failure exn stack
             | OrEntry _ ->
                  stack'
             | ValueEntry _ ->
                  raise (Invalid_argument "pop_failure")
         end
    | [] ->
         raise exn

   (*
    * Pop a successful entry.
    *)
   let rec flatten argsl extl = function
      (args, ext) :: subgoals ->
         flatten (args @ argsl) (ext :: extl) subgoals
    | [] ->
         argsl, extl

   let rec pop_flatten ext subgoals stack =
      let argsl, extl = flatten [] [] subgoals in
         pop_success argsl (Arg.compose ext extl) stack

   and pop_success args ext = function
      entry :: stack ->
         begin
            match entry with
               AndEntryThen1 (_, tac, _) ->
                  if args = [] then
                     pop_success args ext stack
                  else
                     AndEntry1 (tac, args, ext, []) :: stack
             | AndEntryThen2 (_, tacs, _) ->
                  if args = [] then
                     pop_success args ext stack
                  else
                     AndEntry2 (tacs, args, ext, []) :: stack
             | AndEntryThenF (_, tacf, _) ->
                  if args <> [] then
                     try
                        let goals = tacf args in
                           AndEntryF (goals, ext, []) :: stack
                     with
                        (RefineError _) as exn ->
                           pop_failure exn stack
                  else
                     pop_success args ext stack
             | AndEntry1 (tac, goals, ext', subgoals) ->
                  if goals = [] then
                     pop_flatten ext ((args, ext') :: subgoals) stack
                  else
                     AndEntry1 (tac, goals, ext, (args, ext') :: subgoals) :: stack
             | OrEntry _ ->
                  pop_success args ext stack
             | AndEntry2 (((_ :: _) as tacs), ((_ :: _) as goals), ext', subgoals) ->
                  AndEntry2 (tacs, goals, ext, (args, ext') :: subgoals) :: stack
             | AndEntry2 ([], [], ext', subgoals) ->
                  pop_flatten ext ((args, ext') :: subgoals) stack
             | AndEntry2 _ ->
                  pop_failure (RefineError ("thenL", StringError "mismatched subgoal list")) stack
             | AndEntryF (goals, ext', subgoals) ->
                  if goals = [] then
                     pop_flatten ext ((args, ext') :: subgoals) stack
                  else
                     AndEntryF (goals, ext, (args, ext') :: subgoals) :: stack
             | ValueEntry _ ->
                  raise (Invalid_argument "pop_success")
         end
    | [] ->
         [ValueEntry (args, ext)]

   (*
    * Push a new goal onto the stack.
    *)
   let push_goal goal stack =
      match goal with
         Value (args, ext) ->
            pop_success args ext stack
       | First (tacs, arg) ->
            OrEntry (tacs, arg) :: stack
       | All1 (tac1, tac2, arg) ->
            AndEntryThen1 (tac1, tac2, arg) :: stack
       | All2 (tac1, tacs2, arg) ->
            AndEntryThen2 (tac1, tacs2, arg) :: stack
       | AllF (tac1, tacf, arg) ->
            AndEntryThenF (tac1, tacf, arg) :: stack

   (*
    * Evaluate the stack.
    *)
   let eval_entry entry stack =
      match entry with
         AndEntry1 (tac, goal :: goals, ext, subgoals) ->
            begin
               try
                  let goal' = tac goal in
                     push_goal goal' (AndEntry1 (tac, goals, ext, subgoals) :: stack)
               with
                  (RefineError _) as exn ->
                     pop_failure exn stack
            end
       | AndEntry2 (tac :: tacs, goal :: goals, ext, subgoals) ->
            begin
               try
                  let goal' = tac goal in
                     push_goal goal' (AndEntry2 (tacs, goals, ext, subgoals) :: stack)
               with
                  (RefineError _) as exn ->
                     pop_failure exn stack
            end
       | AndEntryF (arg :: args, ext, subgoals) ->
            push_goal arg (AndEntryF (args, ext, subgoals) :: stack)
       | OrEntry ([tac], goal) ->
            begin
               try
                  let goal' = tac goal in
                     push_goal goal' (OrEntry ([], goal) :: stack)
               with
                  (RefineError _) as exn ->
                     pop_failure exn stack
            end
       | OrEntry (tac :: tacs, goal) ->
            begin
               try
                  let goal' = tac goal in
                     push_goal goal' (OrEntry (tacs, goal) :: stack)
               with
                  RefineError _ ->
                     OrEntry (tacs, goal) :: stack
            end
       | AndEntryThen1 (tac1, _, goal) ->
            begin
               try
                  let goal' = tac1 goal in
                     push_goal goal' (entry :: stack)
               with
                  (RefineError _) as exn ->
                     pop_failure exn stack
            end
       | AndEntryThen2 (tac1, _, goal) ->
            begin
               try
                  let goal' = tac1 goal in
                     push_goal goal' (entry :: stack)
               with
                  (RefineError _) as exn ->
                     pop_failure exn stack
            end
       | AndEntryThenF (tac1, _, goal) ->
            begin
               try
                  let goal' = tac1 goal in
                     push_goal goal' (entry :: stack)
               with
                  (RefineError _) as exn ->
                     pop_failure exn stack
            end
       | AndEntry1 _
       | AndEntry2 _
       | AndEntryF _
       | OrEntry _
       | ValueEntry _ ->
            raise (Invalid_argument "expand: invalid stack entry")

   (*
    * Loop until exception is raised.
    *)
   let rec eval_stack printer stack =
      if !debug_strategy then
         print_stack printer stack;
      match stack with
         [ValueEntry (args, ext)] ->
            args, ext
       | entry :: stack ->
            eval_stack printer (eval_entry entry stack)
       | [] ->
            raise (Invalid_argument "eval_stack")

   (*
    * The evaluator just does an appication.
    *)
   let eval printer goal =
      if !debug_strategy then
         eprintf "Refinement starting%t" eflush;
      let x = eval_stack printer (push_goal goal []) in
         if !debug_strategy then
            eprintf "Refinement finished%t" eflush;
         x
end

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
