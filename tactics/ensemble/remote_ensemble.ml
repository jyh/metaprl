(*
 * This is a null-implementation of the
 * remote server.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/htmlman/default.html or visit http://metaprl.org/
 * for more information.
 *
 * Copyright (C) 1998 Jason Hickey, Cornell University
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 *
 * Author: Jason Hickey
 * jyh@cs.cornell.edu
 *)

open Lm_debug
open Lm_printf

open Lm_thread_util

open Remote_queue_sig

let debug_queue =
   create_debug (**)
      { debug_name = "queue";
        debug_description = "Show remote queue operations";
        debug_value = false
      }

module Remote =
struct
   (************************************************************************
    * MODULES                                                              *
    ************************************************************************)

   (*
    * This is the Ensemble queue abstraction.
    *)
   module Queue = Remote_lazy_queue.Make (Ensemble_queue.Queue)

   (************************************************************************
    * TYPES                                                                *
    ************************************************************************)

   (*
    * These are the possible responses to
    * a job.  The RemoteCanceled may be returned
    * if the job was canceled, but it is not required.
    * If the job was not canceled, the Cancel event is
    * never returned.
    *)
   type 'b response =
      RemoteCanceled
    | RemoteSuccess of 'b

   (*
    * A handle has a job argument,
    * and a cell for returning the value.
    *)
   type ('a, 'b) handle =
      { hand_hand : ('a, 'b) Queue.handle;
        mutable hand_value : 'b response option
      }

   (*
    * Local jobs that are being served by the
    * local server.  We keep the handle that
    * references the job.
    *)
   type ('a, 'b) local =
      { mutable local_canceled : bool;
        local_lock : ('a, 'b) Queue.lock
      }

   (*
    * Share keys are passed to the queue.
    *)
   type 'c key = 'c Queue.key

   (*
    * Scheduler gets messages either as upcalls,
    * or from passed events.
    *)
   type ('a, 'b, 'c) message =
      MessageUpcall of ('a, 'b) Queue.upcall
    | MessageEvent of 'c

   (*
    * An event has a polling function that returns
    * one of three values:
    *    EventSuccess x: got a value from the event
    *    EventFailure: no value is available.
    *    EventBlock event: a thread event to block on
    *)
   type 'a poll_value =
      PollSuccess of 'a
    | PollEvent of 'a Lm_thread_event.event
    | PollFailure

   type 'a event = unit -> 'a poll_value

   (*
    * The main job keeps a queue of the locally submitted jobs,
    * as well as the locally issued jobs.
    *)
   type ('a, 'b, 'c) t =
      { queue_queue : ('a, 'b, 'c) Queue.t;
        queue_upcall : ('a, 'b) Queue.upcall Lm_thread_event.event;
        mutable queue_lock : ('a, 'b) Queue.lock list;
        mutable queue_pending : ('a, 'b) handle list;
        mutable queue_local : ('a, 'b) local list
      }

   (************************************************************************
    * IMPLEMENTATION                                                       *
    ************************************************************************)

   (*
    * Create a new empty queue.
    *)
   let create () =
      let queue = Queue.create false in
      let event = Queue.event_of_queue queue in
      let queue =
         { queue_queue = queue;
           queue_upcall = event;
           queue_lock = [];
           queue_pending = [];
           queue_local = []
         }
      in
         queue

   (*
    * Submit a new job.  Just create a handle and queue the job.
    *)
   let submit queue arg =
      let hand =
         { hand_hand = Queue.add queue.queue_queue arg;
           hand_value = None
         }
      in
         queue.queue_pending <- hand :: queue.queue_pending;
         hand

   (*
    * Get the value associated with a handle.
    *)
   let arg_of_handle { hand_hand = hand } =
      Queue.arg_of_handle hand

   (*
    * Get the receive event for the handle.
    *)
   let event_of_handle queue hand () =
      match hand.hand_value with
         Some (RemoteSuccess x) ->
            PollSuccess x
       | _ ->
            PollFailure

   (*
    * Cancel a submitted event.
    *)
   let cancel_handle queue hand =
      hand.hand_value <- Some RemoteCanceled;
      try
         queue.queue_pending <- Lm_list_util.removeq hand queue.queue_pending;
         Queue.delete queue.queue_queue hand.hand_hand
      with
         Failure "removeq" ->
            ()

   (*
    * When polled, the request event will try to pop a pending
    * job for local service.
    *)
   let request queue () =
      match queue.queue_lock with
         lock :: locks ->
            let local =
               { local_canceled = false;
                 local_lock = lock
               }
            in
               queue.queue_lock <- locks;
               queue.queue_local <- local :: queue.queue_local;
               PollSuccess local
       | [] ->
            (* Issue a lock request to the Queue *)
            if !debug_queue then
               begin
                  lock_printer ();
                  eprintf "Remote_ensemble.request%t" eflush;
                  unlock_printer ()
               end;
            Queue.lock queue.queue_queue;
            PollFailure

   (*
    * Get the argument for the local event.
    *)
   let arg_of_local local =
      Queue.arg_of_lock local.local_lock

   (*
    * Poll the local event.
    *)
   let event_of_local queue local () =
      if local.local_canceled then
         PollSuccess ()
      else
         PollFailure

   (*
    * Cancel a local job.
    * The job is pushed back to the shared queue.
    *)
   let cancel_local queue local =
      Queue.cancel queue.queue_queue local.local_lock;
      queue.queue_local <- Lm_list_util.removeq local queue.queue_local

   (*
    * Return a value for the local job.
    *)
   let return_local queue local x =
      Queue.unlock queue.queue_queue local.local_lock x;
      queue.queue_local <- Lm_list_util.removeq local queue.queue_local

   (************************************************************************
    * SHARED MEMORY                                                        *
    ************************************************************************)

   (*
    * Pass the share to the queue.
    *)
   let share queue x =
      Queue.share queue.queue_queue x

   let arg_of_key queue key =
      Queue.arg_of_key queue.queue_queue key

   (************************************************************************
    * SCHEDULING                                                           *
    ************************************************************************)

   (*
    * Handle a cancelation returned by the queue server.
    *)
   let handle_cancel queue lock =
      let rec remove = function
         local :: locals ->
            if local.local_lock == lock then
               begin
                  local.local_canceled <- true;
                  locals
               end
            else
               local :: remove locals
       | [] ->
            []
      in
         queue.queue_local <- remove queue.queue_local

   (*
    * Handle a result from the shared queue.
    *)
   let handle_result queue hand x =
      let rec remove = function
         hand' :: hands ->
            if hand'.hand_hand == hand then
               begin
                  hand'.hand_value <- Some (RemoteSuccess x);
                  hands
               end
            else
               hand' :: remove hands
       | [] ->
            if !debug_queue then
               begin
                  lock_printer ();
                  eprintf "Remote_ensemble.handle_result: lost result%t" eflush;
                  unlock_printer ()
               end;
            []
      in
         queue.queue_pending <- remove queue.queue_pending

   (*
    * Wrap a function around an event.
    *)
   let wrap poll f () =
      match poll () with
         PollSuccess x ->
            PollSuccess (f x)
       | PollFailure ->
            PollFailure
       | PollEvent event ->
            PollEvent (Lm_thread_event.wrap event f)

   (*
    * Wrap a system event.
    *)
   let wrap_event event () =
      PollEvent event

   (*
    * During a select, poll all the events.
    * Collect the system events and block on them if no polls
    * are successful.
    *)
   let rec select queue events =
      let rec poll block_events = function
         event :: events ->
            begin
               match event () with
                  PollSuccess x ->
                     MessageEvent x
                | PollFailure ->
                     poll block_events events
                | PollEvent event ->
                     poll (event :: block_events) events
            end
       | [] ->
            let events =
               [Lm_thread_event.wrap queue.queue_upcall (fun msg -> MessageUpcall msg);
                Lm_thread_event.wrap (Lm_thread_event.choose block_events) (fun msg -> MessageEvent msg)]
            in
               if !debug_queue then
                  begin
                     lock_printer ();
                     eprintf "Remote_ensemble.select: begin%t" eflush;
                     unlock_printer ()
                  end;
               let x = Lm_thread_event.sync 0 (Lm_thread_event.choose events) in
                  if !debug_queue then
                     begin
                        lock_printer ();
                        eprintf "Remote_ensemble.select: end%t" eflush;
                        unlock_printer ()
                     end;
                  x
      in
         match poll [] events with
            MessageUpcall upcall ->
               begin
                  (* Handle the upcall and try again *)
                  match upcall with
                     Queue.UpcallCancel lock ->
                        handle_cancel queue lock
                   | Queue.UpcallResult (hand, x) ->
                        handle_result queue hand x
                   | Queue.UpcallLock lock ->
                        queue.queue_lock <- lock :: queue.queue_lock
                   | Queue.UpcallPreLock lock ->
                        queue.queue_lock <- lock :: queue.queue_lock
                   | Queue.UpcallView ->
                        ()
               end;
               None
          | MessageEvent x ->
               (* Cleanup pending locks that are no longer being waited for
               match queue.queue_lock, queue.queue_lock_pending with
                  Some lock, false ->
                     eprintf "Queue entry canceled%t" eflush;
                     queue.queue_lock <- None;
                     Queue.cancel queue.queue_queue lock;
                     x
                | _ -> *)
                     Some x

   (*
    * Start the main loop.
    *)
   let args = Queue.args

   let main_loop queue =
      Queue.main_loop queue.queue_queue
end

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
