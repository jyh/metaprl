(*
 * Empty set.
 *)

include Czf_itt_set

open Printf
open Nl_debug

open Refiner.Refiner.RefineError

open Sequent
open Resource
open Tacticals

let _ =
   if !debug_load then
      eprintf "Loading Czf_itt_empty%t" eflush

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "empty"

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

primrw unfold_empty : empty <--> collect{void; x. 'x}

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

dform empty_df : empty =
   `"{}"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Empty is a set.
 *)
interactive empty_isset 'H : :
   sequent ['ext] { 'H >- isset{empty} }

(*
 * Nothing is in the empty set.
 *)
interactive empty_member_elim 'H 'J : :
   sequent ['ext] { 'H; x: member{'y; empty}; 'J >- 'T }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Elim form.
 *)
let d_emptyT i p =
   if i = 0 then
      raise (RefineError ("d_emptyT", StringError "no introduction form for empty"))
   else
      let i, j = hyp_indices p i in
         empty_member_elim i j p

let empty_member_term = << member{'x; empty} >>

let d_resource = d_resource.resource_improve d_resource (empty_member_term, d_emptyT)

(*
 * Sethood.
 *)
let d_empty_setT i p =
   if i = 0 then
      empty_isset (hyp_count p) p
   else
      raise (RefineError ("d_empty_setT", StringError "no elimination form"))

let empty_isset_term = << isset{empty} >>

let d_resource = d_resource.resource_improve d_resource (empty_isset_term, d_empty_setT)

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
