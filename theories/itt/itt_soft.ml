(*
 * Regular logic connectives.
 *
 *)

include Tacticals
include Conversionals
include Base_dtactic
include Itt_equal

open Printf
open Nl_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermAddr
open Refine
open Resource

open Sequent
open Tacticals
open Conversionals
open Base_dtactic
open Itt_equal

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Itt_soft%t" eflush

(* debug_string DebugLoad "Loading itt_soft..." *)

(*
 * D tactic.
 *)
let d_soft conv i =
   Conversionals.rw conv i thenT dT i

(*
 * Typehood.
 *)
let d_type_soft conv i =
   Conversionals.rw (addrC [0] conv) i thenT dT i

(*
 * EqCD.
 *)
let eqcd_soft conv =
   Conversionals.rw conv 0 thenT eqcdT

(*
 * Combine them.
 *)
let add_soft_abs dres eqcdres t rw =
   let type_t = mk_type_term t in
   let dres = dres.resource_improve dres (t, d_soft rw) in
   let dres = dres.resource_improve dres (type_t, d_type_soft rw) in
   let eqcdres = eqcdres.resource_improve eqcdres (t, eqcd_soft rw) in
      dres, eqcdres

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
