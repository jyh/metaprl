(*
 * Here are rules for the Void base type.
 * Void has no elements.  Its propositional
 * interpretation is "False".
 *
 *)

include Tacticals
include Itt_equal
include Itt_subtype

open Printf
open Debug
open Sequent
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Resource

open Tacticals
open Itt_equal
open Itt_subtype

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Itt_void%t" eflush

(*
 * incr_debug_level DebugMessage
 * debug_string DebugLoad "Loading itt_void..."
 *)

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare void

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform void_df1 : mode[prl] :: void = `"Void"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext Void
 * by voidFormation
 *)
prim voidFormation 'H : : sequent ['ext] { 'H >- univ[@i:l] } = void

(*
 * H >- Void = Void in Ui ext Ax
 * by voidEquality
 *)
prim voidEquality 'H : : sequent ['ext] { 'H >- void = void in univ[@i:l] } = it

(*
 * H, i:x:Void, J >- C
 * by voidElimination i
 *)
prim voidElimination 'H 'J : : sequent ['ext] { 'H; x: void; 'J['x] >- 'C['x] } = it

(*
 * Squash stability.
 *)
prim void_squashElimination 'H : sequent [squash] { 'H >- void } :
   sequent ['ext] { 'H >- void } = it

(*
 * Subtyping.
 *)
prim void_subtype 'H : :
   sequent ['ext] { 'H >- subtype{void; 'T} } =
   it

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Standard term.
 *)
let void_term = << void >>

(*
 * D
 *)
let d_voidT i p =
   eprintf "d_voidT: %d%t" i eflush;
   if i = 0 then
      failwith "can't prove void"
   else
      let t = goal p in
      let i, j = hyp_indices p i in
         voidElimination i j p

let d_resource = d_resource.resource_improve d_resource (void_term, d_voidT)
let dT = d_resource.resource_extract d_resource

(*
 * EqCD.
 *)
let eqcd_voidT p =
   let count = num_hyps (goal p) in
      voidEquality count p

let eqcd_resource = eqcd_resource.resource_improve eqcd_resource (void_term, eqcd_voidT)
let eqcdT = eqcd_resource.resource_extract eqcd_resource

(************************************************************************
 * SQUASH STABILITY                                                     *
 ************************************************************************)

(*
 * Void is squash stable.
 *)
let squash_void p =
   void_squashElimination (hyp_count p) p

let squash_resource = squash_resource.resource_improve squash_resource (void_term, squash_void)

(************************************************************************
 * SUBTYPING                                                            *
 ************************************************************************)

let void_sub p =
   void_subtype (hyp_count p) p

let sub_resource =
   sub_resource.resource_improve
   sub_resource
   (RLSubtype ([void_term, << 'a >>], void_sub))

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

(*
 * Type of void.
 *)
let inf_void _ decl _ = decl, univ1_term

let typeinf_resource = typeinf_resource.resource_improve typeinf_resource (void_term, inf_void)

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
