(*
 * Primitiva axiomatization of implication.
 *)

include Czf_itt_set

open Printf
open Nl_debug

open Refiner.Refiner.RefineError
open Resource

open Tacticals
open Conversionals
open Sequent
open Var

open Itt_logic
open Itt_rfun

let _ =
   if !debug_load then
      eprintf "Loading Czf_itt_all%t" eflush

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "sall"{x. 'A['x]}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

primrw unfold_sall : "sall"{x. 'A['x]} <--> (all x: set. 'A['x])

let fold_sall = makeFoldC << "sall"{x. 'A['x]} >> unfold_sall

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform sall_df : mode[prl] :: parens :: "prec"[prec_lambda] :: "sall"{x. 'A} =
   pushm[0] Nuprl_font!forall slot{'x} `"." slot{'A} popm

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Typehood.
 *)
interactive sall_type 'H 'y :
   sequent ['ext] { 'H; y: set >- "type"{'A['y]} } -->
   sequent ['ext] { 'H >- "type"{."sall"{x. 'A['x]} } }

(*
 * Intro.
 *)
interactive sall_intro 'H 'a :
   sequent ['ext] { 'H; a: set >- 'A['a] } -->
   sequent ['ext] { 'H >- "sall"{x. 'A['x]} }

(*
 * Elimination.
 *)
interactive sall_elim 'H 'J 'x 'z 'w :
   sequent [squash] { 'H; x: "sall"{y. 'A['y]}; 'J['x] >- isset{'z} } -->
   sequent ['ext] { 'H; x: "sall"{y. 'A['y]}; 'J['x]; w: 'A['z] >- 'T['x] } -->
   sequent ['ext] { 'H; x: "sall"{y. 'A['y]}; 'J['x] >- 'T['x] }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Propositional reasoning.
 *)
let d_sallT i p =
   if i = 0 then
      let v = maybe_new_vars1 p "v" in
         sall_intro (hyp_count p) v p
   else
      let x, _ = nth_hyp p i in
      let w = Var.maybe_new_vars1 p "u" in
      let z = get_with_arg p in
      let i, j = hyp_indices p i in
         (sall_elim i j x z w
          thenLT [addHiddenLabelT "wf";
                  addHiddenLabelT "main"]) p

let sall_term = << "sall"{x. 'A['x]} >>

let d_resource = d_resource.resource_improve d_resource (sall_term, d_sallT)

(*
 * Well-formedness.
 *)
let d_sall_typeT i p =
   if i = 0 then
      let v = maybe_new_vars1 p "v" in
         sall_type (hyp_count p) v p
   else
      raise (RefineError ("d_sall_typeT", StringError "no elim form"))

let sall_type_term = << "type"{."sall"{x. 'A['x]}} >>

let d_resource = d_resource.resource_improve d_resource (sall_type_term, d_sall_typeT)

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
