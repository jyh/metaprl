(*
 * Primitiva axiomatization of implication.
 *)

include Czf_itt_set

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

declare "all"{x. 'A['x]}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

primrw unfold_all : "all"{x. 'A['x]} <--> Itt_rfun!"fun"{set; x. 'A['x]}

let fold_all = makeFoldC << "all"{x. 'A['x]} >> unfold_all

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform all_df : mode[prl] :: parens :: "prec"[prec_lambda] :: "all"{x. 'A} =
   pushm[0] forall slot{'x} `"." slot{'A} popm

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Intro.
 *
 * H >- all x. A
 * by all_intro
 * H, x: set >- A
 *)
prim all_intro 'H 'a :
   sequent ['ext] { 'H; a: set >- 'A['a] } -->
   sequent ['ext] { 'H >- "all"{x. 'A['x]} } =
   it

(*
 * Elimination.
 *
 * H, x: all{x. A[x]}, J[x] >- T[x]
 * by all_elim z
 * H, x: all{x. A[x]}, J[x] >- member{z; set}
 * H, x: all{x. A[x]}, J[x], y: A[z] >- T[x]
 *)
prim all_elim 'H 'J 'x 'z 'w :
   sequent ['ext] { 'H; x: "all"{y. 'A['y]}; 'J['x] >- isset{'z} } -->
   sequent ['ext] { 'H; x: "all"{y. 'A['y]}; 'J['x]; w: 'A['z] >- 'T['x] } -->
   sequent ['ext] { 'H; x: "all"{y. 'A['y]}; 'J['x] >- 'T['x] } =
   it

(*
 * Well formedness.
 *)
prim all_wf 'H 'y :
   sequent ['ext] { 'H; y: set >- wf{'A['y]} } -->
   sequent ['ext] { 'H >- wf{."all"{x. 'A['x]} } } =
   it

(*
 * Simple quantification is restricted.
 *)
prim all_res 'H 'y :
   sequent ['ext] { 'H; y: set >- restricted{'A['x]} } -->
   sequent ['ext] { 'H >- restricted{."all"{x. 'A['x]}} } =
   it

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let all_term = << "all"{x. 'A['x]} >>
let wf_all_term = << wf{. "all"{x. 'A['x]}} >>
let res_all_term = << restricted{. "all"{x. 'A['x]}} >>

(*
 * Propositional reasoning.
 *)
let d_allT i p =
   if i = 0 then
      let v = maybe_new_vars1 p "v" in
         all_intro (hyp_count p) v p
   else
      let x, _ = nth_hyp p i in
      let w = Var.maybe_new_vars1 p "u" in
      let z = get_with_arg p in
      let i, j = hyp_indices p i in
          all_elim i j x z w p

let d_resource = d_resource.resource_improve d_resource (all_term, d_allT)

(*
 * Well-formedness.
 *)
external id : 'a * 'b -> 'a * 'b = "%identity"

let d_wf_allT i p =
   if i = 0 then
      let v = maybe_new_vars1 p "v" in
         all_wf (hyp_count p) v p
   else
      raise (RefineError (id ("d_wf_allT", (StringTermError ("no elim form", wf_all_term)))))

let d_resource = d_resource.resource_improve d_resource (wf_all_term, d_wf_allT)

(*
 * Restricted.
 *)
let d_res_allT i p =
   if i = 0 then
      let v = maybe_new_vars1 p "v" in
         all_res (hyp_count p) v p
   else
      raise (RefineError (id ("d_res_allT", (StringTermError ("no elim form", res_all_term)))))

let d_resource = d_resource.resource_improve d_resource (res_all_term, d_res_allT)

