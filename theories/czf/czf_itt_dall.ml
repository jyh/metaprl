(*
 * Primitiva axiomatization of implication.
 *)

include Czf_itt_all

open Refiner.Refiner.RefineErrors
open Resource

open Tacticals
open Conversionals
open Sequent
open Var

open Itt_logic
open Itt_rfun

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

primrw unfold_dall : "all"{'T; x. 'A['x]} <--> Itt_rfun!"fun"{'T; x. 'A['x]}

let fold_dall = makeFoldC << "all"{'T; x. 'A['x]} >> unfold_dall

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform dall_df : mode[prl] :: parens :: "prec"[prec_lambda] :: "all"{'T; x. 'A} =
   pushm[0] forall `"'" slot{'x} `":" slot{'T} `"." slot{'A} popm

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Intro.
 *
 * H >- all x: T. A
 * by dall_intro
 * H >- member{T; set}
 * H, x: T >- A
 *)
prim dall_intro 'H 'a :
   sequent ['ext] { 'H >- member{'T; set} } -->
   sequent ['ext] { 'H; a: 'T >- 'A['a] } -->
   sequent ['ext] { 'H >- "all"{'T; x. 'A['x]} } =
   it

(*
 * Elimination.
 *
 * H, x: all y:T. A[y]}, J[x] >- T[x]
 * by dall_elim z
 * H, x: all y:T. A[y], J[x] >- member{z; T}
 * H, x: all y:T. A[y], J[x], z: A[z] >- T[x]
 *)
prim dall_elim 'H 'J 'x 'z 'w :
   sequent ['ext] { 'H; x: "all"{'T; y. 'A['y]}; 'J['x] >- member{'z; 'T} } -->
   sequent ['ext] { 'H; x: "all"{'T; y. 'A['y]}; 'J['x]; w: 'A['z] >- 'C['x] } -->
   sequent ['ext] { 'H; x: "all"{'T; y. 'A['y]}; 'J['x] >- 'C['x] } =
   it

(*
 * Well formedness.
 *)
prim dall_wf 'H 'y :
   sequent ['ext] { 'H >- member{'T; set} } -->
   sequent ['ext] { 'H; y: 'T >- wf{'A['y]} } -->
   sequent ['ext] { 'H >- wf{."all"{'T; x. 'A['x]} } } =
   it

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let dall_term = << "all"{'T; x. 'A['x]} >>
let wf_dall_term = << wf{. "all"{'T; x. 'A['x]}} >>

(*
 * Propositional reasoning.
 *)
let d_dallT i p =
   if i = 0 then
      let v = maybe_new_vars1 p "v" in
         dall_intro (hyp_count p) v p
   else
      let x, _ = nth_hyp p i in
      let w = Var.maybe_new_vars1 p "u" in
      let z = get_with_arg p in
      let i, j = hyp_indices p i in
          dall_elim i j x z w p

let d_resource = d_resource.resource_improve d_resource (dall_term, d_dallT)

(*
 * Well-formedness.
 *)
external id : 'a * 'b -> 'a * 'b = "%identity"

let d_wf_dallT i p =
   if i = 0 then
      let v = maybe_new_vars1 p "v" in
         dall_wf (hyp_count p) v p
   else
      raise (RefineError (id ("d_wf_dallT", (StringTermError ("no elim form", wf_dall_term)))))

let d_resource = d_resource.resource_improve d_resource (wf_dall_term, d_wf_dallT)

(*
 * $Log$
 * Revision 1.2  1998/07/01 04:37:21  nogin
 * Moved Refiner exceptions into a separate module RefineErrors
 *
 * Revision 1.1  1998/06/23 22:12:21  jyh
 * Improved rewriter speed with conversion tree and flist.
 *
 *)
