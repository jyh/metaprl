(*
 * Primitiva axiomatization of implication.
 *)

include Czf_itt_and

open Refiner.Refiner.RefineError
open Resource

open Tacticals
open Conversionals
open Sequent
open Var

open Itt_logic
open Itt_rfun

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "implies"{'A; 'B}

(*
 * Make formulas concise.
 *)
declare "iff"{'a; 'b}
primrw unfold_iff : "iff"{'a; 'b} <--> "and"{.'a => 'b; .'b => 'a}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

primrw unfold_implies : "implies"{'A; 'B} <--> "fun"{'A; 'B}

let fold_implies = makeFoldC << "implies"{'A; 'B} >> unfold_implies

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform implies_df : mode[prl] :: parens :: "prec"[prec_implies] :: "implies"{'A; 'B} =
   pushm[0] slot{'A} " " Rightarrow `"' " slot{'B} popm

dform iff_fs : mode[prl] :: parens :: "prec"[prec_implies] :: "iff"{'A; 'B} =
   pushm[0] slot{'A} " " shortleftrightarrow `"' " slot{'B} popm

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Intro.
 *
 * H >- A => B
 * by implies_intro
 * H >- A wf
 * H, A >- B
 *)
prim implies_intro 'H 'a :
   sequent ['ext] { 'H >- wf{'A} } -->
   sequent ['ext] { 'H; a: 'A >- 'B } -->
   sequent ['ext] { 'H >- "implies"{'A; 'B} } =
   it

(*
 * Elimination.
 *
 * H, x: A => B, J[x] >- T[x]
 * by implies_elim i
 * H, x: A => B, J[x] >- A
 * H, x: A => B, J[x], y: B -> T[x]
 *)
prim implies_elim 'H 'J 'x 'y :
   sequent ['ext] { 'H; x: "implies"{'A; 'B}; 'J['x] >- 'A } -->
   sequent ['ext] { 'H; x: "implies"{'A; 'B}; 'J['x]; y: 'B >- 'T['x] } -->
   sequent ['ext] { 'H; x: "implies"{'A; 'B}; 'J['x] >- 'T['x] } =
   it

(*
 * Well formedness.
 *)
prim implies_wf 'H :
   sequent ['ext] { 'H >- wf{'A} } -->
   sequent ['ext] { 'H >- wf{'B} } -->
   sequent ['ext] { 'H >- wf{."implies"{'A; 'B}} } =
   it

(*
 * Implication is restricted.
 *)
prim implies_res 'H :
   sequent ['ext] { 'H >- restricted{'A} } -->
   sequent ['ext] { 'H >- restricted{'B} } -->
   sequent ['ext] { 'H >- restricted{."implies"{'A; 'B}} } =
   it

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let implies_term = << "implies"{'A; 'B} >>
let wf_implies_term = << wf{. "implies"{'A; 'B}} >>
let res_implies_term = << restricted{. "implies"{'A; 'B}} >>

(*
 * Propositional reasoning.
 *)
let d_impliesT i p =
   if i = 0 then
      let v = maybe_new_vars1 p "v" in
         implies_intro (hyp_count p) v p
   else
      let x, _ = nth_hyp p i in
      let y = Var.maybe_new_vars1 p "u" in
      let i, j = hyp_indices p i in
          implies_elim i j x y p

let d_resource = d_resource.resource_improve d_resource (implies_term, d_impliesT)

(*
 * Well-formedness.
 *)
external id : 'a * 'b -> 'a * 'b = "%identity"

let d_wf_impliesT i p =
   if i = 0 then
      implies_wf (hyp_count p) p
   else
      raise (RefineError (id ("d_wf_impliesT", (StringTermError ("no elim form", wf_implies_term)))))

let d_resource = d_resource.resource_improve d_resource (wf_implies_term, d_wf_impliesT)

(*
 * Restricted.
 *)
let d_res_impliesT i p =
   if i = 0 then
      implies_res (hyp_count p) p
   else
      raise (RefineError (id ("d_res_impliesT", (StringTermError ("no elim form", res_implies_term)))))

let d_resource = d_resource.resource_improve d_resource (res_implies_term, d_res_impliesT)

(*
 * $Log$
 * Revision 1.3  1998/07/02 18:37:09  jyh
 * Refiner modules now raise RefineError exceptions directly.
 * Modules in this revision have two versions: one that raises
 * verbose exceptions, and another that uses a generic exception.
 *
 * Revision 1.2  1998/07/01 04:37:25  nogin
 * Moved Refiner exceptions into a separate module RefineErrors
 *
 * Revision 1.1  1998/06/23 22:12:22  jyh
 * Improved rewriter speed with conversion tree and flist.
 *
 *)
