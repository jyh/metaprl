(*
 * Primitiva axiomatization of implication.
 *)

include Czf_itt_wf

open Refiner.Refiner.Refine
open Resource

open Tacticals
open Sequent

open Itt_logic
open Itt_rfun

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "or"{'A; 'B}
declare inl{'A}
declare inr{'A}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

primrw unfold_or : "or"{'A; 'B} <--> union{'A; 'B}
primrw unfold_inl : inl{'a} <--> Itt_union!inl{'a}
primrw unfold_inr : inr{'a} <--> Itt_union!inr{'a}

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform or_df : mode[prl] :: parens :: "prec"[prec_or] :: "or"{'A; 'B} =
   slot{'A} " " vee `"' " slot{'B}

dform inl_df : parens :: "prec"[prec_apply] :: inl{'a} =
   `"inl'" " " slot{'a}

dform inr_df : parens :: "prec"[prec_apply] :: inr{'a} =
   `"inr'" " " slot{'a}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Intro.
 *
 * H >- A \/ B
 * by or_intro_left
 * H >- A
 * H >- B wf
 *)
prim or_intro_left 'H :
   sequent ['ext] { 'H >- 'A } -->
   sequent ['ext] { 'H >- wf{'B} } -->
   sequent ['ext] { 'H >- "or"{'A; 'B} } =
   it

prim or_intro_right 'H :
   sequent ['ext] { 'H >- 'B } -->
   sequent ['ext] { 'H >- wf{'A} } -->
   sequent ['ext] { 'H >- "or"{'A; 'B} } =
   it

(*
 * Elimination.
 *
 * H, x: A \/ B, J[x] >- T[x]
 * by or_elim i
 * H, x: A \/ B, y: A; J[inl y] >- T[inl y]
 * H, x: A \/ B, y: B; J[inr y] >- T[inr y]
 *)
prim or_elim 'H 'J 'y :
   sequent ['ext] { 'H; x: "or"{'A; 'B}; y: 'A; 'J[inl{'y}] >- 'T[inl{'y}] } -->
   sequent ['ext] { 'H; x: "or"{'A; 'B}; y: 'B; 'J[inr{'y}] >- 'T[inr{'y}] } -->
   sequent ['ext] { 'H; x: "or"{'A; 'B}; 'J['x] >- 'T['x] } =
   it

(*
 * Well formedness.
 *)
prim or_wf 'H :
   sequent ['ext] { 'H >- wf{'A} } -->
   sequent ['ext] { 'H >- wf{'B} } -->
   sequent ['ext] { 'H >- wf{."or"{'A; 'B}} } =
   it

(*
 * Implication is restricted.
 *)
prim or_res 'H :
   sequent ['ext] { 'H >- restricted{'A} } -->
   sequent ['ext] { 'H >- restricted{'B} } -->
   sequent ['ext] { 'H >- restricted{."or"{'A; 'B}} } =
   it

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let or_term = << "or"{'A; 'B} >>
let wf_or_term = << wf{. "or"{'A; 'B}} >>
let res_or_term = << restricted{. "or"{'A; 'B}} >>

(*
 * Propositional reasoning.
 *)
let d_orT i p =
   (if i = 0 then
       let intro =
          if get_sel_arg p = 1 then
             or_intro_left
          else
             or_intro_right
       in
          intro (hyp_count p)
    else
       let y = Var.maybe_new_vars1 p "y" in
       let i, j = hyp_indices p i in
          or_elim i j y) p

let d_resource = d_resource.resource_improve d_resource (or_term, d_orT)

(*
 * Well-formedness.
 *)
external pair : 'a * 'b -> 'a * 'b = "%identity"

let d_wf_orT i p =
   if i = 0 then
      or_wf (hyp_count p) p
   else
      raise (RefineError (pair ("d_wf_orT", (StringTermError ("no elim form", wf_or_term)))))

let d_resource = d_resource.resource_improve d_resource (wf_or_term, d_wf_orT)

(*
 * Restricted.
 *)
let d_res_orT i p =
   if i = 0 then
      or_res (hyp_count p) p
   else
      raise (RefineError (pair ("d_res_orT", (StringTermError ("no elim form", res_or_term)))))

let d_resource = d_resource.resource_improve d_resource (res_or_term, d_res_orT)

(*
 * $Log$
 * Revision 1.3  1998/06/22 20:01:42  jyh
 * Fixed syntax error in term_addr_gen.ml
 *
 * Revision 1.2  1998/06/22 19:46:06  jyh
 * Rewriting in contexts.  This required a change in addressing,
 * and the body of the context is the _last_ subterm, not the first.
 *
 * Revision 1.1  1998/06/16 16:26:01  jyh
 * Added itt_test.
 *
 *)
