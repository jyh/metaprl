(*
 * Primitiva axiomatization of implication.
 *)

include Czf_itt_set

open Refiner.Refiner.RefineError
open Resource

open Tacticals
open Conversionals
open Sequent

open Itt_logic
open Itt_rfun

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "or"{'A; 'B}
declare "inl"{'x}
declare "inr"{'x}
declare decide{'x; y. 'a['y]; z. 'b['z]}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

primrw unfold_or : "or"{'A; 'B} <--> union{'A; 'B}
primrw unfold_inl : inl{'x} <--> Itt_union!inl{'x}
primrw unfold_inr : inr{'x} <--> Itt_union!inr{'x}
primrw unfold_decide : decide{'x; y. 'a['y]; z. 'b['z]} <--> Itt_union!decide{'x; y. 'a['y]; z. 'b['z]}

interactive_rw reduce_decide_inl : decide{inl{'x}; u. 'l['u]; v. 'r['v]} <--> 'l['x]
interactive_rw reduce_decide_inr : decide{inr{'x}; u. 'l['u]; v. 'r['v]} <--> 'r['x]

let fold_or  = makeFoldC << "or"{'A; 'B} >> unfold_or
let fold_inl = makeFoldC << inl{'x} >> unfold_inl
let fold_inr = makeFoldC << inr{'x} >> unfold_inr
let fold_decide = makeFoldC << decide{'x; y. 'a['y]; z. 'b['z]} >> unfold_decide

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform or_df : mode[prl] :: parens :: "prec"[prec_or] :: "or"{'A; 'B} =
   slot{'A} " " vee `"' " slot{'B}

dform inl_df : mode[prl] :: parens :: "prec"[prec_apply] :: inl{'x} =
   `"inl' " slot{'x}

dform inr_df : mode[prl] :: parens :: "prec"[prec_apply] :: inr{'x} =
   `"inr' " slot{'x}

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
interactive or_intro_left 'H :
   sequent ['ext] { 'H >- 'A } -->
   sequent ['ext] { 'H >- wf{'B} } -->
   sequent ['ext] { 'H >- "or"{'A; 'B} }

interactive or_intro_right 'H :
   sequent ['ext] { 'H >- 'B } -->
   sequent ['ext] { 'H >- wf{'A} } -->
   sequent ['ext] { 'H >- "or"{'A; 'B} }

(*
 * Elimination.
 *
 * H, x: A \/ B, J[x] >- T[x]
 * by or_elim i
 * H, x: A \/ B, y: A; J[inl y] >- T[inl y]
 * H, x: A \/ B, y: B; J[inr y] >- T[inr y]
 *)
interactive or_elim 'H 'J 'y :
   sequent ['ext] { 'H; x: "or"{'A; 'B}; y: 'A; 'J[inl{'y}] >- 'T[inl{'y}] } -->
   sequent ['ext] { 'H; x: "or"{'A; 'B}; y: 'B; 'J[inr{'y}] >- 'T[inr{'y}] } -->
   sequent ['ext] { 'H; x: "or"{'A; 'B}; 'J['x] >- 'T['x] }

(*
 * Well formedness.
 *)
interactive or_wf 'H :
   sequent ['ext] { 'H >- wf{'A} } -->
   sequent ['ext] { 'H >- wf{'B} } -->
   sequent ['ext] { 'H >- wf{."or"{'A; 'B}} }

interactive or_type 'H :
   sequent ['ext] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- "type"{."or"{'A; 'B}} }

(*
 * Implication is restricted.
 *)
interactive or_res 'H :
   sequent ['ext] { 'H >- restricted{x. 'A['x]} } -->
   sequent ['ext] { 'H >- restricted{x. 'B['x]} } -->
   sequent ['ext] { 'H >- restricted{x. "or"{'A['x]; 'B['x]}} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let or_term = << "or"{'A; 'B} >>
let wf_or_term = << wf{. "or"{'A; 'B}} >>
let res_or_term = << restricted{x. "or"{'A['x]; 'B['x]}} >>

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
let d_wf_orT i p =
   if i = 0 then
      or_wf (hyp_count p) p
   else
      raise (RefineError ("d_wf_orT", (StringTermError ("no elim form", wf_or_term))))

let d_resource = d_resource.resource_improve d_resource (wf_or_term, d_wf_orT)

let d_or_typeT i p =
   if i = 0 then
      or_type (hyp_count p) p
   else
      raise (RefineError ("d_or_typeT", (StringError "no elim form")))

let or_type_term = << "type"{."or"{'A; 'B}} >>

let d_resource = d_resource.resource_improve d_resource (or_type_term, d_or_typeT)

(*
 * Restricted.
 *)
let d_res_orT i p =
   if i = 0 then
      or_res (hyp_count p) p
   else
      raise (RefineError ("d_res_orT", (StringTermError ("no elim form", res_or_term))))

let d_resource = d_resource.resource_improve d_resource (res_or_term, d_res_orT)
