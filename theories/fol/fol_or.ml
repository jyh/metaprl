(*
 * Disjunction.
 *)

include Fol_type

open Nl_resource
open Refiner.Refiner.RefineError
open Tacticals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "or"{'A; 'B}
declare inl{'a}
declare inr{'b}
declare decide{'x; y. 'body1['y]; z. 'body2['z]}

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_or
prec prec_inl
prec prec_inr
prec prec_decide

dform or_df : parens :: "prec"["prec_or"] :: "or"{'A; 'B} =
   szone pushm[0] slot{'A} hspace vee `" " slot{'B} popm ezone

dform inl_df : parens :: "prec"["prec_inl"] :: inl{'x} =
   `"inl " slot{'x}

dform inr_df : parens :: "prec"["prec_inl"] :: inr{'x} =
   `"inr " slot{'x}

dform decide_df : parens :: "prec"["prec_decide"] :: decide{'x; y. 'body1; z. 'body2} =
   szone pushm[3] `"match " slot{'x} `" with" hspace
   `"inl " slot{'y} `" ->" hspace slot{'body1}
   hspace `"| inr " slot{'z} `" ->" hspace slot{'body2}
   popm ezone


(************************************************************************
 * COMPUTATION                                                          *
 ************************************************************************)

primrw reduce_decide_inl : decide{inl{'x}; y. 'body1['y]; z. 'body2['z]} <--> 'body1['x]

primrw reduce_decide_inr : decide{inr{'x}; y. 'body1['y]; z. 'body2['z]} <--> 'body2['x]

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

prim or_type 'H :
   sequent ['ext] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- "type"{."or"{'A; 'B}} } =
   trivial

prim or_intro_left 'H :
   sequent ['ext] { 'H >- "type"{'B} } -->
   ('a : sequent ['ext] { 'H >- 'A }) -->
   sequent ['ext] { 'H >- "or"{'A; 'B} } =
   inl{'a}

prim or_intro_right 'H :
   sequent ['ext] { 'H >- "type"{'A} } -->
   ('b : sequent ['ext] { 'H >- 'B } ) -->
   sequent ['ext] { 'H >- "or"{'A; 'B} } =
   inr{'b}

prim or_elim 'H 'J 'x :
   ('a['x] : sequent ['ext] { 'H; x: 'A; 'J[inl{'x}] >- 'C[inl{'x}] }) -->
   ('b['x] : sequent ['ext] { 'H; x: 'B; 'J[inr{'x}] >- 'C[inr{'x}] }) -->
   sequent ['ext] { 'H; x: 'A or 'B; 'J['x] >- 'C['x] } =
   decide{'x; x. 'a['x]; x. 'b['x]}

(************************************************************************
 * AUTOMATION                                                           *
 ************************************************************************)

let d_or_type i p =
   if i = 0 then
      or_type (Sequent.hyp_count_addr p) p
   else
      raise (RefineError ("d_or_type", StringError "no elimination form"))

let or_type_term = << "type"{."or"{'A; 'B}} >>

let d_resource = d_resource.resource_improve d_resource (or_type_term, d_or_type)

let d_or i p =
   if i = 0 then
      let sel = get_sel_arg p in
         (if sel = 1 then
             or_intro_left
          else
             or_intro_right) (Sequent.hyp_count_addr p) p
   else
      let j, k = Sequent.hyp_indices p i in
      let x, _ = Sequent.nth_hyp p i in
         or_elim j k x p

let or_term = << "or"{'A; 'B} >>

let d_resource = d_resource.resource_improve d_resource (or_term, d_or)

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
