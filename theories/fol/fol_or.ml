(*
 * Disjunction.
 *)

extends Fol_type

open Base_dtactic

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

prim_rw reduce_decide_inl : decide{inl{'x}; y. 'body1['y]; z. 'body2['z]} <--> 'body1['x]

prim_rw reduce_decide_inr : decide{inr{'x}; y. 'body1['y]; z. 'body2['z]} <--> 'body2['x]

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

prim or_type {| intro [] |} 'H :
   [wf] sequent ['ext] { 'H >- "type"{'A} } -->
   [wf] sequent ['ext] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- "type"{."or"{'A; 'B}} } =
   trivial

prim or_intro_left {| intro [SelectOption 1] |} 'H :
   [wf] sequent ['ext] { 'H >- "type"{'B} } -->
   [main] ('a : sequent ['ext] { 'H >- 'A }) -->
   sequent ['ext] { 'H >- "or"{'A; 'B} } =
   inl{'a}

prim or_intro_right {| intro [SelectOption 2] |} 'H :
   [wf] sequent ['ext] { 'H >- "type"{'A} } -->
   [main] ('b : sequent ['ext] { 'H >- 'B } ) -->
   sequent ['ext] { 'H >- "or"{'A; 'B} } =
   inr{'b}

prim or_elim {| elim [] |} 'H 'J 'x :
   [wf] ('a['x] : sequent ['ext] { 'H; x: 'A; 'J[inl{'x}] >- 'C[inl{'x}] }) -->
   [wf] ('b['x] : sequent ['ext] { 'H; x: 'B; 'J[inr{'x}] >- 'C[inr{'x}] }) -->
   sequent ['ext] { 'H; x: 'A or 'B; 'J['x] >- 'C['x] } =
   decide{'x; x. 'a['x]; x. 'b['x]}

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
