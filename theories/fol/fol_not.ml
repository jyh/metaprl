(*
 * Negation is defined in terms of implication.
 *)

extends Fol_false
extends Fol_implies

open Base_dtactic

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "not"{'A}

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_not

dform not_df : parens :: "prec"["prec_not"] :: "not"{'A} =
   tneg slot{'A}

(************************************************************************
 * COMPUTATION                                                          *
 ************************************************************************)

prim_rw unfold_not : "not"{'A} <--> implies{'A; ."false"}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

interactive not_type {| intro [] |} :
   [wf] sequent ['ext] { <H> >- "type"{'A} } -->
   sequent ['ext] { <H> >- "type"{."not"{'A}} }

interactive not_intro {| intro [] |} :
   [wf] sequent ['ext] { <H> >- "type"{'A} } -->
   [main] sequent ['ext] { <H>; x: 'A >- "false" } -->
   sequent ['ext] { <H> >- "not"{'A} }

interactive not_elim {| elim [] |} 'H :
   [main] sequent ['ext] { <H>; x: "not"{'A}; <J['x]> >- 'A } -->
   sequent ['ext] { <H>; x: "not"{'A}; <J['x]> >- 'C['x] }

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
