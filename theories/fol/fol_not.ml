(*
 * Negation is defined in terms of implication.
 *)

extends Fol_false
extends Fol_implies

open Basic_tactics

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

define unfold_not : "not"{'A} <--> implies{'A; ."false"}

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_not

dform not_df : parens :: "prec"["prec_not"] :: "not"{'A} =
   tneg slot{'A}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

interactive not_type {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- "type"{."not"{'A}} }

interactive not_intro {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [main] sequent { <H>; x: 'A >- "false" } -->
   sequent { <H> >- "not"{'A} }

interactive not_elim {| elim [] |} 'H :
   [main] sequent { <H>; x: "not"{'A}; <J['x]> >- 'A } -->
   sequent { <H>; x: "not"{'A}; <J['x]> >- 'C['x] }

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
