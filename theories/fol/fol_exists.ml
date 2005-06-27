(*
 * Existential quantifier.
 *)

extends Fol_and
extends Fol_pred

open Basic_tactics

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "exists"{x. 'B['x]}

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_exists

dform exists_df : parens :: "prec"["prec_exists"] :: "exists"{x. 'B} =
   szone pushm[3] Nuprl_font!"exists" slot{'x} `"." hspace slot{'B} popm ezone

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

prim exists_type {| intro [] |} :
   [wf] sequent { <H>; x: pred >- "type"{'B['x]} } -->
   sequent { <H> >- "type"{."exists"{y. 'B['y]}} } = trivial

prim exists_intro {| intro [] |} 'a :
   [wf] sequent { <H> >- "type"{'a} } -->
   [main] ('b : sequent { <H> >- 'B['a] }) -->
   [wf] sequent { <H>; x: pred >- "type"{'B['x]} } -->
   sequent { <H> >- "exists"{y. 'B['y]} } =
   pair{'a; 'b}

prim exists_elim {| elim [] |} 'H :
   [wf] ('b['y; 'z] : sequent { <H>; y: pred; z: 'B['y]; <J['y, 'z]> >- 'C['y, 'z] }) -->
   sequent { <H>; x: "exists"{w. 'B['w]}; <J['x]> >- 'C['x] } =
   spread{'x; y, z. 'b['y; 'z]}

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
