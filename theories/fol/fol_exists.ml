(*
 * Existential quantifier.
 *)

include Fol_and
include Fol_pred

open Base_dtactic

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

prim exists_type {| intro [] |} 'H 'x :
   [wf] sequent ['ext] { 'H; x: pred >- "type"{'B['x]} } -->
   sequent ['ext] { 'H >- "type"{."exists"{y. 'B['y]}} } = trivial

prim exists_intro {| intro [] |} 'H 'a 'x :
   [wf] sequent ['ext] { 'H >- "type"{'a} } -->
   [main] ('b : sequent ['ext] { 'H >- 'B['a] }) -->
   [wf] sequent ['ext] { 'H; x: pred >- "type"{'B['x]} } -->
   sequent ['ext] { 'H >- "exists"{y. 'B['y]} } =
   pair{'a; 'b}

prim exists_elim {| elim [] |} 'H 'J 'x 'y 'z :
   [wf] ('b['y; 'z] : sequent ['ext] { 'H; y: pred; z: 'B['y]; 'J['y, 'z] >- 'C['y, 'z] }) -->
   sequent ['ext] { 'H; x: "exists"{w. 'B['w]}; 'J['x] >- 'C['x] } =
   spread{'x; y, z. 'b['y; 'z]}

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
