(*
 * Conjunction.
 *)

extends Fol_type

open Dtactic

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "and"{'A; 'B}
declare "pair"{'a; 'b}
declare spread{'x; a, b. 'body['a; 'b]}

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_and

dform and_df : parens :: "prec"["prec_and"] :: "and"{'A; 'B} =
   szone pushm[0] slot{'A} hspace wedge `" " slot{'B} popm ezone

dform pair_df : "pair"{'a; 'b} =
   `"<" slot{'a} `"," slot{'b} `">"

dform spread_df : "spread"{'x; a, b. 'body} =
   szone pushm[0] `"let <" slot{'a} `"," slot{'b} `"> ="
   hspace slot{'x} hspace `"in" hspace slot{'body} popm ezone

(************************************************************************
 * COMPUTATION                                                          *
 ************************************************************************)

prim_rw reduce_spread : spread{pair{'x; 'y}; a, b. 'body['a; 'b]} <--> 'body['x; 'y]

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

prim and_type {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H> >- "type"{'B} } -->
   sequent { <H> >- "type"{.'A & 'B} } = trivial

prim and_intro {| intro [] |} :
   [main] ('a : sequent { <H> >- 'A }) -->
   [main] ('b : sequent { <H> >- 'B }) -->
   sequent { <H> >- 'A & 'B } = pair{'a; 'b}

prim and_elim {| elim [] |} 'H :
   [wf] sequent { <H>; x: 'A & 'B; <J['x]> >- "type"{'A} } -->
   [wf] sequent { <H>; x: 'A & 'B; <J['x]> >- "type"{'B} } -->
   [main] ('body['y; 'z] : sequent { <H>; y: 'A; z: 'B; <J['y, 'z]> >- 'C['y, 'z] }) -->
   sequent { <H>; x: 'A & 'B; <J['x]> >- 'C['x] } =
   spread{'x; y, z. 'body['y; 'z]}

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
