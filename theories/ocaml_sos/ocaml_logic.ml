(*
 * Utilities for the semantics.
 *)

open Debug
open Printf

let _ =
   if !debug_load then
      eprintf "Loading Ocaml_logic%t" eflush

(*
 * Basic propositional logic.
 *)
declare ptrue
declare pfalse
declare por{'p1; 'p2}
declare pand{'p1; 'p2}
declare pimplies{'p1; 'p2}

(*
 * Two out of three proposititons.
 *)
declare two_values{'p1; 'p2; 'p3}

primrw two_values_reduce :
   two_values{'p1; 'p2; 'p3} <-->
      por{pand{'p1; 'p2}; por{pand{'p1; 'p3}; pand{'p2; 'p3}}}

(*
 * $Log$
 * Revision 1.1  1998/04/29 14:49:50  jyh
 * Added ocaml_sos.
 *
 * Revision 1.1  1998/02/18 18:47:20  jyh
 * Initial ocaml semantics.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
