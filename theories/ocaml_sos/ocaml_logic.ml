(*
 * Utilities for the semantics.
 *)

open Nl_debug
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
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
