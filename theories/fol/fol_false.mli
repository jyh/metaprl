(*
 * Falsehood.
 *)

extends Fol_type

declare "false"

rule false_type :
   sequent ['ext] { <H> >- "type"{."false"} }

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
