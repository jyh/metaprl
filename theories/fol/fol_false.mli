(*
 * Falsehood.
 *)

include Fol_type

declare "false"

axiom false_type 'H :
   sequent ['ext] { 'H >- "type"{."false"} }

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
