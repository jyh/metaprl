(*
 * Classical first order logic.
 *)

include Fol_ctheory
include Fol_class

interactive pierce 'H : :
   sequent ['ext] { 'H >- "all"{P. "all"{Q. ((('P => 'Q) => 'P) => 'P)}} }

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
