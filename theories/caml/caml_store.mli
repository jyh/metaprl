(*
 * The store is an area for mapping mutable objects to
 * values.
 *)

include Caml_base

(*
 * Addresses are abstract, and the store acts like
 * an association list.
 *)
declare addr[$s:s]

(*
 * $Log$
 * Revision 1.1  1998/01/03 23:20:29  jyh
 * Upgraded to OCaml 1.07, initial semantics of OCaml.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
