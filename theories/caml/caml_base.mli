(*
 * Define a state construct.
 * We don't define a complete model, but we do provide
 * an interpretation of ref cells.  this requires one level
 * of indirection on ref cells, records, and arrays.
 *)

(*
 * The store is the storage area for mutable objects.
 * The State maps variables to values (through the store
 * if the value is mutable).  the Term is the expression
 * to be evaluated.
 *)
declare program{'Store; 'State; 'Term}

(*
 * $Log$
 * Revision 1.1  1998/01/03 23:20:22  jyh
 * Upgraded to OCaml 1.07, initial semantics of OCaml.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
