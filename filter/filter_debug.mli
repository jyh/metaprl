(*
 * Debug flags for the compiler.
 *)

(*
 * Debug the term grammar.
 *)
val debug_grammar : bool

(*
 * Resource and inheritance debugging.
 *)
val debug_resource : bool

(*
 * Library debugging.
 *)
val debug_library_base : bool

(*
 * $Log$
 * Revision 1.2  1998/02/12 23:38:06  jyh
 * Added support for saving intermediate files to the library.
 *
 * Revision 1.1  1997/04/28 15:50:53  jyh
 * This is the initial checkin of Nuprl-Light.
 * I am porting the editor, so it is not included
 * in this checkin.
 *
 * Directories:
 *     refiner: logic engine
 *     filter: front end to the Ocaml compiler
 *     editor: Emacs proof editor
 *     util: utilities
 *     mk: Makefile templates
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
