(*
 * Utilities for generating variable names.
 *)

(* Generate a new var different from any in the list *)
val new_var : string -> string list -> string
val maybe_new_var : string -> string list -> string
val maybe_new_vars : string list -> string list -> string list

(*
 * $Log$
 * Revision 1.2  1998/06/03 22:20:07  jyh
 * Nonpolymorphic refiner.
 *
 * Revision 1.1  1997/04/28 15:52:46  jyh
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
 * Revision 1.1  1996/09/25 22:52:08  jyh
 * Initial "tactical" commit.
 *
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
