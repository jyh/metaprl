(*
 * Some additions to the tactics.
 * these are combinations of the tacticals and options.
 *
 * $Log$
 * Revision 1.1  1997/04/28 15:52:40  jyh
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
 * Revision 1.1  1996/10/23 15:18:15  jyh
 * First working version of dT tactic.
 *
 *)

open Tactic_type

val get_opt_var_arg : string -> tactic_arg -> string

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
