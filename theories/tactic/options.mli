(*
 * Some additions to tactic arguments.
 *)

open Tactic_type

val get_opt_var_arg : string -> tactic_arg -> string

(*
 * $Log$
 * Revision 1.2  1998/06/09 20:52:53  jyh
 * Propagated refinement changes.
 * New tacticals module.
 *
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
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
