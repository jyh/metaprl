(*
 * Utilities for tactics.
 *
 * $Log$
 * Revision 1.1  1997/04/28 15:52:41  jyh
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
 * Revision 1.1  1996/09/25 22:52:06  jyh
 * Initial "tactical" commit.
 *
 *)

open Term
open Tactic_type

(*
 * Hypothesis operations.
 *)
val get_pos_hyp_index : int -> int -> int
val get_pos_hyp_num : int -> tactic_arg -> int
val hyp_count : tactic_arg -> int
val var_of_hyp : int -> tactic_arg -> string
val get_decl_number : tactic_arg -> string -> int
val nth_hyp : int -> tactic_arg -> term
val declared_vars : tactic_arg -> string list
val concl : tactic_arg -> term
val goal : tactic_arg -> term

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
