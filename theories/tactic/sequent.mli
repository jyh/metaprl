(*
 * Utilities for tactics.
 *)

open Refiner.Refiner.Term
open Refiner.Refiner.Refine
open Tactic_type

(*
 * Hypothesis operations.
 *)
val create : msequent -> tactic_argument -> tactic_arg
val dest : tactic_arg -> msequent * tactic_argument
val arg : tactic_arg -> tactic_argument
val goal : tactic_arg -> term

val concl : tactic_arg -> term
val concl_addr : tactic_arg -> address

val hyp_addr : tactic_arg -> int -> address
val clause_addr : tactic_arg -> int -> address

val var_of_hyp : int -> tactic_arg -> string
val get_decl_number : tactic_arg -> string -> int
val nth_hyp : int -> tactic_arg -> term
val declared_vars : tactic_arg -> string list

val get_pos_hyp_index : int -> int -> int
val get_pos_hyp_num : int -> tactic_arg -> int
val hyp_count : tactic_arg -> int

(*
 * $Log$
 * Revision 1.3  1998/06/03 22:19:59  jyh
 * Nonpolymorphic refiner.
 *
 * Revision 1.2  1998/05/28 13:48:35  jyh
 * Updated the editor to use new Refiner structure.
 * ITT needs dform names.
 *
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
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
