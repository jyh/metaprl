(*
 * Utilities for tactics.
 *)

open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.Refine
open Tactic_type

(*
 * Build an initial argument for a proof.
 *)
val create : string -> msequent -> cache -> attributes -> tactic_resources -> tactic_arg

(*
 * Get the address of a part of the sequent.
 *)
val clause_addr : tactic_arg -> int -> address
val get_decl_number : tactic_arg -> string -> int
val hyp_count : tactic_arg -> int
val hyp_indices : tactic_arg -> int -> int * int

(*
 * Get the parts of the argument.
 *)
val goal : tactic_arg -> term
val concl : tactic_arg -> term
val nth_hyp : tactic_arg -> int -> string * term
val cache : tactic_arg -> cache
val label : tactic_arg -> string
val resources : tactic_arg -> tactic_resources
val attributes : tactic_arg -> attributes

(*
 * Get info about the sequent.
 *)
val declared_vars : tactic_arg -> string list
val explode_sequent : tactic_arg -> esequent
val is_free_seq_var : int -> string -> tactic_arg -> bool

(*
 * $Log$
 * Revision 1.4  1998/06/09 20:52:55  jyh
 * Propagated refinement changes.
 * New tacticals module.
 *
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
