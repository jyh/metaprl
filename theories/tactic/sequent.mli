(*
 * Utilities for tactics.
 *)

open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.Refine

(*
 * Types.
 *)
type extract = Tactic_type.extract
type tactic_arg = Tactic_type.tactic_arg
type tactic_value = Tactic_type.tactic_value
type cache = Tactic_type.cache
type attributes = Tactic_type.attributes

(*
 * Build an initial argument for a proof.
 *)
val create : sentinal -> string -> msequent -> cache -> attributes -> tactic_arg

(*
 * Two tactic_arguments are equal when they have
 * equal msequent parts.  Their labels, etc, are
 * not compared.
 *)
val tactic_arg_alpha_equal : tactic_arg -> tactic_arg -> bool

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
val msequent : tactic_arg -> msequent
val concl : tactic_arg -> term
val nth_hyp : tactic_arg -> int -> string * term
val cache : tactic_arg -> cache
val label : tactic_arg -> string
val attributes : tactic_arg -> attributes

(*
 * Get info about the sequent.
 *)
val declared_vars : tactic_arg -> string list
val explode_sequent : tactic_arg -> esequent
val is_free_seq_var : int -> string -> tactic_arg -> bool

(*
 * Modification of the argument.
 * These are functional.
 *)
val set_goal    : tactic_arg -> term -> tactic_arg
val set_concl   : tactic_arg -> term -> tactic_arg
val set_label   : tactic_arg -> string -> tactic_arg

(*
 * Argument functions.
 *)
val get_term_arg       : tactic_arg -> string -> term
val get_type_arg       : tactic_arg -> string -> term
val get_int_arg        : tactic_arg -> string -> int
val get_bool_arg       : tactic_arg -> string -> bool
val get_subst_arg      : tactic_arg -> term_subst
val get_tactic_arg     : tactic_arg -> string -> Tactic_type.tactic
val get_int_tactic_arg : tactic_arg -> string -> (int -> Tactic_type.tactic)
val get_typeinf_arg    : tactic_arg -> string -> (term_subst -> term -> term_subst * term)

(*
 * $Log$
 * Revision 1.6  1998/07/02 22:25:32  jyh
 * Created term_copy module to copy and normalize terms.
 *
 * Revision 1.5  1998/06/16 16:26:22  jyh
 * Added itt_test.
 *
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
