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
type 'a attributes = 'a Tactic_type.attributes

(*
 * Build an initial argument for a proof.
 *)
val create : sentinal -> string -> msequent -> cache -> term attributes -> tactic_arg

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
val get_pos_hyp_num : tactic_arg -> int -> int

(*
 * Get the parts of the argument.
 *)
val goal : tactic_arg -> term
val msequent : tactic_arg -> msequent
val concl : tactic_arg -> term
val nth_hyp : tactic_arg -> int -> string * term
val cache : tactic_arg -> cache
val label : tactic_arg -> string
val attributes : tactic_arg -> term attributes

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
val get_arg_tactic_arg : tactic_arg -> string -> tactic_arg -> Tactic_type.tactic
val get_typeinf_arg    : tactic_arg -> string -> (term_subst -> term -> term_subst * term)

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
