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
type tactic = Tactic_type.tactic
type tactic_arg = Tactic_type.tactic_arg
type tactic_value = Tactic_type.tactic_value
type cache = Tactic_type.cache
type raw_cache = Tactic_type.raw_cache
type sentinal = Tactic_type.sentinal
type 'a attributes = 'a Tactic_type.attributes
type raw_attribute = Tactic_type.raw_attribute
type raw_attributes = Tactic_type.raw_attributes

(*
 * Build an initial argument for a proof.
 *)
val create : Tactic_type.sentinal -> string -> msequent -> raw_cache -> raw_attributes -> tactic_arg

(*
 * Sentinals.
 *)
val sentinal_of_refiner : string -> sentinal
val sentinal_of_refiner_object : string -> string -> sentinal

(*
 * Cache.
 *)
val make_cache : (unit -> cache) -> raw_cache
val cache : tactic_arg -> cache

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
val hyp_count_addr : tactic_arg -> address
val hyp_split_addr : tactic_arg -> int -> address * address
val hyp_indices : tactic_arg -> int -> address * address
val get_pos_hyp_num : tactic_arg -> int -> int

(*
 * Get the parts of the argument.
 *)
val goal : tactic_arg -> term
val msequent : tactic_arg -> msequent
val concl : tactic_arg -> term
val nth_hyp : tactic_arg -> int -> string * term
val label : tactic_arg -> string

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
 * Attribute construction.
 *)
val term_attribute       : string -> term -> raw_attribute
val type_attribute       : string -> term -> raw_attribute
val int_attribute        : string -> int -> raw_attribute
val bool_attribute       : string -> bool -> raw_attribute
val subst_attribute      : string -> term -> raw_attribute
val tactic_attribute     : string -> (unit -> tactic) -> raw_attribute
val int_tactic_attribute : string -> (unit -> int -> tactic) -> raw_attribute
val arg_tactic_attribute : string -> (unit -> tactic_arg -> tactic) -> raw_attribute
val typeinf_attribute    : string -> (unit -> unify_subst -> term -> unify_subst * term) -> raw_attribute

(*
 * Argument functions.
 *)
val attributes         : tactic_arg -> term attributes
val get_term_arg       : tactic_arg -> string -> term
val get_type_arg       : tactic_arg -> string -> term
val get_int_arg        : tactic_arg -> string -> int
val get_bool_arg       : tactic_arg -> string -> bool
val get_subst_arg      : tactic_arg -> term_subst
val get_tactic_arg     : tactic_arg -> string -> Tactic_type.tactic
val get_int_tactic_arg : tactic_arg -> string -> (int -> Tactic_type.tactic)
val get_arg_tactic_arg : tactic_arg -> string -> tactic_arg -> Tactic_type.tactic
val get_typeinf_arg    : tactic_arg -> string -> (unify_subst -> term -> unify_subst * term)

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
