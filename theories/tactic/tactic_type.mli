(*
 * Define the common types.
 * A file with this name is required for every theory.
 *)

open Nl_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermSubst
open Refiner.Refiner.Refine

(************************************************************************
 * TYPES                                                                *
 ************************************************************************)

(*
 * Attributes are values that inherited in the
 * proof tree.  These are an incomplete set of
 * the simple attributes.  They are listed to
 * make proof marshaling easier.  All other
 * attributes should be fetched through the
 * attribute functions.
 *)
type 'term attribute =
   TermArg of 'term
 | TypeArg of 'term
 | IntArg of int
 | BoolArg of bool
 | SubstArg of 'term

and 'a attributes = (string * 'a attribute) list

(*
 * Thes are the attributes that are used internally.
 *)
and raw_attribute
and raw_attributes = raw_attribute list

(*
 * Here are all the different type of tactics.
 *    1. A tactic_arg contains all the info about the argument
 *    2. An extract contains the info to produce a Refine.extract
 *    3. A tactic_value is the abstract result of a tactic,
 *       which can be used to provide a (tactic_arg list * extract)
 *    4. A pre_tactic is some precompiled info used to construct a tactic.
 *    5. A tactic is a refinement
 *)
and tactic_arg
and tactic_value
and extract
and pre_tactic
and sentinal
and tactic = tactic_arg -> tactic_value

(*
 * The cache is the abstract representation
 * of sequents.  The justifications for these sequents
 * are tactics.
 *)
and cache = tactic Tactic_cache.extract
and raw_cache

(************************************************************************
 * OPERATIONS                                                           *
 ************************************************************************)

(*
 * Build an initial argument for a proof.
 *)
val create : sentinal -> string -> msequent -> raw_cache -> raw_attributes -> tactic_arg

(*
 * Sentinals are computed by naming the module and
 * rule for the sentinal.
 *)
val sentinal_of_refiner : string -> sentinal
val sentinal_of_refiner_object : string -> string -> sentinal

(*
 * Cache is also computed lazily.
 *)
val make_cache : (unit -> cache) -> raw_cache

(*
 * Start the main loop.
 *)
val args : unit -> (string * Arg.spec * string) list
val main_loop : unit -> unit

(*
 * Access to the argument.
 *)
val goal        : tactic_arg -> term
val msequent    : tactic_arg -> msequent
val nth_hyp     : tactic_arg -> int -> string * term
val nth_concl   : tactic_arg -> int -> term
val cache       : tactic_arg -> cache
val label       : tactic_arg -> string

(*
 * Modification of the argument.
 * These are functional.
 *)
val set_goal    : tactic_arg -> term -> tactic_arg
val set_concl   : tactic_arg -> term -> tactic_arg
val set_label   : tactic_arg -> string -> tactic_arg

(*
 * Install new attributes.
 *)
val term_attribute : string -> term -> raw_attribute
val type_attribute : string -> term -> raw_attribute
val int_attribute : string -> int -> raw_attribute
val bool_attribute : string -> bool -> raw_attribute
val subst_attribute : string -> term -> raw_attribute
val tactic_attribute : string -> (unit -> tactic) -> raw_attribute
val int_tactic_attribute : string -> (unit -> int -> tactic) -> raw_attribute
val arg_tactic_attribute : string -> (unit -> tactic_arg -> tactic) -> raw_attribute
val typeinf_attribute : string -> (unit -> unify_subst -> term -> unify_subst * term) -> raw_attribute

(*
 * Fetch attributes.
 *)
val attributes     : tactic_arg -> term attributes
val get_term       : tactic_arg -> string -> term
val get_type       : tactic_arg -> string -> term
val get_int        : tactic_arg -> string -> int
val get_bool       : tactic_arg -> string -> bool
val get_subst      : tactic_arg -> term_subst
val get_tactic     : tactic_arg -> string -> tactic
val get_int_tactic : tactic_arg -> string -> (int -> tactic)
val get_arg_tactic : tactic_arg -> string -> (tactic_arg -> tactic)
val get_typeinf    : tactic_arg -> string -> (unify_subst -> term -> unify_subst * term)

(*
 * Map a function over the terms in an attribute list.
 *)
val map_attributes : ('a -> 'b) -> 'a attributes -> 'b attributes

(*
 * Two tactic_arguments are equal when they have
 * equal msequent parts.  Their labels, etc, are
 * not compared.
 *)
val tactic_arg_alpha_equal : tactic_arg -> tactic_arg -> bool

(*
 * Apply a tactic.
 *)
val refine : tactic -> tactic_arg -> tactic_arg list * extract
val compose : extract -> extract list -> extract
val term_of_extract : Refine.refiner -> extract -> term list -> term

(*
 * Lift refiner tactics into our tactic type.
 * These functions are required by the Filter_prog module.
 *)
val compile_rule : build -> prim_tactic -> pre_tactic
val tactic_of_rule : pre_tactic -> address array * string array -> term list -> tactic

(*
 * Also convert rewrites.
 *)
val tactic_of_rewrite : rw -> tactic
val tactic_of_cond_rewrite : cond_rewrite -> tactic

(*
 * Basic tactics.
 *)
val idT : tactic
val nthAssumT : int -> tactic

(*
 * Basic tacticals.
 *)
val prefix_thenT : tactic -> tactic -> tactic
val prefix_thenLT : tactic -> tactic list -> tactic
val prefix_thenFLT : tactic -> (tactic_arg list -> tactic_value list) -> tactic
val prefix_orelseT : tactic -> tactic -> tactic

(*
 * Argument management.
 *)
val setLabelT : string -> tactic
val withTermT : string -> term -> tactic -> tactic
val withTypeT : string -> term -> tactic -> tactic
val withBoolT : string -> bool -> tactic -> tactic
val withIntT : string -> int -> tactic -> tactic
val withSubstT : term_subst -> tactic -> tactic
val withTacticT : string -> tactic -> tactic -> tactic

(*
 * Print timing information.
 *)
val timingT : tactic -> tactic
val finalT : (unit -> unit) -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
