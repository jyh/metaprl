(*
 * Standard logical connectives.
 *
 *)

include Itt_equal
include Itt_rfun
include Itt_dfun
include Itt_fun
include Itt_dprod
include Itt_prod
include Itt_union
include Itt_void
include Itt_unit
include Itt_struct

open Refiner.Refiner.TermType

open Tacticals
open Conversionals

open Base_auto_tactic

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

define unfoldProp : "prop"[@i:l] <--> "univ"[@i:l]

define unfoldTrue : "true" <--> unit
define unfoldFalse : "false" <--> void

define unfoldNot : "not"{'a} <--> 'a -> void

define unfoldAnd : "and"{'a; 'b} <--> 'a * 'b
define unfoldOr : "or"{'a; 'b} <--> 'a + 'b
define unfoldImplies : "implies"{'a; 'b} <--> 'a -> 'b
define unfoldIff : "iff"{'a; 'b} <--> (('a -> 'b) & ('b -> 'a))
define unfoldCand : "cand"{'a; 'b} <--> "and"{'a; 'b}
define unfoldCor : "cor"{'a; 'b} <--> "or"{'a; ."cand"{."not"{'a}; 'b}}

define unfoldAll : "all"{'A; x. 'B['x]} <--> x: 'A -> 'B['x]
define unfoldExists : "exists"{'A; x. 'B['x]} <--> x: 'A * 'B['x]

rewrite reducePropTrue : "prop"["true":t] <--> "true"
rewrite reducePropFalse : "prop"["false":t] <--> "false"

topval foldTrue : conv
topval foldFalse : conv
topval foldNot : conv
topval foldImplies : conv
topval foldIff : conv
topval foldAnd : conv
topval foldOr : conv
topval foldCand : conv
topval foldCor : conv
topval foldAll : conv
topval foldExists : conv

(************************************************************************
 * DISPLAY FORMS							*
 ************************************************************************)

prec prec_iff
prec prec_implies
prec prec_and
prec prec_or
prec prec_quant

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val is_true_term : term -> bool
val true_term : term

val is_false_term : term -> bool
val false_term : term

val is_all_term : term -> bool
val dest_all : term -> string * term * term
val mk_all_term : string -> term -> term -> term

val is_exists_term : term -> bool
val dest_exists : term -> string * term * term
val mk_exists_term : string -> term -> term -> term

val is_or_term : term -> bool
val dest_or : term -> term * term
val mk_or_term : term -> term -> term

val is_and_term : term -> bool
val dest_and : term -> term * term
val mk_and_term : term -> term -> term

val is_cor_term : term -> bool
val dest_cor : term -> term * term
val mk_cor_term : term -> term -> term

val is_cand_term : term -> bool
val dest_cand : term -> term * term
val mk_cand_term : term -> term -> term

val is_implies_term : term -> bool
val dest_implies : term -> term * term
val mk_implies_term : term -> term -> term

val is_iff_term : term -> bool
val dest_iff : term -> term * term
val mk_iff_term : term -> term -> term

val is_not_term : term -> bool
val dest_not : term -> term
val mk_not_term : term -> term

(************************************************************************
 * AUTOMATION                                                           *
 ************************************************************************)

topval univCDT : tactic
topval genUnivCDT : tactic
topval instHypT : term list -> int -> tactic

val logic_prec : auto_prec
val back_hyp_prec : auto_prec
val back_assum_prec : auto_prec

topval backThruHypT : int -> tactic
topval assumT : int -> tactic
topval backThruAssumT : int -> tactic

topval moveToConclT : int -> tactic
topval moveToConclVarsT : string list -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
