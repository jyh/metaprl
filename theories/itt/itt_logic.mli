(*
 * Standard logical connectives.
 *
 *)

include Itt_equal
include Itt_dprod
include Itt_union
include Itt_void
include Itt_unit
include Itt_soft
include Itt_struct

open Refiner.Refiner.TermType

open Tacticals

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

define unfoldAll : "all"{'A; x. 'B['x]} <--> x: 'A -> 'B['x]
define unfoldExists : "exists"{'A; x. 'B['x]} <--> x: 'A * 'B['x]

rewrite reducePropTrue : "prop"["true":t] <--> "true"
rewrite reducePropFalse : "prop"["false":t] <--> "false"

(************************************************************************
 * EXTRA RULES                                                          *
 ************************************************************************)

(*
 * All elimination.
 *)
axiom allElimination 'H 'J 'w 'z :
   sequent [squash] { 'H; x: all a: 'A. 'B['a]; 'J['x] >- 'z = 'z in 'A } -->
   sequent ['ext] { 'H; x: all a: 'A. 'B['a]; 'J['x]; w: 'B['z] >- 'C['x] } -->
   sequent ['ext] { 'H; x: all a: 'A. 'B['a]; 'J['x] >- 'C['x] }

(*
 * IFF typehood.
 *)
axiom iffType 'H :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent [squash] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- "type"{iff{'A; 'B}} }

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

val univCDT : tactic
val genUnivCDT : tactic
val instHypT : term list -> int -> tactic

val back_hyp_prec : auto_prec
val back_assum_prec : auto_prec

val backThruHypT : int -> tactic
val assumT : int -> tactic
val backThruAssumT : int -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
