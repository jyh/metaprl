(*
 * Standard logical connectives.
 *
 *)

open Refiner.Refiner.Term

include Itt_equal
include Itt_dprod
include Itt_union
include Itt_void
include Itt_unit
include Itt_soft

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

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
