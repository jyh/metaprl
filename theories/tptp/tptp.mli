(*
 * These are the basic terms and axioms of TPTP.
 *)

include Itt_theory

open Refiner.Refiner.TermType

open Conversionals
open Tacticals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(* All and exists are always bound over atom *)
declare "all"{v. 'b['v]}
declare "exists"{v. 'b['v]}
declare "atomic"{'b}
declare "t"

declare "atom0"
declare "atom1"
declare "atom2"
declare "atom3"
declare "atom4"
declare "atom5"
declare "prop0"
declare "prop1"
declare "prop2"
declare "prop3"
declare "prop4"
declare "prop5"

rewrite unfold_atomic : "atomic"{'x} <--> ('x = 'x in atom)
rewrite unfold_all : "all"{v. 'b['v]} <--> Itt_logic!"all"{atom; v. 'b['v]}
rewrite unfold_exists : "exists"{v. 'b['v]} <--> Itt_logic!"exists"{atom; v. 'b['v]}

rewrite unfold_atom0 : atom0 <-->
                          atom
rewrite unfold_atom1 : atom1 <-->
                          atom -> atom
rewrite unfold_atom2 : atom2 <-->
                          atom -> atom -> atom
rewrite unfold_atom3 : atom3 <-->
                          atom -> atom -> atom -> atom
rewrite unfold_atom4 : atom4 <-->
                          atom -> atom -> atom -> atom -> atom
rewrite unfold_atom5 : atom5 <-->
                          atom -> atom -> atom -> atom -> atom -> atom

rewrite unfold_prop0 : prop0 <-->
                          univ[1:l]
rewrite unfold_prop1 : prop1 <-->
                          atom -> univ[1:l]
rewrite unfold_prop2 : prop2 <-->
                          atom -> atom -> univ[1:l]
rewrite unfold_prop3 : prop3 <-->
                          atom -> atom -> atom -> univ[1:l]
rewrite unfold_prop4 : prop4 <-->
                          atom -> atom -> atom -> atom -> univ[1:l]
rewrite unfold_prop5 : prop5 <-->
                          atom -> atom -> atom -> atom -> atom -> univ[1:l]

rewrite unfold_apply2 : "apply"{'f1; 'x1; 'x2} <--> ('f1 'x1 'x2)
rewrite unfold_apply3 : "apply"{'f1; 'x1; 'x2; 'x3} <--> ('f1 'x1 'x2 'x3)
rewrite unfold_apply4 : "apply"{'f1; 'x1; 'x2; 'x3; 'x4} <--> ('f1 'x1 'x2 'x3 'x4)
rewrite unfold_apply5 : "apply"{'f1; 'x1; 'x2; 'x3; 'x4; 'x5} <--> ('f1 'x1 'x2 'x3 'x4 'x5)

val fold_atom0 : conv
val fold_atom1 : conv
val fold_atom2 : conv
val fold_atom3 : conv
val fold_atom4 : conv
val fold_atom5 : conv

val fold_prop0 : conv
val fold_prop1 : conv
val fold_prop2 : conv
val fold_prop3 : conv
val fold_prop4 : conv
val fold_prop5 : conv

val fold_apply2 : conv
val fold_apply3 : conv
val fold_apply4 : conv
val fold_apply5 : conv

val fold_atomic : conv
val fold_all : conv
val fold_exists : conv

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(************************************************************************
 * OPERATIONS                                                           *
 ************************************************************************)

(*
 * Nested terms.
 *)
val t_term : term
val is_t_term : term -> bool

val is_atomic_term : term -> bool
val mk_atomic_term : term -> term
val dest_atomic : term -> term

val is_apply_term : term -> bool
val mk_apply_term : term list -> term
val dest_apply : term -> term list
val arity_of_apply : term -> int
val head_of_apply : term -> term

val mk_or_term : term list -> term
val dest_or : term -> term list

val mk_and_term : term list -> term
val dest_and : term -> term list

val is_all_term : term -> bool
val mk_all_term : string list -> term -> term
val dest_all : term -> string list * term
val var_of_all : term -> string

val is_exists_term : term -> bool
val mk_exists_term : string list -> term -> term
val dest_exists : term -> string list * term
val var_of_exists : term -> string

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * This is for proving intro rules.
 *)
val tptp_autoT : tactic

val t_atomicT : tactic
val atomicT : int -> tactic
val typeT : int -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
