(*
 * We define an equality on sets.
 * The normal intensional equality ('s1 = 's2 in set) is
 * not sufficient, because it is not a small type (it is in U2).
 *
 * We define and extensional equality by induction
 * on the sets.
 *)

include Czf_itt_set

open Refiner.Refiner.TermType

open Tacticals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare eq{'s1; 's2}
declare eq_inner{'s1; 's2}
declare fun_set{z. 'f['z]}
declare fun_prop{z. 'P['z]}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

rewrite reduce_eq_inner : eq_inner{collect{'T1; x1. 'f1['x1]}; collect{'T2; x2. 'f2['x2]}} <-->
   ((all y1 : 'T1. exst y2: 'T2. eq_inner{.'f1['y1]; .'f2['y2]})
    & (all y2 : 'T2. exst y1: 'T1. eq_inner{.'f1['y1]; .'f2['y2]}))

rewrite unfold_eq : eq{'s1; 's2} <-->
   ((isset{'s1} & isset{'s2}) & eq_inner{'s1; 's2})

rewrite reduce_eq : eq{collect{'T1; x1. 'f1['x1]}; collect{'T2; x2. 'f2['x2]}} <-->
   ((isset{collect{'T1; x1. 'f1['x1]}} & isset{collect{'T2; x2. 'f2['x2]}})
   & ((all y1 : 'T1. exst y2: 'T2. eq_inner{.'f1['y1]; .'f2['y2]})
     & (all y2 : 'T2. exst y1: 'T1. eq_inner{.'f1['y1]; .'f2['y2]})))

(*
 * A functional predicate can produce proofs for
 * all equal sets.
 *)
rewrite unfold_fun_set : fun_set{z. 'f['z]} <-->
    (all s1: set. all s2: set. (eq{'s1; 's2} => eq{'f['s1]; 'f['s2]}))

rewrite unfold_fun_prop : fun_prop{z. 'P['z]} <-->
    (all s1: set. all s2: set. (eq{'s1; 's2} => 'P['s1] => 'P['s2]))

rewrite unfold_dfun_prop : fun_prop{u. 'A['u]; v. 'B['v]} <-->
    (all s1: set. all s2: set. (eq{'s1; 's2} => (all x: 'A['s1]. all y: 'A['s2]. ('B['x] => 'B['y]))))

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Membership in a universe.
 *)
axiom eq_inner_equality1 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- eq_inner{'s1; 's2} = eq_inner{'s1; 's2} in univ[1:l] }

(*
 * Membership in a universe.
 *)
axiom eq_inner_type 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent ['ext] { 'H >- "type"{eq_inner{'s1; 's2}} }

(*
 * More general equality in a universe.
 *)
axiom eq_inner_equality2 'H :
   sequent [squash] { 'H >- 's1 = 's3 in set } -->
   sequent [squash] { 'H >- 's2 = 's4 in set } -->
   sequent ['ext] { 'H >- eq_inner{'s1; 's2} = eq_inner{'s3; 's4} in univ[1:l] }

(*
 * Functionality of eq_inner.
 *)
axiom eq_inner_fun 'H :
   sequent ['ext] { 'H >- fun_set{z. 'f1['z]} } -->
   sequent ['ext] { 'H >- fun_set{z. 'f2['z]} } -->
   sequent ['ext] { 'H >- fun_prop{z. eq_inner{'f1['z]; 'f2['z]}} }

(*
 * Equality typehood.
 *)
axiom eq_type 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent [squash] { 'H >- isset{'s2} } -->
   sequent [squash] { 'H >- "type"{eq{'s1; 's2}} }

(*
 * Equality is over sets.
 *)
axiom eq_isset_left 'H 's2 :
   sequent ['ext] { 'H >- eq{'s1; 's2} } -->
   sequent ['ext] { 'H >- isset{'s1} }

axiom eq_isset_right 'H 's1 :
   sequent ['ext] { 'H >- eq{'s1; 's2} } -->
   sequent ['ext] { 'H >- isset{'s2} }

(*
 * Reflexivity.
 *)
axiom eq_ref 'H :
   sequent [squash] { 'H >- isset{'s1} } -->
   sequent ['ext] { 'H >- eq{'s1; 's1} }

(*
 * Symettry.
 *)
axiom eq_sym 'H :
   sequent ['ext] { 'H >- eq{'s2; 's1} } -->
   sequent ['ext] { 'H >- eq{'s1; 's2} }

(*
 * Transitivity.
 *)
axiom eq_trans 'H 's2 :
   sequent ['ext] { 'H >- eq{'s1; 's2} } -->
   sequent ['ext] { 'H >- eq{'s2; 's3} } -->
   sequent ['ext] { 'H >- eq{'s1; 's3} }

(*
 * Finally, functionality puts them all together.
 *)
axiom eq_fun 'H :
   sequent ['ext] { 'H >- fun_set{z. 'f1['z]} } -->
   sequent ['ext] { 'H >- fun_set{z. 'f2['z]} } -->
   sequent ['ext] { 'H >- fun_prop{z. eq{'f1['z]; 'f2['z]}} }

(*
 * Substitution over functional expressions.
 *)
axiom eq_hyp_subst 'H 'J 's1 's2 (bind{v. 'P['v]}) 'z :
   sequent ['ext] { 'H; x: 'P['s1]; 'J['x] >- eq{'s1; 's2} } -->
   sequent ['ext] { 'H; x: 'P['s1]; 'J['x]; z: 'P['s2] >- 'C['x] } -->
   sequent ['ext] { 'H; x: 'P['s1]; 'J['x] >- fun_prop{z. 'P['z]} } -->
   sequent ['ext] { 'H; x: 'P['s1]; 'J['x] >- 'C['x] }

axiom eq_concl_subst 'H 's1 's2 (bind{v. 'C['v]}) 'z :
   sequent ['ext] { 'H >- eq{'s1; 's2} } -->
   sequent ['ext] { 'H >- 'C['s2] } -->
   sequent ['ext] { 'H >- fun_prop{z. 'C['z]} } -->
   sequent ['ext] { 'H >- 'C['s1] }

(*
 * Typehood of fun propositions.
 *)
axiom fun_set_type 'H :
   sequent ['ext] { 'H; z: set >- isset{'f['z]} } -->
   sequent ['ext] { 'H >- "type"{fun_set{z. 'f['z]}} }

axiom fun_prop_type 'H :
   sequent [squash] { 'H; z: set >- "type"{'f['z]} } -->
   sequent ['ext] { 'H >- "type"{fun_prop{z. 'f['z]}} }

(*
 * Unquantified sets are functional.
 *)
axiom fun_set 'H :
   sequent ['ext] { 'H >- isset{'u} } -->
   sequent ['ext] { 'H >- fun_set{z. 'u} }

axiom fun_ref 'H :
   sequent ['ext] { 'H >- fun_set{z. 'z} }

(*
 * LEMMAS:
 * Every functional type is a type.
 *)
axiom fun_set_is_set 'H (bind{z. 'P['z]}) 's :
   sequent ['ext] { 'H >- isset{'s} } -->
   sequent ['ext] { 'H >- fun_set{z. 'P['z]} } -->
   sequent ['ext] { 'H >- isset{'P['s]} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val is_eq_term : term -> bool
val mk_eq_term : term -> term -> term
val dest_eq : term -> term * term

val is_fun_set_term : term -> bool
val mk_fun_set_term : string -> term -> term
val dest_fun_set : term -> string * term

val is_fun_prop_term : term -> bool
val mk_fun_prop_term : string -> term -> term
val dest_fun_prop : term -> string * term

(*
 * Equality relations.
 *)
val eqSetRefT : tactic
val eqSetSymT : tactic
val eqSetTransT : term -> tactic

(*
 * 's1 = 's2 => isset{'s1}
 *)
val eqSetLeftT : term -> tactic

(*
 * 's1 = 's2 => isset{'s2}
 *)
val eqSetRightT : term -> tactic

(*
 * Substitution.
 *)
val setSubstT : term -> int -> tactic

(*
 * $Log$
 * Revision 1.1  1998/07/14 15:43:16  jyh
 * Intermediate version with auto tactic.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
