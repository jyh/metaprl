(*
 * This interpretation of CZF is derived from Aczel's
 * paper "The Type Theoretic Interpretation of Constructive
 * Set Theory: Inductive Definitions," Logic, Methodology
 * and Philosophy of Science VII, Barcan Marcus et. al. eds.,
 * Elsevier 1986 17--49.
 *
 * The "set" type is used to relate CZF to the Nuprl type theory.
 * We use a W-type over U1 to define sets.
 *
 *    type set = W(x:U1. x)
 *
 * We abbreviate the sets themselves as:
 *    collect{T; x. a[x]} = tree{T; lambda x. a[x]}
 *
 * This interpretation justifies Aczel's construction:
 *
 *          H >- T in small     H, x:T >- a[x] in set
 *          -----------------------------------------
 *               H >- collect{T; x. a[x]} in set
 *)

include Czf_itt_eq_inner

open Refiner.Refiner.Term

open Tacticals
open Conversionals

open Base_auto_tactic

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*
 * Sets are built by collecting over small types.
 *   set: the type of all sets
 *   isset{'s}: the judgement that 's is a set
 *)
declare set
declare isset{'s}

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

(*
 * Sets.
 *)
rewrite unfold_set : set <--> (quot x, y: pre_set // eq_inner{'x; 'y})
rewrite unfold_isset : isset{'s} <--> ('s = 's in set)

val fold_set : conv
val fold_isset : conv

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * A set is a type in ITT.
 *)
axiom set_type 'H :
   sequent ['ext] { 'H >- "type"{set} }

(*
 * Equality from sethood.
 *)
axiom equal_set 'H :
   sequent ['ext] { 'H >- isset{'s} } -->
   sequent ['ext] { 'H >- 's = 's in set }

(*
 * By assumption.
 *)
axiom isset_assum 'H 'J :
   sequent ['ext] { 'H; x: set; 'J['x] >- isset{'x} }

(*
 * This is how a set is constructed.
 *)
axiom isset_collect2 'H 'y :
   sequent [squash] { 'H >- 'T = 'T in univ[1:l] } -->
   sequent [squash] { 'H; y: 'T >- is_pre_set{'a['y]} } -->
   sequent ['ext] { 'H >- isset{collect{'T; x. 'a['x]}} }

(*
 * Applications often come up.
 * This is not a necessary axiom, ut it is useful.
 *)
axiom isset_apply 'H 'J :
   sequent [squash] { 'H; f: 'T -> set; 'J['f] >- 'x = 'x in 'T } -->
   sequent ['ext] { 'H; f: 'T -> set; 'J['f] >- isset{.'f 'x} }

(*
 * Induction.  This requires extensional Nuprl.
 *)
axiom set_elim 'H 'J 'a 'T 'f 'w 'z :
   sequent ['ext] { 'H;
                    a: set;
                    'J['a];
                    T: univ[1:l];
                    f: 'T -> set;
                    w: (all x : 'T. 'C['f 'x]);
                    z: isset{collect{'T; x. 'f 'x}}
                  >- 'C[collect{'T; x. 'f 'x}]
                  } -->
                     sequent ['ext] { 'H; a: set; 'J['a] >- 'C['a] }

(*
 * These are related forms to expand a set into its
 * collect representation.
 *)
axiom set_split_hyp2 'H 'J 's (bind{v. 'A['v]}) 'T 'f 'z :
   sequent [squash] { 'H; x: 'A['s]; 'J['x] >- isset{'s} } -->
   sequent [squash] { 'H; x: 'A['s]; 'J['x]; z: set >- "type"{'A['z]} } -->
   sequent ['ext] { 'H;
                    x: 'A['s];
                    'J['x];
                    T: univ[1:l];
                    f: 'T -> set;
                    z: 'A[collect{'T; y. 'f 'y}]
                    >- 'C['x] } -->
   sequent ['ext] { 'H; x: 'A['s]; 'J['x] >- 'C['x] }

axiom set_split_concl 'H 's (bind{v. 'C['v]}) 'T 'f 'z :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent [squash] { 'H; z: set >- "type"{'C['z]} } -->
   sequent ['ext] { 'H; T: univ[1:l]; f: 'T -> set >- 'C[collect{'T; y. 'f 'y}] } -->
   sequent ['ext] { 'H >- 'C['s] }

(*
 * Equality on tree induction forms.
 *)
axiom set_ind_equality 'H 'A (bind{x.'B['x]}) 'a 'f 'g :
   sequent [squash] { 'H >- 'z1 = 'z2 in set } -->
   sequent [squash] { 'H; a: 'A; f: 'B['a] -> set; g: a: 'A -> 'B['a] -> 'T >-
      'body1['a; 'f; 'g] = 'body2['a; 'f; 'g] in 'T } -->
   sequent ['ext] { 'H >- set_ind{'z1; a1, f1, g1. 'body1['a1; 'f1; 'g1]}
                          = set_ind{'z2; a2, f2, g2. 'body2['a2; 'f2; 'g2]}
                          in 'T }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * isset{'s} => 's = 's in set
 *)
val eqSetT : tactic

(*
 * H, x: set, J >- isset{x}
 *)
val setAssumT : int -> tactic

(*
 * Every set is a pre_set.
 *)
val setPreSetT : tactic

(*
 * Replace a set with a collect.
 *)
val splitT : term -> int -> tactic

(*
 * Automation.
 *)
val set_prec : auto_prec

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
