(*
 * The "set" type is used to relate CZF to the Nuprl type theory.
 * The set type is defined inductively.
 *    The base types are:
 *       1. int
 *       2. fun{A; x.B[x]}
 *       3. exists{A; x.B[x]}
 *       4. union{A; B}
 *       5. equal{A; a; b}
 *
 *    The inductive construction is given by rule:
 *       6. H >- T in U1         H, x:T >- a in set
 *          -------------------------------------
 *               H >- collect{T; x. a[x]} in set
 *
 * We could define this set recursively.  Instead, we define it
 * as a collection of rules.
 *)

include Itt_theory

open Refiner.Refiner.Term

open Tactic_type

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "set"
declare member{'x; 't}

(*
 * These are the small types from which sets are built.
 *)
declare small
declare small_type{'t}

(*
 * The "collect" term is used to build sets.
 *)
declare "collect"{'T; x. 'a['x]}

(************************************************************************
 * SMALL TYPE RULES                                                     *
 ************************************************************************)

(*
 * These are the types in the small universe.
 *)
axiom hyp_small 'H 'J :
   sequent ['ext] { 'H; a: small; 'J['a] >- small_type{'a} }

axiom int_small 'H :
   sequent ['ext] { 'H >- small_type{int} }

axiom fun_small 'H :
   sequent ['ext] { 'H >- small_type{'A} } -->
   sequent ['ext] { 'H; a: 'A >- small_type{'B['a]} } -->
   sequent ['ext] { 'H >- small_type{(a: 'A -> 'B['a])} }

axiom exists_small 'H :
   sequent ['ext] { 'H >- small_type{'A} } -->
   sequent ['ext] { 'H; a: 'A >- small_type{'B['a]} } -->
   sequent ['ext] { 'H >- small_type{(a: 'A * 'B['a])} }

axiom union_small 'H :
   sequent ['ext] { 'H >- small_type{'A} } -->
   sequent ['ext] { 'H >- small_type{'B} } -->
   sequent ['ext] { 'H >- small_type{('A + 'B)} }

axiom equal_small 'H :
   sequent ['ext] { 'H >- small_type{'A} } -->
   sequent ['ext] { 'H >- 'a = 'a in 'A } -->
   sequent ['ext] { 'H >- 'b = 'b in 'A } -->
   sequent ['ext] { 'H >- small_type{('a = 'b in 'A)} }

(*
 * There are no other small types.
 *)
axiom small_elim 'H 'J (a1: 'A1 -> 'B1) (a2:'A2 * 'B2) ('A3 + 'B3) ('a4 = 'b4 in 'A4) :
   sequent ['ext] { 'H; 'J[int] >- 'C[int] } -->
   sequent ['ext] { 'H; A1: small; B1: 'A1 -> small; 'J[(a1:'A1 -> 'B1 'a1)] >- 'C[(a1:'A1 -> 'B1 'a1)] } -->
   sequent ['ext] { 'H; A2: small; B2: 'A2 -> small; 'J[(a2:'A2 * 'B2 'a2)] >- 'C[(a2:'A2 * 'B2 'a2)] } -->
   sequent ['ext] { 'H; A3: small; B3: small; 'J[('A3 + 'B3)] >- 'C[('A3 + 'B3)] } -->
   sequent ['ext] { 'H; A4: small; a4: 'A4; b: 'A4; 'J[('a4 = 'b4 in 'A4)] >- 'C[('a4 = 'b4 in 'A4)] } -->
   sequent ['ext] { 'H; x: small; 'J['x] >- 'C['x] }

(************************************************************************
 * SET TYPE                                                             *
 ************************************************************************)

(*
 * This is how a set is constructed.
 *)
axiom collect_set 'H :
   sequent ['ext] { 'H >- small_type{'T} } -->
   sequent ['ext] { 'H; x: 'T >- member{'a['x]; set} } -->
   sequent ['ext] { 'H >- member{collect{'T; x. 'a['x]}; set} }

(*
 * Transfinite induction.
 *)
axiom set_elim 'H 'J 'a 'T 'f 'w :
   sequent ['ext] { 'H; a: set; 'J['a]; T: small; f: 'T -> set; w: (all x : 'T. 'C['f 'x]) >- 'C[collect{'T; x. 'f 'x}] } -->
   sequent ['ext] { 'H; a: set; 'J['a] >- 'C['a] }

(************************************************************************
 * MEMBERSHIP TACTIC                                                    *
 ************************************************************************)

type memd_data

resource (term * tactic, tactic, memd_data) memd_resource

val memd_of_proof : tactic_arg -> tactic

val memdT : tactic

val x_resource : Base_dtactic.d_resource

val dT : int -> tactic

(*
 * $Log$
 * Revision 1.1  1998/06/15 22:32:50  jyh
 * Added CZF.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
