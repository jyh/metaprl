(*
 * Small type is used to index the set w-type.
 * The small type is just U1.
 *)

include Itt_theory

open Tacticals
open Conversionals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

(*
 * These are the small types from which sets are built.
 *    small: the type of small propositions
 *    small_type{'t}: 't = 't in small
 *)
declare small
declare small_type{'t}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

rewrite unfold_small : small <--> univ[1:l]
rewrite unfold_small_type : small_type{'t} <--> ('t = 't in small)

val fold_small : conv
val fold_small_type : conv

(************************************************************************
 * SMALL TYPE RULES                                                     *
 ************************************************************************)

axiom small_type 'H :
   sequent ['ext] { 'H >- "type"{small} }

axiom small_type_type 'H :
   sequent [squash] { 'H >- small_type{'x} } -->
   sequent ['ext] { 'H >- "type"{'x} }

(*
 * These are the types in the small universe.
 *)
axiom void_small 'H :
   sequent ['ext] { 'H >- small_type{void} }

axiom unit_small 'H :
   sequent ['ext] { 'H >- small_type{unit} }

axiom int_small 'H :
   sequent ['ext] { 'H >- small_type{int} }

axiom dfun_small 'H 'z :
   sequent ['ext] { 'H >- small_type{'A} } -->
   sequent ['ext] { 'H; z: 'A >- small_type{'B['z]} } -->
   sequent ['ext] { 'H >- small_type{. a: 'A -> 'B['a]} }

axiom fun_small 'H :
   sequent ['ext] { 'H >- small_type{'A} } -->
   sequent ['ext] { 'H >- small_type{'B} } -->
   sequent ['ext] { 'H >- small_type{. 'A -> 'B} }

axiom dprod_small 'H 'z :
   sequent ['ext] { 'H >- small_type{'A} } -->
   sequent ['ext] { 'H; z: 'A >- small_type{'B['z]} } -->
   sequent ['ext] { 'H >- small_type{. a: 'A * 'B['a]} }

axiom prod_small 'H :
   sequent ['ext] { 'H >- small_type{'A} } -->
   sequent ['ext] { 'H >- small_type{'B} } -->
   sequent ['ext] { 'H >- small_type{. 'A * 'B} }

axiom union_small 'H :
   sequent ['ext] { 'H >- small_type{'A} } -->
   sequent ['ext] { 'H >- small_type{'B} } -->
   sequent ['ext] { 'H >- small_type{. 'A + 'B} }

axiom equal_small 'H :
   sequent ['ext] { 'H >- small_type{'A} } -->
   sequent ['ext] { 'H >- 'a = 'a in 'A } -->
   sequent ['ext] { 'H >- 'b = 'b in 'A } -->
   sequent ['ext] { 'H >- small_type{. 'a = 'b in 'A} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * small_type{'x} => type{'x}
 *)
val smallTypeT : tactic

val smallAssumT : int -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
