(*
 * Here are rules for the Void base type.
 * Void has no elements.  Its propositional
 * interpretation is "False".
 *
 *)

include Tacticals
include Itt_equal
include Itt_subtype

open Refiner.Refiner.Term
open Tacticals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare void

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext Void
 * by voidFormation
 *)
axiom voidFormation 'H : sequent ['ext] { 'H >- univ[@i:l] }

(*
 * H >- Void = Void in Ui ext Ax
 * by voidEquality
 *)
axiom voidEquality 'H : sequent ['ext] { 'H >- void = void in univ[@i:l] }

(*
 * Typehood.
 *)
axiom voidType 'H : sequent ['ext] { 'H >- "type"{void} }

(*
 * H; i:x:Void; J >- C
 * by voidElimination i
 *)
axiom voidElimination 'H 'J : sequent ['ext] { 'H; x: void; 'J['x] >- 'C['x] }

(*
 * Squash elimination.
 *)
axiom void_squashElimination 'H :
   sequent [squash] { 'H >- void } -->
   sequent ['ext] { 'H >- void }

(*
 * Subtyping.
 *)
axiom void_subtype 'H :
   sequent ['ext] { 'H >- subtype{void; 'T} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val d_voidT : int -> tactic
val eqcd_voidT : tactic

val void_term : term

val dT : int -> tactic

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
