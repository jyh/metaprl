(*
 * Although unit is not strictly necessary,
 * we define it anyway, so we can use it before numbers
 * are defined.
 *
 * Type unit contains one element, it.
 *)

include Tacticals

include Itt_equal

open Refiner.Refiner.Term

open Tacticals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare unit

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext Unit
 * by unitFormation
 *)
axiom unitFormation 'H : sequent ['ext] { 'H >- univ[@i:l] }

(*
 * H >- Unit = Unit in Ui ext Ax
 * by unitEquality
 *)
axiom unitEquality 'H : sequent ['ext] { 'H >- unit = unit in univ[@i:l] }

(*
 * H >- Ui ext Unit
 * by unitFormation
 *)
axiom unit_memberFormation 'H : sequent ['ext] { 'H >- unit }

(*
 * H >- Unit = Unit in Ui ext Ax
 * by unitEquality
 *)
axiom unit_memberEquality 'H : sequent ['ext] { 'H >- it = it in unit }

(*
 * H; i:x:Unit; J >- C
 * by unitElimination i
 * H; i:x:Unit; J[it / x] >- C[it / x]
 *)
axiom unitElimination 'H 'J :
   sequent['ext] { 'H; x: unit; 'J[it] >- 'C[it] } -->
   sequent ['ext] { 'H; x: unit; 'J['x] >- 'C['x] }

(*
 * Squash elimination.
 *)
axiom unit_squashElimination 'H :
   sequent [squash] { 'H >- unit } -->
   sequent ['ext] { 'H >- unit }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val d_unitT : int -> tactic
val eqcd_unitT : tactic
val eqcd_itT : tactic
val unit_term : term

(*
 * $Log$
 * Revision 1.4  1998/07/02 18:38:04  jyh
 * Refiner modules now raise RefineError exceptions directly.
 * Modules in this revision have two versions: one that raises
 * verbose exceptions, and another that uses a generic exception.
 *
 * Revision 1.3  1998/05/28 13:48:22  jyh
 * Updated the editor to use new Refiner structure.
 * ITT needs dform names.
 *
 * Revision 1.2  1998/04/22 22:45:26  jyh
 * *** empty log message ***
 *
 * Revision 1.1  1997/08/06 16:18:48  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *: itt_void.mli,v $
 *
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
