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
 * $Log$
 * Revision 1.7  1998/07/02 18:38:06  jyh
 * Refiner modules now raise RefineError exceptions directly.
 * Modules in this revision have two versions: one that raises
 * verbose exceptions, and another that uses a generic exception.
 *
 * Revision 1.6  1998/06/15 22:33:41  jyh
 * Added CZF.
 *
 * Revision 1.5  1998/05/28 13:48:24  jyh
 * Updated the editor to use new Refiner structure.
 * ITT needs dform names.
 *
 * Revision 1.4  1998/04/22 22:45:29  jyh
 * *** empty log message ***
 *
 * Revision 1.3  1998/04/09 18:26:12  jyh
 * Working compiler once again.
 *
 * Revision 1.2  1997/08/06 16:18:50  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *
 * Revision 1.1  1997/04/28 15:52:32  jyh
 * This is the initial checkin of Nuprl-Light.
 * I am porting the editor, so it is not included
 * in this checkin.
 *
 * Directories:
 *     refiner: logic engine
 *     filter: front end to the Ocaml compiler
 *     editor: Emacs proof editor
 *     util: utilities
 *     mk: Makefile templates
 *
 * Revision 1.8  1996/09/02 19:38:48  jyh
 * Semi working package management.
 * All _univ version removed.
 *
 * Revision 1.7  1996/05/21 02:18:34  jyh
 * This is a semi-working version before Wisconsin vacation.
 *
 * Revision 1.6  1996/04/11 13:34:54  jyh
 * This is the final version with the old syntax for terms.
 *
 * Revision 1.5  1996/03/28 02:51:48  jyh
 * This is an initial version of the type theory.
 *
 * Revision 1.4  1996/03/05 19:59:55  jyh
 * Version just before LogicalFramework.
 *
 * Revision 1.3  1996/02/15 20:36:47  jyh
 * Upgrading prlcomp.
 *
 * Revision 1.2  1996/02/13 21:36:15  jyh
 * Intermediate checkin while matching is bing added to the refiner.
 *
 * Revision 1.1  1996/02/10 20:18:18  jyh
 * Initiali checking for base+itt refiners.
 *
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
