(*
 * Simplifications for undependent functions.
 *
 *)

include Tactic_type

include Itt_equal
include Itt_rfun

open Tactic_type

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * H >- Ui ext A -> B
 * by independentFunctionFormation
 *
 * H >- Ui ext A
 * H >- Ui ext B
 *)
axiom independentFunctionFormation 'H :
   sequent ['ext] { 'H >- univ[@i:l] } -->
   sequent ['ext] { 'H >- univ[@i:l] } -->
   sequent ['ext] { 'H >- univ[@i:l] }

(*
 * H >- (A1 -> B1) = (A2 -> B2) in Ui
 * by independentFunctionEquality
 *
 * H >- A1 = A2 in Ui
 * H >- B1 = B2 in Ui
 *)
axiom independentFunctionEquality 'H :
   sequent [squash] { 'H >- 'A1 = 'A2 in univ[@i:l] } -->
   sequent [squash] { 'H >- 'B1 = 'B2 in univ[@i:l] } -->
   sequent ['ext] { 'H >- ('A1 -> 'B1) = ('A2 -> 'B2) in univ[@i:l] }

(*
 * H >- a:A -> B[a] ext lambda(z. b[z])
 * by lambdaFormation Ui z
 *
 * H >- A = A in Ui
 * H, z: A >- B[z] ext b[z]
 *)
axiom independentLambdaFormation 'H 'z :
   sequent [squash] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H; z: 'A >- 'B } -->
   sequent ['ext] { 'H >- 'A -> 'B }

(*
 * H, f: A -> B, J[x] >- T[x]                   ext t[f, f a]
 * by independentFunctionElimination i y
 *
 * H, f: A -> B, J >- A                         ext a
 * H, f: A -> B, J[x], y: B >- T[x]             ext t[f, y]
 *)
axiom independentFunctionElimination 'H 'J 'f 'y :
   sequent ['ext] { 'H; f: 'A -> 'B; 'J['f] >- 'A } -->
   sequent ['ext] { 'H; f: 'A -> 'B; 'J['f]; y: 'B >- 'T['f] } -->
   sequent ['ext] { 'H; f: 'A -> 'B; 'J['f] >- 'T['f] }

(*
 * H >- A1 -> B1 <= A2 -> B2
 * by functionSubtype
 *
 * H >- A2 <= A1
 * H >- B1 <= B2
 *)
axiom independentFunctionSubtype 'H :
   sequent [squash] { 'H >- subtype{'A2; 'A1} } -->
   sequent [squash] { 'H >- subtype{'B1; 'B2} } -->
   sequent ['ext] { 'H >- subtype{ ('A1 -> 'B1); ('A2 -> 'B2) } }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

val d_funT : int -> tactic
val eqcd_funT : tactic

(*
 * $Log$
 * Revision 1.3  1998/04/22 22:44:47  jyh
 * *** empty log message ***
 *
 * Revision 1.2  1997/08/06 16:18:31  jyh
 * This is an ocaml version with subtyping, type inference,
 * d and eqcd tactics.  It is a basic system, but not debugged.
 *
 * Revision 1.1  1997/04/28 15:52:12  jyh
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
 * Revision 1.4  1996/09/02 19:37:24  jyh
 * Semi working package management.
 * All _univ version removed.
 *
 * Revision 1.3  1996/05/21 02:16:47  jyh
 * This is a semi-working version before Wisconsin vacation.
 *
 * Revision 1.2  1996/04/11 13:34:00  jyh
 * This is the final version with the old syntax for terms.
 *
 * Revision 1.1  1996/03/28 02:51:31  jyh
 * This is an initial version of the type theory.
 *
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
