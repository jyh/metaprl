(*
 * Primitiva axiomatization of implication.
 *)

include Czf_itt_set

open Conversionals

declare "or"{'A; 'B}
declare inl{'A}
declare inr{'A}

rewrite unfold_or : "or"{'A; 'B} <--> union{'A; 'B}
rewrite unfold_inl : inl{'a} <--> Itt_union!inl{'a}
rewrite unfold_inr : inr{'a} <--> Itt_union!inr{'a}

val fold_or : conv
val fold_inl : conv
val fold_inr : conv

(*
 * Intro.
 *
 * H >- A \/ B
 * by or_intro_left
 * H >- A
 * H >- B wf
 *)
axiom or_intro_left 'H :
   sequent ['ext] { 'H >- 'A } -->
   sequent ['ext] { 'H >- wf{'B} } -->
   sequent ['ext] { 'H >- "or"{'A; 'B} }

axiom or_intro_right 'H :
   sequent ['ext] { 'H >- 'B } -->
   sequent ['ext] { 'H >- wf{'A} } -->
   sequent ['ext] { 'H >- "or"{'A; 'B} }

(*
 * Elimination.
 *
 * H, x: A \/ B, J[x] >- T[x]
 * by or_elim i
 * H, x: A \/ B, y: A; J[inl y] >- T[inl y]
 * H, x: A \/ B, y: B; J[inr y] >- T[inr y]
 *)
axiom or_elim 'H 'J 'y :
   sequent ['ext] { 'H; x: "or"{'A; 'B}; y: 'A; 'J[inl{'y}] >- 'T[inl{'y}] } -->
   sequent ['ext] { 'H; x: "or"{'A; 'B}; y: 'B; 'J[inr{'y}] >- 'T[inr{'y}] } -->
   sequent ['ext] { 'H; x: "or"{'A; 'B}; 'J['x] >- 'T['x] }

(*
 * Well formedness.
 *)
axiom or_wf 'H :
   sequent ['ext] { 'H >- wf{'A} } -->
   sequent ['ext] { 'H >- wf{'B} } -->
   sequent ['ext] { 'H >- wf{."or"{'A; 'B}} }

(*
 * Implication is restricted.
 *)
axiom or_res 'H :
   sequent ['ext] { 'H >- restricted{'A} } -->
   sequent ['ext] { 'H >- restricted{'B} } -->
   sequent ['ext] { 'H >- restricted{."or"{'A; 'B}} }

(*
 * $Log$
 * Revision 1.4  1998/07/02 18:37:13  jyh
 * Refiner modules now raise RefineError exceptions directly.
 * Modules in this revision have two versions: one that raises
 * verbose exceptions, and another that uses a generic exception.
 *
 * Revision 1.3  1998/06/23 22:12:23  jyh
 * Improved rewriter speed with conversion tree and flist.
 *
 * Revision 1.2  1998/06/22 19:46:07  jyh
 * Rewriting in contexts.  This required a change in addressing,
 * and the body of the context is the _last_ subterm, not the first.
 *
 * Revision 1.1  1998/06/16 16:26:03  jyh
 * Added itt_test.
 *
 *)
