(*
 * Primitiva axiomatization of implication.
 *)

include Czf_itt_wf

open Conversionals

declare "implies"{'A; 'B}

rewrite unfold_implies : "implies"{'A; 'B} <--> "fun"{'A; 'B}

val fold_implies : conv

(*
 * Intro.
 *
 * H >- A => B
 * by implies_intro
 * H >- A wf
 * H, A >- B
 *)
axiom implies_intro 'H 'a :
   sequent ['ext] { 'H >- wf{'A} } -->
   sequent ['ext] { 'H; a: 'A >- 'B } -->
   sequent ['ext] { 'H >- "implies"{'A; 'B} }

(*
 * Elimination.
 *
 * H, x: A => B, J[x] >- T[x]
 * by implies_elim i
 * H, x: A => B, J[x] >- A
 * H, x: A => B, J[x], y: B -> T[x]
 *)
axiom implies_elim 'H 'J 'x 'y :
   sequent ['ext] { 'H; x: "implies"{'A; 'B}; 'J['x] >- 'A } -->
   sequent ['ext] { 'H; x: "implies"{'A; 'B}; 'J['x]; y: 'B >- 'T['x] } -->
   sequent ['ext] { 'H; x: "implies"{'A; 'B}; 'J['x] >- 'T['x] }

(*
 * Well formedness.
 *)
axiom implies_wf 'H :
   sequent ['ext] { 'H >- wf{'A} } -->
   sequent ['ext] { 'H >- wf{'B} } -->
   sequent ['ext] { 'H >- wf{."implies"{'A; 'B}} }

(*
 * Implication is restricted.
 *)
axiom implies_res 'H :
   sequent ['ext] { 'H >- restricted{'A} } -->
   sequent ['ext] { 'H >- restricted{'B} } -->
   sequent ['ext] { 'H >- restricted{."implies"{'A; 'B}} }

(*
 * $Log$
 * Revision 1.1  1998/06/23 22:12:22  jyh
 * Improved rewriter speed with conversion tree and flist.
 *
 *)
