(*
 * Primitiva axiomatization of implication.
 *)

include Czf_itt_all

open Conversionals

rewrite unfold_dall : "all"{'T; x. 'A['x]} <--> Itt_rfun!"fun"{'T; x. 'A['x]}

val fold_dall : conv

(*
 * Intro.
 *
 * H >- all x: T. A
 * by dall_intro
 * H >- member{T; set}
 * H, x: T >- A
 *)
axiom dall_intro 'H 'a :
   sequent ['ext] { 'H >- member{'T; set} } -->
   sequent ['ext] { 'H; a: 'T >- 'A['a] } -->
   sequent ['ext] { 'H >- "all"{'T; x. 'A['x]} }

(*
 * Elimination.
 *
 * H, x: all y:T. A[y]}, J[x] >- T[x]
 * by dall_elim z
 * H, x: all y:T. A[y], J[x] >- member{z; T}
 * H, x: all y:T. A[y], J[x], z: A[z] >- T[x]
 *)
axiom dall_elim 'H 'J 'x 'z 'w :
   sequent ['ext] { 'H; x: "all"{'T; y. 'A['y]}; 'J['x] >- member{'z; 'T} } -->
   sequent ['ext] { 'H; x: "all"{'T; y. 'A['y]}; 'J['x]; w: 'A['z] >- 'C['x] } -->
   sequent ['ext] { 'H; x: "all"{'T; y. 'A['y]}; 'J['x] >- 'C['x] }

(*
 * Well formedness.
 *)
axiom dall_wf 'H 'y :
   sequent ['ext] { 'H >- member{'T; set} } -->
   sequent ['ext] { 'H; y: 'T >- wf{'A['y]} } -->
   sequent ['ext] { 'H >- wf{."all"{'T; x. 'A['x]} } }

(*
 * $Log$
 * Revision 1.1  1998/06/23 22:12:21  jyh
 * Improved rewriter speed with conversion tree and flist.
 *
 *)
