(*
 * Primitiva axiomatization of implication.
 *)

include Czf_itt_set

open Tacticals
open Conversionals

declare "all"{x. 'A['x]}

rewrite unfold_all : "all"{x. 'A['x]} <--> Itt_rfun!"fun"{set; x. 'A['x]}

val fold_all : conv

(*
 * Intro.
 *
 * H >- all x. A
 * by all_intro
 * H, x: set >- A
 *)
axiom all_intro 'H 'a :
   sequent ['ext] { 'H; a: set >- 'A['a] } -->
   sequent ['ext] { 'H >- "all"{x. 'A['x]} }

(*
 * Elimination.
 *
 * H, x: all{x. A[x]}, J[x] >- T[x]
 * by all_elim z
 * H, x: all{x. A[x]}, J[x] >- member{z; set}
 * H, x: all{x. A[x]}, J[x], y: A[z] >- T[x]
 *)
axiom all_elim 'H 'J 'x 'z 'w :
   sequent ['ext] { 'H; x: "all"{y. 'A['y]}; 'J['x] >- isset{'z} } -->
   sequent ['ext] { 'H; x: "all"{y. 'A['y]}; 'J['x]; w: 'A['z] >- 'T['x] } -->
   sequent ['ext] { 'H; x: "all"{y. 'A['y]}; 'J['x] >- 'T['x] }

(*
 * Well formedness.
 *)
axiom all_wf 'H 'y :
   sequent ['ext] { 'H; y: set >- wf{'A['y]} } -->
   sequent ['ext] { 'H >- wf{."all"{x. 'A['x]} } }

(*
 * Simple quantification is restricted.
 *)
axiom all_res 'H 'y :
   sequent ['ext] { 'H; y: set >- restricted{'A['x]} } -->
   sequent ['ext] { 'H >- restricted{."all"{x. 'A['x]}} }

val d_allT : int -> tactic

(*
 * $Log$
 * Revision 1.2  1998/07/02 18:36:57  jyh
 * Refiner modules now raise RefineError exceptions directly.
 * Modules in this revision have two versions: one that raises
 * verbose exceptions, and another that uses a generic exception.
 *
 * Revision 1.1  1998/06/23 22:12:20  jyh
 * Improved rewriter speed with conversion tree and flist.
 *
 *)
