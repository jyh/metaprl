(*
 * Primitiva axiomatization of implication.
 *)

include Czf_itt_wf

open Conversionals

declare "and"{'A; 'B}
declare pair{'a; 'b}

rewrite unfold_and : "and"{'A; 'B} <--> prod{'A; 'B}
rewrite unfold_pair : pair{'a; 'b} <--> Itt_dprod!pair{'a; 'b}

val fold_and : conv
val fold_pair : conv

(*
 * Intro.
 *
 * H >- A /\ B
 * by or_intro
 * H >- A
 * H >- B
 *)
axiom and_intro 'H :
   sequent ['ext] { 'H >- 'A } -->
   sequent ['ext] { 'H >- 'B } -->
   sequent ['ext] { 'H >- "and"{'A; 'B} }

(*
 * Elimination.
 *
 * H, x: A /\ B, J[x] >- T[x]
 * by and_elim i
 * H, x: A /\ B, y: A; z:B; J[<y, z>] >- T[<y, z>]
 *)
axiom and_elim 'H 'J 'x 'y 'z :
   sequent ['ext] { 'H;
                    x: "and"{'A; 'B};
                    y: 'A; z: 'B;
                    'J[pair{'y; 'z}]
                    >- 'T[pair{'y; 'z}]
   } -->
   sequent ['ext] { 'H; x: "and"{'A; 'B}; 'J['x] >- 'T['x] }

(*
 * Well formedness.
 *)
axiom and_wf 'H :
   sequent ['ext] { 'H >- wf{'A} } -->
   sequent ['ext] { 'H >- wf{'B} } -->
   sequent ['ext] { 'H >- wf{."and"{'A; 'B}} }

(*
 * Implication is restricted.
 *)
axiom and_res 'H :
   sequent ['ext] { 'H >- restricted{'A} } -->
   sequent ['ext] { 'H >- restricted{'B} } -->
   sequent ['ext] { 'H >- restricted{."and"{'A; 'B}} }

(*
 * $Log$
 * Revision 1.1  1998/06/23 22:12:20  jyh
 * Improved rewriter speed with conversion tree and flist.
 *
 *)
