(*
 * Primitiva axiomatization of implication.
 *)

include Czf_itt_exists

open Conversionals

rewrite unfold_dexists : "exists"{'T; x. 'A['x]} <--> (x: set * (member{'x; 'T} * 'A['x]))

val fold_dexists : conv

(*
 * Intro.
 *
 * H >- exists x:T. A[x]
 * by dexists_intro z
 * H >- member{z; 'T}
 * H, x:T >- wf{A[x]}
 * H >- A[z]
 *)
axiom dexists_intro 'H 'z 'w :
   sequent ['ext] { 'H >- member{'z; 'T} } -->
   sequent ['ext] { 'H >- 'A['z] } -->
   sequent ['ext] { 'H; w: set >- wf{'A['w]} } -->
   sequent ['ext] { 'H >- "exists"{'T; x. 'A['x]} }

(*
 * Elimination.
 *
 * H, x: y:T. A[y], J[x] >- T[x]
 * by exists_elim
 * H, x: y:T. A[x], z: T, w: A[z], J[pair{z, w}] >- T[pair{z, w}]
 *)
axiom dexists_elim 'H 'J 'x 'z 'v 'w :
   sequent ['ext] { 'H;
                    x: "exists"{'T; y. 'A['y]};
                    z: set;
                    v: member{'z; 'T};
                    w: 'A['z];
                    'J[pair{'z; 'w}]
                    >- 'C[pair{'z; 'w}]
                  } -->
   sequent ['ext] { 'H; x: "exists"{'T; y. 'A['y]}; 'J['x] >- 'C['x] }

(*
 * Well formedness.
 *)
axiom dexists_wf 'H 'y :
   sequent ['ext] { 'H >- wf{'T} } -->
   sequent ['ext] { 'H; y: 'T >- wf{'A['y]} } -->
   sequent ['ext] { 'H >- wf{."exists"{'T; x. 'A['x]} } }

