(*
 * Primitiva axiomatization of implication.
 *)

include Czf_itt_exists

open Refiner.Refiner.RefineError
open Resource

open Tacticals
open Conversionals
open Sequent
open Var

open Itt_logic
open Itt_rfun

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

primrw unfold_dexists : "exists"{'T; x. 'A['x]} <-->
                           (x: (x:set * member{'x; 'T}) * 'A[fst{'x}])

let fold_dexists = makeFoldC << "exists"{'T; x. 'A['x]} >> unfold_dexists

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform dexists_df : mode[prl] :: parens :: "prec"[prec_lambda] :: "exists"{'T; x. 'A} =
   pushm[0] Nuprl_font!"exists" `"'" slot{'x} `":" slot{'T} `"." slot{'A} popm

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Intro.
 *
 * H >- exists x:T. A[x]
 * by dexists_intro z
 * H >- member{z; 'T}
 * H, x:T >- wf{A[x]}
 * H >- A[z]
 *)
prim dexists_intro 'H 'z 'w :
   sequent ['ext] { 'H >- member{'z; 'T} } -->
   sequent ['ext] { 'H >- 'A['z] } -->
   sequent ['ext] { 'H; w: set >- wf{'A['w]} } -->
   sequent ['ext] { 'H >- "exists"{'T; x. 'A['x]} } =
   it

(*
 * Elimination.
 *
 * H, x: y:T. A[y], J[x] >- T[x]
 * by exists_elim
 * H, x: y:T. A[x], z: T, w: A[z], J[pair{z, w}] >- T[pair{z, w}]
 *)
prim dexists_elim 'H 'J 'x 'z 'v 'w :
   sequent ['ext] { 'H;
                    x: "exists"{'T; y. 'A['y]};
                    z: 'T;
                    v: member{'z; 'T};
                    w: 'A['z];
                    'J[pair{'z; 'w}]
                    >- 'C[pair{'z; 'w}]
                  } -->
   sequent ['ext] { 'H; x: "exists"{'T; y. 'A['y]}; 'J['x] >- 'C['x] } =
   it

(*
 * Well formedness.
 *)
prim dexists_wf 'H 'y :
   sequent ['ext] { 'H >- wf{'T} } -->
   sequent ['ext] { 'H; y: 'T >- wf{'A['y]} } -->
   sequent ['ext] { 'H >- wf{."exists"{'T; x. 'A['x]} } } =
   it

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let dexists_term = << "exists"{'T; x. 'A['x]} >>
let wf_dexists_term = << wf{. "exists"{'T; x. 'A['x]}} >>

(*
 * Propositional reasoning.
 *)
let d_dexistsT i p =
   if i = 0 then
      let z = get_with_arg p in
      let w = maybe_new_vars1 p "v" in
         dexists_intro (hyp_count p) z w p
   else
      let x, _ = nth_hyp p i in
      let z, v, w = Var.maybe_new_vars3 p "u" "v" "w" in
      let i, j = hyp_indices p i in
          dexists_elim i j x z v w p

let d_resource = d_resource.resource_improve d_resource (dexists_term, d_dexistsT)

(*
 * Well-formedness.
 *)
external id : 'a * 'b -> 'a * 'b = "%identity"

let d_wf_dexistsT i p =
   if i = 0 then
      let v = maybe_new_vars1 p "v" in
         dexists_wf (hyp_count p) v p
   else
      raise (RefineError (id ("d_wf_dexistsT", (StringTermError ("no elim form", wf_dexists_term)))))

let d_resource = d_resource.resource_improve d_resource (wf_dexists_term, d_wf_dexistsT)

(*
 * $Log$
 * Revision 1.3  1998/07/02 18:37:03  jyh
 * Refiner modules now raise RefineError exceptions directly.
 * Modules in this revision have two versions: one that raises
 * verbose exceptions, and another that uses a generic exception.
 *
 * Revision 1.2  1998/07/01 04:37:22  nogin
 * Moved Refiner exceptions into a separate module RefineErrors
 *
 * Revision 1.1  1998/06/23 22:12:21  jyh
 * Improved rewriter speed with conversion tree and flist.
 *
 *)
