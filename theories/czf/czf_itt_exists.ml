(*
 * Primitiva axiomatization of implication.
 *)

include Czf_itt_and

open Refiner.Refiner.RefineErrors
open Resource

open Tacticals
open Conversionals
open Sequent
open Var

open Itt_logic
open Itt_rfun

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "exists"{x. 'A['x]}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

primrw unfold_exists : "exists"{x. 'A['x]} <--> prod{set; x. 'A['x]}

let fold_exists = makeFoldC << "exists"{x. 'A['x]} >> unfold_exists

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform exists_df : mode[prl] :: parens :: "prec"[prec_lambda] :: "exists"{x. 'A} =
   pushm[0] Nuprl_font!"exists" `"'" slot{'x} `"." slot{'A} popm

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Intro.
 *
 * H >- exists x. A[x]
 * by exists_intro z
 * H >- member{z; set}
 * H >- A[z]
 *)
prim exists_intro 'H 'z 'w :
   sequent ['ext] { 'H >- member{'z; set} } -->
   sequent ['ext] { 'H >- 'A['z] } -->
   sequent ['ext] { 'H; w: set >- wf{'A['w]} } -->
   sequent ['ext] { 'H >- "exists"{x. 'A['x]} } =
   it

(*
 * Elimination.
 *
 * H, x: exists{y. A[y]}, J[x] >- T[x]
 * by exists_elim
 * H, x: exists{x. A[x]}, z: set, w: A[z], J[pair{z, w}] >- T[pair{z, w}]
 *)
prim exists_elim 'H 'J 'x 'z 'w :
   sequent ['ext] { 'H;
                    x: "exists"{y. 'A['y]};
                    z: set;
                    w: 'A['z];
                    'J[pair{'z; 'w}]
                    >- 'T[pair{'z; 'w}]
                  } -->
   sequent ['ext] { 'H; x: "exists"{y. 'A['y]}; 'J['x] >- 'T['x] } =
   it

(*
 * Well formedness.
 *)
prim exists_wf 'H 'y :
   sequent ['ext] { 'H; y: set >- wf{'A['y]} } -->
   sequent ['ext] { 'H >- wf{."exists"{x. 'A['x]} } } =
   it

(*
 * Simple quantification is restricted.
 *)
prim exists_res 'H 'y :
   sequent ['ext] { 'H; y: set >- restricted{'A['x]} } -->
   sequent ['ext] { 'H >- restricted{."exists"{x. 'A['x]}} } =
   it

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let exists_term = << "exists"{'A; 'B} >>
let wf_exists_term = << wf{. "exists"{'A; 'B}} >>
let res_exists_term = << restricted{. "exists"{'A; 'B}} >>

(*
 * Propositional reasoning.
 *)
let d_existsT i p =
   if i = 0 then
      let z = get_with_arg p in
      let w = maybe_new_vars1 p "v" in
         exists_intro (hyp_count p) z w p
   else
      let x, _ = nth_hyp p i in
      let z, w = Var.maybe_new_vars2 p "u" "v" in
      let i, j = hyp_indices p i in
          exists_elim i j x z w p

let d_resource = d_resource.resource_improve d_resource (exists_term, d_existsT)

(*
 * Well-formedness.
 *)
external id : 'a * 'b -> 'a * 'b = "%identity"

let d_wf_existsT i p =
   if i = 0 then
      let v = maybe_new_vars1 p "v" in
         exists_wf (hyp_count p) v p
   else
      raise (RefineError (id ("d_wf_existsT", (StringTermError ("no elim form", wf_exists_term)))))

let d_resource = d_resource.resource_improve d_resource (wf_exists_term, d_wf_existsT)

(*
 * Restricted.
 *)
let d_res_existsT i p =
   if i = 0 then
      let v = maybe_new_vars1 p "v" in
         exists_res (hyp_count p) v p
   else
      raise (RefineError (id ("d_res_existsT", (StringTermError ("no elim form", res_exists_term)))))

let d_resource = d_resource.resource_improve d_resource (res_exists_term, d_res_existsT)

(*
 * $Log$
 * Revision 1.2  1998/07/01 04:37:23  nogin
 * Moved Refiner exceptions into a separate module RefineErrors
 *
 * Revision 1.1  1998/06/23 22:12:21  jyh
 * Improved rewriter speed with conversion tree and flist.
 *
 *)
