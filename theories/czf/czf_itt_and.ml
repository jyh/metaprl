(*
 * Primitiva axiomatization of implication.
 *)

include Czf_itt_set

open Refiner.Refiner.RefineError
open Resource

open Tacticals
open Conversionals
open Sequent

open Itt_logic
open Itt_rfun

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "and"{'A; 'B}
declare pair{'a; 'b}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

primrw unfold_and : "and"{'A; 'B} <--> prod{'A; 'B}
primrw unfold_pair : pair{'a; 'b} <--> Itt_dprod!pair{'a; 'b}

let fold_and = makeFoldC << "and"{'A; 'B} >> unfold_and
let fold_pair = makeFoldC << "pair"{'a; 'b} >> unfold_pair

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform and_df : mode[prl] :: parens :: "prec"[prec_and] :: "and"{'A; 'B} =
   slot{'A} " " wedge `"' " slot{'B}

dform pair_df : pair{'a; 'b} =
   `"<" pushm[0] slot{'a} `";" " " slot{'b} popm `">'"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Intro.
 *
 * H >- A /\ B
 * by or_intro
 * H >- A
 * H >- B
 *)
prim and_intro 'H :
   ('a : sequent ['ext] { 'H >- 'A }) -->
   ('b : sequent ['ext] { 'H >- 'B }) -->
   sequent ['ext] { 'H >- "and"{'A; 'B} } =
   pair{'a; 'b}

(*
 * Elimination.
 *
 * H, x: A /\ B, J[x] >- T[x]
 * by and_elim i
 * H, x: A /\ B, y: A; z:B; J[<y, z>] >- T[<y, z>]
 *)
prim and_elim 'H 'J 'x 'y 'z :
   ('t['x; 'y; 'z] :
    sequent ['ext] { 'H;
                     x: "and"{'A; 'B};
                     y: 'A;
                     z: 'B;
                     'J[pair{'y; 'z}]
                    >- 'T[pair{'y; 'z}]
   }) -->
   sequent ['ext] { 'H; x: "and"{'A; 'B}; 'J['x] >- 'T['x] } =
   't[pair{'y; 'z}; 'y; 'z]

(*
 * Well formedness.
 *)
prim and_wf 'H :
   sequent ['ext] { 'H >- wf{'A} } -->
   sequent ['ext] { 'H >- wf{'B} } -->
   sequent ['ext] { 'H >- wf{."and"{'A; 'B}} } =
   it

(*
 * Implication is restricted.
 *)
prim and_res 'H :
   sequent ['ext] { 'H >- restricted{'A} } -->
   sequent ['ext] { 'H >- restricted{'B} } -->
   sequent ['ext] { 'H >- restricted{."and"{'A; 'B}} } =
   it

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let and_term = << "and"{'A; 'B} >>
let wf_and_term = << wf{. "and"{'A; 'B}} >>
let res_and_term = << restricted{. "and"{'A; 'B}} >>

(*
 * Propositional reasoning.
 *)
let d_andT i p =
   if i = 0 then
      and_intro (hyp_count p) p
   else
      let x, _ = nth_hyp p i in
      let y, z = Var.maybe_new_vars2 p "u" "v" in
      let i, j = hyp_indices p i in
          and_elim i j x y z p

let d_resource = d_resource.resource_improve d_resource (and_term, d_andT)

(*
 * Well-formedness.
 *)
external id : 'a * 'b -> 'a * 'b = "%identity"

let d_wf_andT i p =
   if i = 0 then
      and_wf (hyp_count p) p
   else
      raise (RefineError (id ("d_wf_andT", (StringTermError ("no elim form", wf_and_term)))))

let d_resource = d_resource.resource_improve d_resource (wf_and_term, d_wf_andT)

(*
 * Restricted.
 *)
let d_res_andT i p =
   if i = 0 then
      and_res (hyp_count p) p
   else
      raise (RefineError (id ("d_res_andT", (StringTermError ("no elim form", res_and_term)))))

let d_resource = d_resource.resource_improve d_resource (res_and_term, d_res_andT)

(*
 * $Log$
 * Revision 1.3  1998/07/02 18:36:58  jyh
 * Refiner modules now raise RefineError exceptions directly.
 * Modules in this revision have two versions: one that raises
 * verbose exceptions, and another that uses a generic exception.
 *
 * Revision 1.2  1998/07/01 04:37:20  nogin
 * Moved Refiner exceptions into a separate module RefineErrors
 *
 * Revision 1.1  1998/06/23 22:12:20  jyh
 * Improved rewriter speed with conversion tree and flist.
 *
 *)
