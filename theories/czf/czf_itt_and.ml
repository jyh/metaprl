(*
 * Primitiva axiomatization of implication.
 *)

include Czf_itt_set

open Printf
open Debug

open Refiner.Refiner.RefineError
open Resource

open Tacticals
open Conversionals
open Sequent

open Itt_logic
open Itt_rfun
open Itt_dprod

let _ =
   if !debug_load then
      eprintf "Loading Czf_itt_and%t" eflush

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "and"{'A; 'B}
declare pair{'a; 'b}
declare spread{'z; x, y. 'b['x; 'y]}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

primrw unfold_and : "and"{'A; 'B} <--> 'A * 'B
primrw unfold_pair : pair{'a; 'b} <--> Itt_dprod!pair{'a; 'b}
primrw unfold_spread : spread{'z; x, y. 'b['x; 'y]} <-->
   Itt_dprod!spread{'z; x, y. 'b['x; 'y]}

let fold_and = makeFoldC << "and"{'A; 'B} >> unfold_and
let fold_pair = makeFoldC << "pair"{'a; 'b} >> unfold_pair
let fold_spread = makeFoldC << spread{'z; x, y. 'b['x; 'y]} >> unfold_spread

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform and_df : mode[prl] :: parens :: "prec"[prec_and] :: "and"{'A; 'B} =
   slot{'A} " " wedge `"' " slot{'B}

dform pair_df : pair{'a; 'b} =
   `"<" pushm[0] slot{'a} `";" " " slot{'b} popm `">'"

(*
dform spread_df : parens :: "prec"[prec_spread] :: mode[prl] :: spread{'e; u, v. 'b} =
   `"let " pair{'u; 'v} `" = " slot{'e} `" in " slot{'b}
*)

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Typehood.
 *)
interactive and_type 'H :
   sequent ['ext] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- "type"{."and"{'A; 'B}} }

(*
 * Well formedness.
 *)
interactive and_wf 'H :
   sequent ['ext] { 'H >- wf{'A} } -->
   sequent ['ext] { 'H >- wf{'B} } -->
   sequent ['ext] { 'H >- wf{."and"{'A; 'B}} }

(*
 * Intro.
 *
 * H >- A /\ B
 * by or_intro
 * H >- A
 * H >- B
 *)
interactive and_intro 'H :
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
interactive and_elim 'H 'J 'x 'y 'z :
   sequent ['ext] { 'H;
                     y: 'A;
                     z: 'B;
                     'J[pair{'y; 'z}]
                    >- 'T[pair{'y; 'z}]
   } -->
   sequent ['ext] { 'H; x: "and"{'A; 'B}; 'J['x] >- 'T['x] }

(*
 * Implication is restricted.
 *)
interactive and_res 'H :
   sequent ['ext] { 'H >- restricted{x. 'A['x]} } -->
   sequent ['ext] { 'H >- restricted{x. 'B['x]} } -->
   sequent ['ext] { 'H >- restricted{x. "and"{'A['x]; 'B['x]}} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let and_term = << "and"{'A; 'B} >>
let wf_and_term = << wf{. "and"{'A; 'B}} >>
let res_and_term = << restricted{x. "and"{'A['x]; 'B['x]}} >>

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
let d_wf_andT i p =
   if i = 0 then
      and_wf (hyp_count p) p
   else
      raise (RefineError ("d_wf_andT", (StringTermError ("no elim form", wf_and_term))))

let d_resource = d_resource.resource_improve d_resource (wf_and_term, d_wf_andT)

(*
 * Typehood.
 *)
let d_type_andT i p =
   if i = 0 then
      and_type (hyp_count p) p
   else
      raise (RefineError ("d_type_andT", StringError "no elim form"))

let type_and_term = << "type"{."and"{'A; 'B}} >>

let d_resource = d_resource.resource_improve d_resource (type_and_term, d_type_andT)


(*
 * Restricted.
 *)
let d_res_andT i p =
   if i = 0 then
      and_res (hyp_count p) p
   else
      raise (RefineError ("d_res_andT", (StringTermError ("no elim form", res_and_term))))

let d_resource = d_resource.resource_improve d_resource (res_and_term, d_res_andT)

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
