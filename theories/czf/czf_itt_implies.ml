(*
 * Primitiva interactiveatization of implication.
 *)

include Czf_itt_and
include Czf_itt_sep

open Printf
open Debug

open Refiner.Refiner.RefineError
open Resource

open Tacticals
open Conversionals
open Sequent
open Var

open Itt_logic
open Itt_rfun

let _ =
   if !debug_load then
      eprintf "Loading Czf_itt_implies%t" eflush

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "implies"{'A; 'B}
declare "iff"{'A; 'B}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

primrw unfold_implies : "implies"{'A; 'B} <--> "fun"{'A; 'B}
primrw unfold_iff : "iff"{'A; 'B} <--> "and"{."implies"{'A; 'B}; ."implies"{'B; 'A}}

let fold_implies = makeFoldC << "implies"{'A; 'B} >> unfold_implies
let fold_iff = makeFoldC << "iff"{'A; 'B} >> unfold_iff

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform implies_df : mode[prl] :: parens :: "prec"[prec_implies] :: "implies"{'A; 'B} =
   pushm[0] slot{'A} " " Rightarrow `"' " slot{'B} popm

dform iff_fs : mode[prl] :: parens :: "prec"[prec_implies] :: "iff"{'A; 'B} =
   pushm[0] slot{'A} " " Leftrightarrow `"' " slot{'B} popm

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Typehood.
 *)
interactive implies_type 'H :
   sequent ['ext] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- "type"{."implies"{'A; 'B}} }

(*
 * Well formedness.
 *)
interactive implies_wf 'H :
   sequent ['ext] { 'H >- wf{'A} } -->
   sequent ['ext] { 'H >- wf{'B} } -->
   sequent ['ext] { 'H >- wf{."implies"{'A; 'B}} }

(*
 * Intro.
 *
 * H >- A => B
 * by implies_intro
 * H >- A wf
 * H, A >- B
 *)
interactive implies_intro 'H 'a :
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
interactive implies_elim 'H 'J 'x 'y :
   sequent ['ext] { 'H; x: "implies"{'A; 'B}; 'J['x] >- 'A } -->
   sequent ['ext] { 'H; x: "implies"{'A; 'B}; 'J['x]; y: 'B >- 'T['x] } -->
   sequent ['ext] { 'H; x: "implies"{'A; 'B}; 'J['x] >- 'T['x] }

(*
 * Implication is restricted.
 *)
interactive implies_res 'H :
   sequent ['ext] { 'H >- restricted{x. 'A['x]} } -->
   sequent ['ext] { 'H >- restricted{x. 'B['x]} } -->
   sequent ['ext] { 'H >- restricted{x ."implies"{'A['x]; 'B['x]}} }

(*
 * Typehood.
 *)
interactive iff_type 'H :
   sequent ['ext] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- "type"{."iff"{'A; 'B}} }

(*
 * Well formedness.
 *)
interactive iff_wf 'H :
   sequent ['ext] { 'H >- wf{'A} } -->
   sequent ['ext] { 'H >- wf{'B} } -->
   sequent ['ext] { 'H >- wf{."iff"{'A; 'B}} }

(*
 * Intro.
 *
 * H >- A => B
 * by iff_intro
 * H >- A wf
 * H, A >- B
 *)
interactive iff_intro 'H :
   sequent ['ext] { 'H >- "implies"{'A; 'B} } -->
   sequent ['ext] { 'H >- "implies"{'B; 'A} } -->
   sequent ['ext] { 'H >- "iff"{'A; 'B} }

(*
 * Elimination.
 *
 * H, x: A => B, J[x] >- T[x]
 * by iff_elim i
 * H, x: A => B, J[x] >- A
 * H, x: A => B, J[x], y: B -> T[x]
 *)
interactive iff_elim 'H 'J 'x 'y 'z :
   sequent ['ext] { 'H; y: "implies"{'A; 'B}; z: "implies"{'B; 'A}; 'J["pair"{'y; 'z}] >- 'T["pair"{'y; 'z}] } -->
   sequent ['ext] { 'H; x: "iff"{'A; 'B}; 'J['x] >- 'T['x] }

(*
 * Implication is restricted.
 *)
interactive iff_res 'H :
   sequent ['ext] { 'H >- restricted{x. 'A['x]} } -->
   sequent ['ext] { 'H >- restricted{x. 'B['x]} } -->
   sequent ['ext] { 'H >- restricted{x ."iff"{'A['x]; 'B['x]}} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Propositional reasoning.
 *)
let d_impliesT i p =
   if i = 0 then
      let v = maybe_new_vars1 p "v" in
         implies_intro (hyp_count p) v p
   else
      let x, _ = nth_hyp p i in
      let y = Var.maybe_new_vars1 p "u" in
      let i, j = hyp_indices p i in
          implies_elim i j x y p

let implies_term = << "implies"{'A; 'B} >>

let d_resource = d_resource.resource_improve d_resource (implies_term, d_impliesT)

(*
 * Well-formedness.
 *)
let d_wf_impliesT i p =
   if i = 0 then
      implies_wf (hyp_count p) p
   else
      raise (RefineError ("d_wf_impliesT", (StringError "no elim form")))

let wf_implies_term = << wf{. "implies"{'A; 'B}} >>

let d_resource = d_resource.resource_improve d_resource (wf_implies_term, d_wf_impliesT)

(*
 * Restricted.
 *)
let d_res_impliesT i p =
   if i = 0 then
      implies_res (hyp_count p) p
   else
      raise (RefineError ("d_res_impliesT", (StringError "no elim form")))

let res_implies_term = << restricted{x. "implies"{'A['x]; 'B['x]}} >>

let d_resource = d_resource.resource_improve d_resource (res_implies_term, d_res_impliesT)

(*
 * Typehood.
 *)
let d_type_impliesT i p =
   if i = 0 then
      implies_type (hyp_count p) p
   else
      raise (RefineError ("d_type_impliesT", (StringError "no elim form")))

let type_implies_term = << "type"{. "implies"{'A; 'B}} >>

let d_resource = d_resource.resource_improve d_resource (type_implies_term, d_type_impliesT)

(*
 * Propositional reasoning.
 *)
let d_iffT i p =
   if i = 0 then
      iff_intro (hyp_count p) p
   else
      let x, _ = nth_hyp p i in
      let y, z = Var.maybe_new_vars2 p "u" "v" in
      let i, j = hyp_indices p i in
          iff_elim i j x y z p

let iff_term = << "iff"{'A; 'B} >>

let d_resource = d_resource.resource_improve d_resource (iff_term, d_iffT)

(*
 * Well-formedness.
 *)
let d_wf_iffT i p =
   if i = 0 then
      iff_wf (hyp_count p) p
   else
      raise (RefineError ("d_wf_iffT", (StringError "no elim form")))

let wf_iff_term = << wf{. "iff"{'A; 'B}} >>

let d_resource = d_resource.resource_improve d_resource (wf_iff_term, d_wf_iffT)

(*
 * Restricted.
 *)
let d_res_iffT i p =
   if i = 0 then
      iff_res (hyp_count p) p
   else
      raise (RefineError ("d_res_iffT", (StringError "no elim form")))

let res_iff_term = << restricted{. "iff"{'A; 'B}} >>

let d_resource = d_resource.resource_improve d_resource (res_iff_term, d_res_iffT)

(*
 * Typehood.
 *)
let d_type_iffT i p =
   if i = 0 then
      iff_type (hyp_count p) p
   else
      raise (RefineError ("d_type_iffT", (StringError "no elim form")))

let type_iff_term = << "type"{. "iff"{'A; 'B}} >>

let d_resource = d_resource.resource_improve d_resource (type_iff_term, d_type_iffT)

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
