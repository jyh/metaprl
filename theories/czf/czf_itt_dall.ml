(*
 * Primitiva interactiveatization of implication.
 *)

include Czf_itt_set

open Debug
open Printf

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
      eprintf "Loading Czf_itt_dall%t" eflush

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "all"{'T; x. 'A['x]}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

primrw unfold_dall : "all"{'s; x. 'A['x]} <-->
   set_ind{'s; a, f, g. "fun"{'a; x. 'A['f 'x]}}

interactive_rw reduce_dall : "all"{collect{'T; x. 'f['x]}; y. 'A['y]} <-->
   (t: 'T -> 'A['f['t]])

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform dall_df : mode[prl] :: parens :: "prec"[prec_lambda] :: "all"{'s; x. 'A} =
   pushm[0] forall `"'" slot{'x} " " Nuprl_font!member " " slot{'s} `"." slot{'A} popm

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Typehood.
 *)
interactive dall_type 'H 'y :
   sequent ['ext] { 'H >- isset{'s} } -->
   sequent ['ext] { 'H; y: set >- "type"{'A['y]} } -->
   sequent ['ext] { 'H >- "type"{."all"{'s; x. 'A['x]}} }

(*
 * Well formedness.
 *)
interactive dall_wf 'H 'y :
   sequent ['ext] { 'H >- isset{'T} } -->
   sequent ['ext] { 'H; y: set >- wf{'A['y]} } -->
   sequent ['ext] { 'H >- wf{."all"{'T; x. 'A['x]} } }

(*
 * Intro.
 *)
interactive dall_intro 'H 'a 'b :
   sequent ['ext] { 'H >- isset{'T} } -->
   sequent ['ext] { 'H; a: set >- wf{'A['a]} } -->
   sequent ['ext] { 'H; a: set; b: member{'a; 'T} >- 'A['a] } -->
   sequent ['ext] { 'H >- "all"{'T; x. 'A['x]} }

(*
 * Elimination.
 *)
interactive dall_elim 'H 'J 'x 'z 'w :
   sequent ['ext] { 'H; x: "all"{'T; y. 'A['y]}; 'J['x] >- member{'z; 'T} } -->
   sequent ['ext] { 'H; x: "all"{'T; y. 'A['y]}; 'J['x]; w: 'A['z] >- 'C['x] } -->
   sequent ['ext] { 'H; x: "all"{'T; y. 'A['y]}; 'J['x] >- 'C['x] }

(*
 * This is a restricted formula.
 *)
interactive dall_res 'H :
   sequent ['ext] { 'H >- isset{'s} } -->
   sequent ['ext] { 'H >- restricted{y. 'A['y]} } -->
   sequent ['ext] { 'H >- restricted{z. "all"{'s; y. 'A['y]}} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

let dall_term = << "all"{'T; x. 'A['x]} >>
let wf_dall_term = << wf{. "all"{'T; x. 'A['x]}} >>

(*
 * Propositional reasoning.
 *)
let d_dallT i p =
   if i = 0 then
      let v, w = maybe_new_vars2 p "v" "w" in
         dall_intro (hyp_count p) v w p
   else
      let x, _ = nth_hyp p i in
      let w = Var.maybe_new_vars1 p "u" in
      let z = get_with_arg p in
      let i, j = hyp_indices p i in
          dall_elim i j x z w p

let d_resource = d_resource.resource_improve d_resource (dall_term, d_dallT)

(*
 * Well-formedness.
 *)
let d_wf_dallT i p =
   if i = 0 then
      let v = maybe_new_vars1 p "v" in
         dall_wf (hyp_count p) v p
   else
      raise (RefineError ("d_wf_dallT", (StringTermError ("no elim form", wf_dall_term))))

let d_resource = d_resource.resource_improve d_resource (wf_dall_term, d_wf_dallT)

(*
 * Typehood.
 *)
let d_dall_typeT i p =
   if i = 0 then
      let v = maybe_new_vars1 p "v" in
         dall_type (hyp_count p) v p
   else
      raise (RefineError ("d_dall_typeT", StringError "no elimination form"))

let dall_type_term = << "type"{."all"{'s; x. 'A['x]}} >>

let d_resource = d_resource.resource_improve d_resource (dall_type_term, d_dall_typeT)

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
