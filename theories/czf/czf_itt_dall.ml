(*
 * Primitiva interactiveatization of implication.
 *)

include Czf_itt_all
include Czf_itt_set_ind

open Nl_debug
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

declare "dall"{'T; x. 'A['x]}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

primrw unfold_dall : "dall"{'s; x. 'A['x]} <-->
   set_ind{'s; a, f, g. (x: 'a -> 'A['f 'x])}

interactive_rw reduce_dall : "dall"{collect{'T; x. 'f['x]}; y. 'A['y]} <-->
   (t: 'T -> 'A['f['t]])

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform dall_df : mode[prl] :: parens :: "prec"[prec_lambda] :: "dall"{'s; x. 'A} =
   pushm[0] forall slot{'x} " " Nuprl_font!member " " slot{'s} `"." slot{'A} popm

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Typehood.
 *)
interactive dall_type 'H 'y :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent [squash] { 'H; y: set >- "type"{'A['y]} } -->
   sequent ['ext] { 'H >- "type"{."dall"{'s; x. 'A['x]}} }

(*
 * Intro.
 *)
interactive dall_intro 'H 'a 'b :
   sequent [squash] { 'H >- isset{'s} } -->
   sequent [squash] { 'H; a: set >- "type"{'A['a]} } -->
   sequent ['ext] { 'H; a: set; b: member{'a; 's} >- 'A['a] } -->
   sequent ['ext] { 'H >- "dall"{'s; x. 'A['x]} }

(*
 * Elimination.
 *)
interactive dall_elim 'H 'J 'z 'w :
   sequent [squash] { 'H; x: "dall"{'s; y. 'A['y]}; 'J['x]; w: set >- "type"{'A['w]} } -->
   sequent ['ext] { 'H; x: "dall"{'s; y. 'A['y]}; 'J['x] >- fun_prop{w. 'A['w]} } -->
   sequent ['ext] { 'H; x: "dall"{'s; y. 'A['y]}; 'J['x] >- member{'z; 's} } -->
   sequent ['ext] { 'H; x: "dall"{'s; y. 'A['y]}; 'J['x]; w: 'A['z] >- 'C['x] } -->
   sequent ['ext] { 'H; x: "dall"{'s; y. 'A['y]}; 'J['x] >- 'C['x] }

(*
 * This is a restricted formula.
 *)
interactive dall_res2 'H 'w 'x :
   sequent ['ext] { 'H; w: set; x: set >- "type"{'B['w; 'x]} } -->
   sequent ['ext] { 'H >- fun_set{w. 'A['w]} } -->
   sequent ['ext] { 'H >- restricted{z, y. 'B['z; 'y]} } -->
   sequent ['ext] { 'H >- restricted{z. "dall"{'A['z]; y. 'B['z; 'y]}} }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Propositional reasoning.
 *)
let d_dallT i p =
   if i = 0 then
      let v, w = maybe_new_vars2 p "v" "w" in
         (dall_intro (hyp_count_addr p) v w
          thenLT [addHiddenLabelT "wf";
                  addHiddenLabelT "wf";
                  addHiddenLabelT "main"]) p
   else
      let x, _ = nth_hyp p i in
      let u = Var.maybe_new_vars1 p "u" in
      let z = get_with_arg p in
      let i, j = hyp_indices p i in
         (dall_elim i j z u
          thenLT [addHiddenLabelT "wf";
                  addHiddenLabelT "wf";
                  addHiddenLabelT "antecedent";
                  addHiddenLabelT "main"]) p

let dall_term = << "dall"{'s; x. 'A['x]} >>

let d_resource = d_resource.resource_improve d_resource (dall_term, d_dallT)

(*
 * Typehood.
 *)
let d_dall_typeT i p =
   if i = 0 then
      let v = maybe_new_vars1 p "v" in
         (dall_type (hyp_count_addr p) v thenT addHiddenLabelT "wf") p
   else
      raise (RefineError ("d_dall_typeT", StringError "no elimination form"))

let dall_type_term = << "type"{."dall"{'s; x. 'A['x]}} >>

let d_resource = d_resource.resource_improve d_resource (dall_type_term, d_dall_typeT)

(*
 * Restricted.
 *)
let d_dall_resT i p =
   if i = 0 then
      let w, v = maybe_new_vars2 p "u" "v" in
         (dall_res2 (hyp_count_addr p) w v
          thenLT [addHiddenLabelT "wf";
                  addHiddenLabelT "wf";
                  addHiddenLabelT "main"]) p
   else
      raise (RefineError ("d_dall_resT", StringError "no elimination form"))

let dall_res_term = << restricted{dall{'s; x. 'A['x]}} >>

let d_resource = d_resource.resource_improve d_resource (dall_res_term, d_dall_resT)

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
