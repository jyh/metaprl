(*
 * Primitiva axiomatization of implication.
 *)

include Czf_itt_set
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
      eprintf "Loading Czf_itt_dexists%t" eflush

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "exists"{'T; x. 'A['x]}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

primrw unfold_dexists : "exists"{'s; x. 'A['x]} <-->
   set_ind{'s; a, f, g. "prod"{'a; x. 'A['f 'x]}}

interactive_rw reduce_dexists : "exists"{collect{'T; x. 'f['x]}; y. 'A['y]} <-->
   (t: 'T * 'A['f['t]])

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform dexists_df : mode[prl] :: parens :: "prec"[prec_lambda] :: "exists"{'s; x. 'A} =
   pushm[0] Nuprl_font!"exists" slot{'x} " " Nuprl_font!member " " slot{'s} `"." slot{'A} popm

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Typehood.
 *)
interactive dexists_type 'H 'y :
   sequent ['ext] { 'H >- isset{'s} } -->
   sequent ['ext] { 'H; y: set >- "type"{'A['y]} } -->
   sequent ['ext] { 'H >- "type"{."exists"{'s; x. 'A['x]}} }


(*
 * Well formedness.
 *)
interactive dexists_wf 'H 'y :
   sequent ['ext] { 'H >- isset{'s} } -->
   sequent ['ext] { 'H; y: set >- wf{'A['y]} } -->
   sequent ['ext] { 'H >- wf{."exists"{'s; x. 'A['x]} } }

(*
 * Intro.
 *)
interactive dexists_intro 'H 'z 'w :
   sequent ['ext] { 'H >- isset{'s} } -->
   sequent ['ext] { 'H; w: set >- wf{'A['w]} } -->
   sequent ['ext] { 'H >- member{'z; 's} } -->
   sequent ['ext] { 'H >- 'A['z] } -->
   sequent ['ext] { 'H >- "exists"{'s; x. 'A['x]} }

interactive dexists_intro2 'H 'z 'w :
   sequent ['ext] { 'H; w: set >- wf{'A['w]} } -->
   sequent ['ext] { 'H >- member{'z; 's} } -->
   sequent ['ext] { 'H >- 'A['z] } -->
   sequent ['ext] { 'H >- "exists"{'s; x. 'A['x]} }

(*
 * Elimination.
 *)
interactive dexists_elim 'H 'J 'x 'z 'v 'w :
   sequent ['ext] { 'H; x: "exists"{'s; y. 'A['y]}; 'J['x] >- isset{'s} } -->
   sequent ['ext] { 'H; x: "exists"{'s; y. 'A['y]}; 'J['x]; z: set >- wf{'A['z]} } -->
   sequent ['ext] { 'H;
                    x: "exists"{'s; y. 'A['y]};
                    'J['x];
                    z: set;
                    v: member{'z; 's};
                    w: 'A['z]
                    >- 'C['x]
                  } -->
   sequent ['ext] { 'H; x: "exists"{'s; y. 'A['y]}; 'J['x] >- 'C['x] }

(*
 * This is a restricted formula.
 *)
interactive dexists_res 'H 'w :
   sequent ['ext] { 'H; w: set >- isset{'A['w]} } -->
   sequent ['ext] { 'H; w: set >- restricted{y. 'B['y; 'w]} } -->
   sequent ['ext] { 'H >- restricted{z. "exists"{'A['z]; y. 'B['y; 'z]}} }

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
         dexists_intro2 (hyp_count p) z w p
   else
      let x, _ = nth_hyp p i in
      let z, v, w = Var.maybe_new_vars3 p "u" "v" "w" in
      let i, j = hyp_indices p i in
          dexists_elim i j x z v w p

let d_resource = d_resource.resource_improve d_resource (dexists_term, d_dexistsT)

(*
 * Well-formedness.
 *)
let d_wf_dexistsT i p =
   if i = 0 then
      let v = maybe_new_vars1 p "v" in
         dexists_wf (hyp_count p) v p
   else
      raise (RefineError ("d_wf_dexistsT", (StringTermError ("no elim form", wf_dexists_term))))

let d_resource = d_resource.resource_improve d_resource (wf_dexists_term, d_wf_dexistsT)

(*
 * Typehood.
 *)
let d_dexists_typeT i p =
   if i = 0 then
      let v = maybe_new_vars1 p "v" in
         dexists_type (hyp_count p) v p
   else
      raise (RefineError ("d_desists_typeT", StringError "no elimination form"))

let dexists_type_term = << "type"{."exists"{'s; z. 'A['z]}} >>

let d_resource = d_resource.resource_improve d_resource (dexists_type_term, d_dexists_typeT)

(*
 * Restricted.
 *)
let d_dexists_resT i p =
   if i = 0 then
      let v = maybe_new_vars1 p "v" in
         dexists_res (hyp_count p) v p
   else
      raise (RefineError ("d_dexists_res", StringError "no elimination form"))

let dexists_res_term = << restricted{z. "exists"{'s; y. 'A['y; 'z]}} >>

let d_resource = d_resource.resource_improve d_resource (dexists_res_term, d_dexists_resT)

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
