(*
 * Primitiva interactiveatization of implication.
 *)

include Czf_itt_sep

open Printf
open Debug

open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.RefineError
open Resource

open Tacticals
open Conversionals
open Sequent
open Var

open Base_auto_tactic
open Base_dtactic

open Itt_equal
open Itt_logic
open Itt_rfun
open Itt_derive
open Itt_dprod

let _ =
   if !debug_load then
      eprintf "Loading Czf_itt_and%t" eflush

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Implication is restricted.
 *)
interactive dfun_fun2 'H 'u 'v 'z :
   sequent ['ext] { 'H; u: set >- "type"{'A['u]} } -->
   sequent ['ext] { 'H; u: set; z: 'A['u] >- "type"{'B['u; 'z]} } -->
   sequent ['ext] { 'H >- fun_prop{z. 'A['z]} } -->
   sequent ['ext] { 'H; u: set; v: 'A['u] >- fun_prop{z. 'B['z; 'v]} } -->
   sequent ['ext] { 'H; u: set >- fun_prop{z. 'A['z]; w. 'B['u; 'w]} } -->
   sequent ['ext] { 'H >- fun_prop{z. "fun"{'A['z]; w. 'B['z; 'w]}} }

interactive dfun_res2 'H 'u 'v 'z :
   sequent ['ext] { 'H; u: set >- "type"{'A['u]} } -->
   sequent ['ext] { 'H; u: set; v: set; z: 'A['v] >- "type"{'B['u; 'z]} } -->
   sequent ['ext] { 'H >- restricted{z. 'A['z]} } -->
   sequent ['ext] { 'H; u: set; v: 'A['u] >- restricted{z. 'B['z; 'v]} } -->
   sequent ['ext] { 'H; u: set >- fun_prop{z. 'A['z]; w. 'B['u; 'w]} } -->
   sequent ['ext] { 'H >- restricted{z. "fun"{'A['z]; w. 'B['z; 'w]}} }

(*
(*
 * Implication is restricted.
 *)
interactive prod_fun 'H 'w :
   sequent ['ext] { 'H; w: set >- "type"{'A['w]} } -->
   sequent ['ext] { 'H; w: set >- "type"{'B['w]} } -->
   sequent ['ext] { 'H >- fun_prop{x. 'A['x]} } -->
   sequent ['ext] { 'H >- fun_prop{x. 'B['x]} } -->
   sequent ['ext] { 'H >- fun_prop{x. "prod"{'A['x]; 'B['x]}} }

(*
 * Implication is restricted.
 *)
interactive prod_res 'H 'w :
   sequent ['ext] { 'H; w: set >- "type"{'A['w]} } -->
   sequent ['ext] { 'H; w: set >- "type"{'B['w]} } -->
   sequent ['ext] { 'H >- restricted{x. 'A['x]} } -->
   sequent ['ext] { 'H >- restricted{x. 'B['x]} } -->
   sequent ['ext] { 'H >- restricted{x. "prod"{'A['x]; 'B['x]}} }

(*
 * Implication is restricted.
 *)
interactive and_fun 'H 'w :
   sequent ['ext] { 'H; w: set >- "type"{'A['w]} } -->
   sequent ['ext] { 'H; w: set >- "type"{'B['w]} } -->
   sequent ['ext] { 'H >- fun_prop{x. 'A['x]} } -->
   sequent ['ext] { 'H >- fun_prop{x. 'B['x]} } -->
   sequent ['ext] { 'H >- fun_prop{x. "and"{'A['x]; 'B['x]}} }

(*
 * Implication is restricted.
 *)
interactive and_res 'H 'w :
   sequent ['ext] { 'H; w: set >- "type"{'A['w]} } -->
   sequent ['ext] { 'H; w: set >- "type"{'B['w]} } -->
   sequent ['ext] { 'H >- restricted{x. 'A['x]} } -->
   sequent ['ext] { 'H >- restricted{x. 'B['x]} } -->
   sequent ['ext] { 'H >- restricted{x. "and"{'A['x]; 'B['x]}} }
*)

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * In dfun_res, the bckThruAssumT is not smart enough.
 * This tactic is a hack meant to work in this specifi proof.
 *)
let type2T p =
   let z =
      try get_term_arg p "type2T" with
         RefineError _ ->
            << 'z >>
   in
   let { sequent_hyps = hyps; sequent_goals = goals } = Sequent.explode_sequent p in
   let goal = dest_type_term (List.hd goals) in
   let v, subterms = dest_so_var goal in
      match subterms with
         [x; y] ->
            (assumT 2 thenMT instHypT [x; z; y] (-1)) p
       | _ ->
            raise (RefineError ("type2T", StringError "sequent has the wrong format"))

(*
 * Also decompose iffs in the hyps.
 *)
let d_iffT i p =
   let _, hyp = Sequent.nth_hyp p i in
      if is_iff_term hyp then
         dT i p
      else
         raise (RefineError ("d_iffT", StringError "not an iff"))

(*
 * Our auto tactic needs to chain trhough aplications and fst.
 *)
let allAutoT =
   repeatT (firstT [progressT autoT;
                    autoApplyT 0;
                    progressT (rwh reduceFst 0);
                    onSomeHypT d_iffT;
                    type2T;
                    idT])

(*
 * Restricted.
 *)
let d_dfun_funT i p =
   if i = 0 then
      let u, v, z = maybe_new_vars3 p "u" "v" "z" in
         dfun_fun2 (hyp_count p) u v z p
   else
      raise (RefineError ("d_dfun_funT", StringError "no elimination fandm"))

let dfun_fun_term = << fun_prop{z. "fun"{'P1['z]; w. 'P2['z; 'w]}} >>

let d_resource = d_resource.resource_improve d_resource (dfun_fun_term, d_dfun_funT)

(*
 * Restricted.
 *)
let d_dfun_resT i p =
   if i = 0 then
      let u, v, z = maybe_new_vars3 p "u" "v" "z" in
         dfun_res2 (hyp_count p) u v z p
   else
      raise (RefineError ("d_dfun_resT", StringError "no elimination fandm"))

let dfun_res_term = << restricted{z. "fun"{'P1['z]; w. 'P2['z; 'w]}} >>

let d_resource = d_resource.resource_improve d_resource (dfun_res_term, d_dfun_resT)

(*
(*
 * Restricted.
 *)
let d_all_funT i p =
   if i = 0 then
      let z = maybe_new_vars1 p "z" in
         all_fun (hyp_count p) z p
   else
      raise (RefineError ("d_all_funT", StringError "no elimination fallm"))

let all_fun_term = << fun_prop{z. "all"{'P1['z]; 'P2['z]}} >>

let d_resource = d_resource.resource_improve d_resource (all_fun_term, d_all_funT)

(*
 * Restricted.
 *)
let d_all_resT i p =
   if i = 0 then
      let z = maybe_new_vars1 p "z" in
         all_res (hyp_count p) z p
   else
      raise (RefineError ("d_all_resT", StringError "no elimination fallm"))

let all_res_term = << restricted{z. "all"{'P1['z]; 'P2['z]}} >>

let d_resource = d_resource.resource_improve d_resource (all_res_term, d_all_resT)
*)

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
