(*
 * Testing.
 *)

open Printf
open Nl_debug

open Refiner.Refiner.Term
open Refiner.Refiner.TermAddr
open Refiner.Refiner.Refine

open Tacticals
open Conversionals

open Typeinf
open Base_dtactic
open Base_auto_tactic
open Itt_rfun
open Itt_fun
open Itt_int
open Itt_logic
open Itt_dprod
open Itt_union
open Itt_equal
open Itt_struct
open Itt_w
open Itt_derive

open Tptp
open Tptp_prove

open Nl

(*
 * Proof saving.
 *)
let zT, z =
   let pf = ref None in
   let zT p =
      pf := Some p;
      idT p
   in
   let z () =
      match !pf with
         Some p ->
            p
       | None ->
            raise Not_found
   in
      zT, z

let _ = load "tptp_prove"
let _ = cd "tptp_prove"
let _ = set_writeable ()
let _ = create_tptp "GEN"
let _ = cd "GEN"
(*
let _ = create_tptp "ALG001-1"
let _ = cd "ALG001-1"
*)

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
