(*
 * Universal quantifier.
 *)

include Fol_implies
include Fol_univ
include Fol_struct

open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.RefineError
open Mp_resource
open Tactic_type.Tacticals

open Base_dtactic

open Fol_type
open Fol_struct

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "all"{x. 'B['x]}

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_all

dform all_df : parens :: "prec"["prec_all"] :: "all"{x. 'B} =
   szone pushm[3] forall slot{'x} `"." hspace slot{'B} popm ezone

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

prim all_type {| intro_resource [] |} 'H 'x :
   [wf] sequent ['ext] { 'H; x: univ >- "type"{'B[prop{'x}]} } -->
   sequent ['ext] { 'H >- "type"{."all"{y. 'B['y]}} } = trivial

prim all_intro {| intro_resource [] |} 'H 'x :
   [main] ('b['x] : sequent ['ext] { 'H; x: univ >- 'B[prop{'x}] }) -->
   [wf] sequent ['ext] { 'H; x: univ >- "type"{'B[prop{'x}]} } -->
   sequent ['ext] { 'H >- "all"{y. 'B['y]} } =
   lambda{y. 'b['y]}

prim all_elim {| elim_resource [ThinOption thinT] |} 'H 'J 'x 'z 'a :
   [wf] sequent ['ext] { 'H; x: "all"{y. 'B['y]}; 'J['x] >- "type"{'a} } -->
   [main] ('b['x; 'z] : sequent ['ext] { 'H; x: "all"{y. 'B['y]}; 'J['x]; z: 'B['a] >- 'C['x] }) -->
   sequent ['ext] { 'H; x: "all"{y. 'B['y]}; 'J['x] >- 'C['x] } =
   'b['x; 'x 'a]

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
