(*
 * Universal quantifier.
 *)

include Fol_implies
include Fol_univ

open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.RefineError
open Nl_resource
open Tacticals

open Fol_type

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

prim all_type 'H 'x :
   sequent ['ext] { 'H; x: univ >- "type"{'B['x]} } -->
   sequent ['ext] { 'H >- "type"{."all"{y. 'B['y]}} } = trivial

prim all_intro 'H 'x :
   ('b['x] : sequent ['ext] { 'H; x: univ >- 'B['x] }) -->
   sequent ['ext] { 'H >- "all"{y. 'B['y]} } =
   lambda{y. 'b['y]}

prim all_elim 'H 'J 'x 'z 'a :
   sequent ['ext] { 'H; x: "all"{y. 'B['y]}; 'J['x] >- "type"{'a} } -->
   ('b['x; 'z] : sequent ['ext] { 'H; x: "all"{y. 'B['y]}; 'J['x]; z: 'B['a] >- 'C['x] }) -->
   sequent ['ext] { 'H; x: "all"{y. 'B['y]}; 'J['x] >- 'C['x] } =
   'b['x; 'x 'a]

(************************************************************************
 * AUTOMATION                                                           *
 ************************************************************************)

let all_term = << "all"{y. 'B['y]} >>

let all_opname = opname_of_term all_term
let is_all_term = is_dep1_term all_opname
let dest_all = dest_dep1_term all_opname

let d_all_type i p =
   if i = 0 then
      let t = dest_type (Sequent.concl p) in
      let v, _ = dest_all t in
      let v = Var.maybe_new_vars1 p v in
         all_type (Sequent.hyp_count_addr p) v p
   else
      raise (RefineError ("d_all_type", StringError "no elimination form"))

let all_type_term = << "type"{."all"{x. 'B['x]}} >>

let d_resource = d_resource.resource_improve d_resource (all_type_term, d_all_type)

let d_all i p =
   if i = 0 then
      let goal = Sequent.concl p in
      let v, _ = dest_all goal in
      let v = Var.maybe_new_vars1 p v in
         all_intro (Sequent.hyp_count_addr p) v p
   else
      let x, a = Sequent.nth_hyp p i in
      let v, _ = dest_all a in
      let v = Var.maybe_new_vars1 p v in
      let y = get_with_arg p in
      let j, k = Sequent.hyp_indices p i in
         all_elim j k x v y p

let d_resource = d_resource.resource_improve d_resource (all_term, d_all)

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
