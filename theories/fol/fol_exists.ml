(*
 * Existential quantifier.
 *)

include Fol_and
include Fol_univ

open Refiner.Refiner.RefineError
open Mp_resource
open Tacticals

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "exists"{x. 'B['x]}

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_exists

dform exists_df : parens :: "prec"["prec_exists"] :: "exists"{x. 'B} =
   szone pushm[3] Nuprl_font!"exists" slot{'x} `"." hspace slot{'B} popm ezone

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

prim exists_type 'H 'x :
   sequent ['ext] { 'H; x: univ >- "type"{'B[prop{'x}]} } -->
   sequent ['ext] { 'H >- "type"{."exists"{y. 'B['y]}} } = trivial


prim exists_intro 'H 'a :
   sequent ['ext] { 'H >- "type"{'a} } -->
   ('b : sequent ['ext] { 'H >- 'B['a] }) -->
   sequent ['ext] { 'H >- "exists"{y. 'B['y]} } =
   pair{'a; 'b}

prim exists_elim 'H 'J 'x 'y 'z :
   ('b['y; 'z] : sequent ['ext] { 'H; y: univ; z: 'B[prop{'y}]; 'J['y, 'z] >- 'C['y, 'z] }) -->
   sequent ['ext] { 'H; x: "exists"{w. 'B['w]}; 'J['x] >- 'C['x] } =
   spread{'x; y, z. 'b['y; 'z]}

(************************************************************************
 * AUTOMATION                                                           *
 ************************************************************************)

let d_exists_type i p =
   if i = 0 then
      let v = Var.maybe_new_vars1 p "v" in
         exists_type (Sequent.hyp_count_addr p) v p
   else
      raise (RefineError ("d_exists_type", StringError "no elimination form"))

let exists_type_term = << "type"{."exists"{x. 'B['x]}} >>

let d_resource = d_resource.resource_improve d_resource (exists_type_term, d_exists_type)

let d_exists i p =
   if i = 0 then
      let a = get_with_arg p in
         exists_intro (Sequent.hyp_count_addr p) a p
   else
      let x, _ = Sequent.nth_hyp p i in
      let y, z = Var.maybe_new_vars2 p "u" "v" in
      let j, k = Sequent.hyp_indices p i in
         exists_elim j k x y z p

let exists_term = << "exists"{x. 'B['x]} >>

let d_resource = d_resource.resource_improve d_resource (exists_term, d_exists)

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
