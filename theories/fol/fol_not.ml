(*
 * Negation is defined in terms of implication.
 *)

include Fol_false
include Fol_implies

open Mp_resource
open Refiner.Refiner.RefineError

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "not"{'A}

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_not

dform not_df : parens :: "prec"["prec_not"] :: "not"{'A} =
   tneg slot{'A}

(************************************************************************
 * COMPUTATION                                                          *
 ************************************************************************)

primrw unfold_not : "not"{'A} <--> implies{'A; ."false"}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

interactive not_type 'H :
   sequent ['ext] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- "type"{."not"{'A}} }

interactive not_intro 'H 'x :
   sequent ['ext] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H; x: 'A >- "false" } -->
   sequent ['ext] { 'H >- "not"{'A} }

interactive not_elim 'H 'J :
   sequent ['ext] { 'H; x: "not"{'A}; 'J['x] >- 'A } -->
   sequent ['ext] { 'H; x: "not"{'A}; 'J['x] >- 'C['x] }

(************************************************************************
 * AUTOMATION                                                           *
 ************************************************************************)

let d_not_type i p =
   if i = 0 then
      not_type (Sequent.hyp_count_addr p) p
   else
      raise (RefineError ("d_not_type", StringError "no elimination form"))

let not_type_term = << "type"{."not"{'A}} >>

let d_resource = d_resource.resource_improve d_resource (not_type_term, d_not_type)

let d_not i p =
   if i = 0 then
      let x = Var.maybe_new_vars1 p "x" in
         not_intro (Sequent.hyp_count_addr p) x p
   else
      let j, k = Sequent.hyp_indices p i in
         not_elim j k p

let not_term = << "not"{'A} >>

let d_resource = d_resource.resource_improve d_resource (not_term, d_not)

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
