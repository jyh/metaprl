(*
 * Implication.
 *)

include Fol_type

open Mp_resource
open Refiner.Refiner.RefineError

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare implies{'A; 'B}
declare lambda{x. 'b['x]}
declare apply{'f; 'a}

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_implies
prec prec_lambda
prec prec_apply

prec prec_lambda < prec_apply
prec prec_lambda < prec_implies
prec prec_implies < prec_apply

dform implies_df : parens :: "prec"["prec_implies"] :: implies{'A; 'B} =
   szone pushm[0] slot["le"]{'A} hspace Rightarrow `" " slot{'B} popm ezone

dform lambda_df : parens :: "prec"["prec_lambda"] :: lambda{x. 'b} =
   szone pushm[3] Nuprl_font!lambda slot{'x} `"." slot{'b} popm ezone

dform apply_df : parens :: "prec"["prec_apply"] :: apply{'f; 'a} =
   slot{'f} hspace slot{'a}

(************************************************************************
 * COMPUTATION                                                          *
 ************************************************************************)

primrw beta : (lambda{x. 'b['x]} 'a) <--> 'b['a]

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

prim implies_type 'H :
   sequent ['ext] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- "type"{implies{'A; 'B}} } = trivial

prim implies_intro 'H 'x :
   sequent ['ext] { 'H >- "type"{'A} } -->
   ('b['x] : sequent ['ext] { 'H; x: 'A >- 'B }) -->
   sequent ['ext] { 'H >- 'A => 'B } = lambda{x. 'b['x]}

prim implies_elim 'H 'J 'f 'b :
   ('a : sequent ['ext] { 'H; f: 'A => 'B; 'J['f] >- 'A }) -->
   ('t['f; 'b] : sequent ['ext] { 'H; f: 'A => 'B; 'J['f]; b: 'B >- 'C['f] }) -->
   sequent ['ext] { 'H; f: 'A => 'B; 'J['f] >- 'C['f] } = 't['f; 'f 'a]

(************************************************************************
 * AUTOMATION                                                           *
 ************************************************************************)

let d_implies_type i p =
   if i = 0 then
      implies_type (Sequent.hyp_count_addr p) p
   else
      raise (RefineError ("d_implies_type", StringError "no elimination form"))

let implies_type_term = << "type"{implies{'A; 'B}} >>

let d_resource = Mp_resource.improve d_resource (implies_type_term, d_implies_type)

let d_implies i p =
   if i = 0 then
      let v = Var.maybe_new_vars1 p "v" in
         implies_intro (Sequent.hyp_count_addr p) v p
   else
      let v = Var.maybe_new_vars1 p "v" in
      let f, _ = Sequent.nth_hyp p i in
      let j, k = Sequent.hyp_indices p i in
         implies_elim j k f v p

let implies_term = << "implies"{'A; 'B} >>

let d_resource = Mp_resource.improve d_resource (implies_term, d_implies)

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
