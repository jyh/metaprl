(*
 * Conjunction.
 *)

include Fol_type

open Mp_resource
open Refiner.Refiner.RefineError

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "and"{'A; 'B}
declare "pair"{'a; 'b}
declare spread{'x; a, b. 'body['a; 'b]}

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_and

dform and_df : parens :: "prec"["prec_and"] :: "and"{'A; 'B} =
   szone pushm[0] slot{'A} hspace wedge `" " slot{'B} popm ezone

dform pair_df : "pair"{'a; 'b} =
   `"<" slot{'a} `"," slot{'b} `">"

dform spread_df : "spread"{'x; a, b. 'body} =
   szone pushm[0] `"let <" slot{'a} `"," slot{'b} `"> ="
   hspace slot{'x} hspace `"in" hspace slot{'body} popm ezone

(************************************************************************
 * COMPUTATION                                                          *
 ************************************************************************)

prim_rw reduce_spread : spread{pair{'x; 'y}; a, b. 'body['a; 'b]} <--> 'body['x; 'y]

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

prim and_type 'H :
   sequent ['ext] { 'H >- "type"{'A} } -->
   sequent ['ext] { 'H >- "type"{'B} } -->
   sequent ['ext] { 'H >- "type"{.'A & 'B} } = trivial

prim and_intro 'H :
   ('a : sequent ['ext] { 'H >- 'A }) -->
   ('b : sequent ['ext] { 'H >- 'B }) -->
   sequent ['ext] { 'H >- 'A & 'B } = pair{'a; 'b}

prim and_elim 'H 'J 'x 'y 'z :
   ('body['y; 'z] : sequent ['ext] { 'H; y: 'A; z: 'B; 'J['y, 'z] >- 'C['y, 'z] }) -->
   sequent ['ext] { 'H; x: 'A & 'B; 'J['x] >- 'C['x] } =
   spread{'x; y, z. 'body['y; 'z]}

(************************************************************************
 * AUTOMATION                                                           *
 ************************************************************************)

let d_and_type i p =
   if i = 0 then
      and_type (Sequent.hyp_count_addr p) p
   else
      raise (RefineError ("d_and_type", StringError "no elimination form"))

let and_type_term = << "type"{.'A & 'B} >>

let d_resource = Mp_resource.improve d_resource (and_type_term, d_and_type)

let d_and i p =
   if i = 0 then
      and_intro (Sequent.hyp_count_addr p) p
   else
      let y, z = Var.maybe_new_vars2 p "u" "v" in
      let x, _ = Sequent.nth_hyp p i in
      let j, k = Sequent.hyp_indices p i in
         and_elim j k x y z p

let and_term = << 'A & 'B >>

let d_resource = Mp_resource.improve d_resource (and_term, d_and)

(*
 * -*-
 * Local Variables:
 * Caml-master: "pousse"
 * End:
 * -*-
 *)
