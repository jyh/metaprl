(*
 * All the parts of ITT.
 *
 *)

include Base_theory
include Itt_equal
include Itt_void
include Itt_atom
include Itt_bool
include Itt_int
include Itt_int_bool
include Itt_arith
include Itt_rfun
include Itt_dfun
include Itt_fun
include Itt_dprod
include Itt_prod
include Itt_union
include Itt_struct
include Itt_set
include Itt_isect
include Itt_subtype
include Itt_w
include Itt_prec
include Itt_srec
include Itt_quotient
include Itt_list
include Itt_derive
include Itt_prop_decide

open Itt_equal
open Itt_rfun
open Itt_logic
open Itt_w

(*
 * Combine the precedences.
 *)
prec prec_equal < prec_apply
prec prec_type = prec_apply
prec prec_and < prec_apply
prec prec_w = prec_quant
prec prec_tree_ind < prec_quant

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
