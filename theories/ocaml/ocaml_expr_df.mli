(*
 * Display forms for expressions.
 *)

include Ocaml
include Ocaml_base_df

(*
 * Display flags.
 *)
declare ident_expr
declare list_expr
declare se_list
declare ee_list

(*
 * Precedences.
 *)
prec prec_proj
prec prec_apply
prec prec_cons
prec prec_assign
prec prec_equal
prec prec_if
prec prec_rel
prec prec_not
prec prec_fun
prec prec_let

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
