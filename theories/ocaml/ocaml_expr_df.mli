(*
 * Display forms for expressions.
 *)

include Ocaml
include Ocaml_base_df

(*
 * Display flags.
 *)
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
 * $Log$
 * Revision 1.1  1998/02/18 18:47:15  jyh
 * Initial ocaml semantics.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
