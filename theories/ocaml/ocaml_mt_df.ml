(*
 * Display forms for module types.
 *)

include Ocaml
include Ocaml_base_df
include Ocaml_expr_df

(*
 * Projection.
 *)
dform parens :: "prec"[prec_proj] :: mt_proj{'mt1; 'mt2} =
   slot{'mt1} "." slot{'mt2}

(*
 * Application.
 *)
dform parens :: "prec"[prec_apply] :: mt_apply{'mt1; 'mt2} =
   slot{'mt1} space slot{'mt2}

(*
 * Functor.
 *)
dform parens :: "prec"[prec_fun] :: mt_functor[$name:s]{'mt1; 'mt2} =
   "functor" space "(" slot[$name:s] space ":" space slot{'mt1} ")"
   space "->" slot{'mt2}

(*
 * Id.
 *)
dform mt_lid[$name:s] = slot[$name:s]
dform mt_uid[$name:s] = slot[$name:s]

(*
 * Signature.
 *)
dform mt_sig{'sil} =
   szone pushm push_indent "sig" sbreak
   slot{list_expr; 'sil}
   popm sbreak "end" popm ezone

(*
 * Module type with clause.
 *)
dform mt_with{'mt; 'wcl} =
   szone pushm slot{'mt} slot{mt_with; 'wcl} popm ezone

dform slot{mt_with; nil} = ""

dform slot{mt_with; cons{'wc; 'wcl}} =
   slot{'wc} slot{mt_with; 'wcl}

(*
 * $Log$
 * Revision 1.1  1998/02/13 16:02:17  jyh
 * Partially implemented semantics for caml.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
