(*
 * Display forms for module types.
 *)

include Ocaml
include Ocaml_base_df
include Ocaml_expr_df

open Debug
open Printf

open Ocaml_expr_df

let _ =
   if !debug_load then
      eprintf "Loading Ocaml_mt_df%t" eflush

(*
 * Projection.
 *)
dform mt_proj_df: parens :: "prec"[prec_proj] :: mt_proj{'mt1; 'mt2} =
   slot{'mt1} "." slot{'mt2}

(*
 * Application.
 *)
dform mt_apply_df : parens :: "prec"[prec_apply] :: mt_apply{'mt1; 'mt2} =
   slot{'mt1} space slot{'mt2}

(*
 * Functor.
 *)
dform mt_functor_df : parens :: "prec"[prec_fun] :: mt_functor[@name:s]{'mt1; 'mt2} =
   "functor" space "(" slot[@name:s] space ":" space slot{'mt1} ")"
   space "->" slot{'mt2}

(*
 * Id.
 *)
dform mt_lid_df : mt_lid[@name:s] = slot[@name:s]
dform mt_uid_df : mt_uid[@name:s] = slot[@name:s]

(*
 * Signature.
 *)
dform mt_sig_df : mt_sig{'sil} =
   szone pushm[0] push_indent "sig" sbreak
   slot{list_expr; 'sil}
   popm sbreak "end" popm ezone

(*
 * Module type with clause.
 *)
dform mt_with_df : mt_with{'mt; 'wcl} =
   szone pushm[0] slot{'mt} slot{mt_with; 'wcl} popm ezone

dform mt_with_nil_df : slot{mt_with; nil} = `""

dform mt_with_cons_df : slot{mt_with; cons{'wc; 'wcl}} =
   slot{'wc} slot{mt_with; 'wcl}

(*
 * $Log$
 * Revision 1.4  1998/04/29 20:54:06  jyh
 * Initial working display forms.
 *
 * Revision 1.3  1998/04/29 14:49:10  jyh
 * Added ocaml_sos.
 *
 * Revision 1.2  1998/02/18 18:47:30  jyh
 * Initial ocaml semantics.
 *
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
