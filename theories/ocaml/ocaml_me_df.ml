(*
 * Display forms for module expressions.
 *)

include Ocaml
include Ocaml_base_df
include Ocaml_expr_df
include Ocaml_mt_df

open Debug
open Printf

let _ =
   if !debug_load then
      eprintf "Loading Ocaml_me_df%t" eflush

(*
 * Projection.
 *)
dform me_proj_df : me_proj{'me1; 'me2} = proj{'me1; 'me2}

(*
 * Application.
 *)
dform me_apply_df : me_apply{'me1; 'me2} = apply{'me1; 'me2}

(*
 * Functor.
 *)
dform me_functor_df : me_functor[@name:s]{'mt; 'me} = mt_functor[@name:s]{'mt; 'me}

(*
 * Structure.
 *)
dform me_struct_df : me_struct{'sil} =
   szone pushm[0] push_indent "_struct" sbreak
   slot{list_expr; 'sil}
   popm sbreak "_end" popm ezone

(*
 * Type cast.
 *)
dform me_cast_df : me_cast{'me; 'mt} =
   "(" szone pushm[0] slot{'me} space ":" space slot{'mt} popm ezone ")"

(*
 * Variables.
 *)
dform me_lid_df : me_lid[@name:s] = slot[@name:s]
dform me_uid_df : me_uid[@name:s] = slot[@name:s]

(*
 * $Log$
 * Revision 1.5  1998/05/04 13:01:32  jyh
 * Ocaml display without let rec.
 *
 * Revision 1.4  1998/04/29 20:54:05  jyh
 * Initial working display forms.
 *
 * Revision 1.3  1998/04/29 14:49:05  jyh
 * Added ocaml_sos.
 *
 * Revision 1.2  1998/02/18 18:47:23  jyh
 * Initial ocaml semantics.
 *
 * Revision 1.1  1998/02/13 16:02:15  jyh
 * Partially implemented semantics for caml.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
