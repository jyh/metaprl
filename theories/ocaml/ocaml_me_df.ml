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
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
