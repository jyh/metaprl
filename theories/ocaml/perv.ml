(*
 * These are the public pervasive terms.
 *)

open Printf
open Debug

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Perv%t" eflush

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "nil"
declare "cons"{'car; 'cdr}
declare "string"[@s:s]
declare "lambda"{x. 'b}
declare "hyp"{'A; x. 'B}
declare "concl"{'A; 'B}
declare "sequent"{'A}
declare "rewrite"{'redex; 'contractum}

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

(*
 * Pervasive display forms.
 *)
dform perv_nil_df : "nil" = `""

dform perv_cons_df : "cons"{'car; 'cdr} =
   slot{'car} slot{'cdr}

dform perv_string_df : "string"[@s:s] =
   `"\"" slot[@s:s] `"\""

(*
 * $Log$
 * Revision 1.2  1998/05/07 16:03:07  jyh
 * Adding interactive proofs.
 *
 * Revision 1.1  1998/04/29 20:54:14  jyh
 * Initial working display forms.
 *
 * Revision 1.4  1998/04/24 19:39:10  jyh
 * Updated debugging.
 *
 * Revision 1.3  1998/04/24 02:43:17  jyh
 * Added more extensive debugging capabilities.
 *
 * Revision 1.2  1998/04/23 20:04:49  jyh
 * Initial rebuilt editor.
 *
 * Revision 1.1  1998/04/17 01:31:28  jyh
 * Editor is almost constructed.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
