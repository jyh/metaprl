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
dform "nil" = `""

dform "cons"{'car; 'cdr} =
   slot{'car} slot{'cdr}

(*
 * $Log$
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
