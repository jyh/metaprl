(*
 * These are the public pervasive terms.
 *)

open Printf
open Nl_debug

open Refiner.Refiner

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
(* declare "sequent"{'A} *)
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
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
