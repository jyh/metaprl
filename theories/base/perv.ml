(*
 * These are the public pervasive terms.
 *)

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
