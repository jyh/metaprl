(*
 * These are the public pervasive terms.
 *)

declare "nil"
declare "cons"{'car; 'cdr}
declare "string"[@s:s]
declare "lambda"{x. 'b}
declare "hyp"{'A; x. 'B}
declare "concl"{'A; 'B}
declare "sequent"{'A}
declare "rewrite"{'redex; 'contractum}

(*
 * $Log$
 * Revision 1.1  1998/06/22 19:46:43  jyh
 * Rewriting in contexts.  This required a change in addressing,
 * and the body of the context is the _last_ subterm, not the first.
 *
 * Revision 1.1  1998/04/29 20:54:17  jyh
 * Initial working display forms.
 *
 * Revision 1.2  1998/04/23 20:04:52  jyh
 * Initial rebuilt editor.
 *
 * Revision 1.1  1998/04/17 01:31:30  jyh
 * Editor is almost constructed.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
