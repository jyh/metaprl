(*
 * Well-formedness judgement.
 * Rules for well-formedness are included
 * in the modules for each operator.
 *
 * We also include the "restricted" judgement,
 * which is used to define restricted separation.
 *)

include Czf_itt_wf

declare wf{'A}

declare restricted{'A}

(*
 * $Log$
 * Revision 1.1  1998/06/15 22:33:03  jyh
 * Added CZF.
 *
 * Revision 1.1  1997/04/28 15:52:04  jyh
 * This is the initial checkin of Nuprl-Light.
 * I am porting the editor, so it is not included
 * in this checkin.
 *
 * Directories:
 *     refiner: logic engine
 *     filter: front end to the Ocaml compiler
 *     editor: Emacs proof editor
 *     util: utilities
 *     mk: Makefile templates
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
