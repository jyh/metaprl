(*
 * Valid kinds.
 *
 * $Log$
 * Revision 1.1  1997/04/28 15:52:37  jyh
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
 *)

include lf_ctx;;

axiom type_kind 'S 'C : ctx{'S[nil_sig]; 'C[nil_ctx]} -->
   sequent { 'S; 'C >> type };;

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
