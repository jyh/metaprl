(*
 * Structural rules.
 * Could add thinning etc.
 *)

(*
 * Hyp.
 *)
axiom hyp 'H 'J :
   sequent { 'H; x: 'A; 'J >> 'A };;

(*
 * $Log$
 * Revision 1.2  1998/06/01 13:55:43  jyh
 * Proving twice one is two.
 *
 * Revision 1.1  1997/04/28 15:52:02  jyh
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
