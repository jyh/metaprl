(*
 * Set membership.
 *)

declare member{'x; 'y};;

(*
 * Membership by assumption.
 *)
axiom hyp_mem 'H 'J :
   sequent { 'H; x: 'A; 'J >> member{'x; 'A} };;

(*
 * $Log$
 * Revision 1.1  1997/04/28 15:52:01  jyh
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
