(*
 * Valid signatures.
 *
 * $Log$
 * Revision 1.2  1998/06/01 13:56:37  jyh
 * Proving twice one is two.
 *
 * Revision 1.1  1997/04/28 15:52:36  jyh
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

declare sig{'S};;
declare nil_sig;;
declare mem{'A; 'B};;
declare type;;

(*
 * Valid signatures.
 *)
axiom nil_sig : sig{nil_sig};;

axiom kind_sig 'S : sig{'S[nil_sig]} -->
    sequent { 'S >> 'K } -->
    sig{'S[hyp{'K; a. nil_sig}]};;

axiom type_sig 'S : sig{'S[nil_sig]} -->
   sequent { 'S >> mem{'A; type} } -->
   sig{'S[hyp{'A; c. nil_sig}]};;

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
