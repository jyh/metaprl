(*
 * Valid contexts.
 *
 * $Log$
 * Revision 1.1  1997/04/28 15:52:33  jyh
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

include Lf_sig;;

declare ctx{'S; 'C};;
declare nil_ctx;;

axiom empty_ctx : sig{'S} --> ctx{'S; nil_ctx};;
                     
axiom type_ctx 'S 'C : ctx{'S[nil_sig]; 'C[nil_ctx] } -->
    sequent { 'S; 'C >> mem{'A; type} } -->
    ctx{'S[nil_sig]; 'C[hyp{'A; x. nil_ctx}]};;

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
