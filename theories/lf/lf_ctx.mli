(*
 * Valid contexts.
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
