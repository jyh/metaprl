(*
 * Valid signatures.
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
