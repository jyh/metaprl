(*
 * Valid kinds.
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
