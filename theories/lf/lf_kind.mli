(*
 * Valid kinds.
 *)

include Lf_sig;;

declare equal{'A; 'B};;

(*
 * Const family.
 *)
axiom const_fam 'S 'C :
   ctx{'S1[hyp{'K; c. 'S2[nil_sig; 'c]}]; 'C[nil_ctx]} -->
   sequent { 'S1; c. 'K; 'S2['c]; 'C['c] >> mem{'c; 'K}};;

(*
 * Kind equality.
 *)
axiom conv_fam 'S 'C :
   sequent { 'S; 'C >> mem{'A; 'K1 } } -->
   sequent { 'S; 'C >> 'K2 } -->
   sequent { 'S; 'C >> equal{'K1; 'K2} } -->
   sequent { 'S; 'C >> mem{'A; 'K2} };;

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
