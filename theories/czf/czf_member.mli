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
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
