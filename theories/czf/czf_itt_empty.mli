(*
 * Empty set.
 *)

include Czf_itt_set

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

declare "empty"

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

rewrite unfold_empty : empty <--> collect{void; x. 'x}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * Empty is a set.
 *)
axiom empty_isset 'H :
   sequent ['ext] { 'H >- isset{empty} }

(*
 * Nothing is in the empty set.
 *)
axiom empty_member_elim 'H 'J :
   sequent ['ext] { 'H; x: member{'y; empty}; 'J >- 'T }

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
