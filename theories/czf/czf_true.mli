(*
 * Logical true.
 *)

include Czf_wf

declare "true"

(*
 * True is always true.
 *
 * H >- true
 * by true_intro
 *)
axiom true_intro 'H : sequent { 'H >- "true" }

(*
 * True is well formed.
 *
 * H >- wf{"true"}
 * by true_wf
 *)
axiom true_wf 'H :
   sequent { 'H >- wf{."true"} }

(*
 * True is a restricted formula.
 *)
axiom true_res 'H :
   sequent { 'H >- restricted{."true"} }

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
