(*
 * Logical true.
 *)

include Czf_itt_set

declare "true"

(*
 * Definition of truth.
 *)
rewrite unfold_true : "true" <--> unit

(*
 * True is always true.
 *
 * H >- true
 * by true_intro
 *)
axiom true_intro 'H : sequent ['ext] { 'H >- "true" }

(*
 * True is well formed.
 *
 * H >- wf{"true"}
 * by true_wf
 *)
axiom true_wf 'H :
   sequent ['ext] { 'H >- wf{."true"} }

(*
 * Typehood.
 *)
axiom true_type 'H :
   sequent ['ext] { 'H >- "type"{."true"} }

(*
 * True is a restricted formula.
 *)
axiom true_res 'H :
   sequent ['ext] { 'H >- restricted{x ."true"} }

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
