(*
 * Logical true.
 *)

include Czf_itt_set
include Czf_wf

declare "true"

primrw unfoldTrue : "true" <--> (0 = 0 in int)

(*
 * True is always true.
 *
 * H >- true
 * by true_intro
 *)
prim true_intro 'H : : sequent { 'H >- "true" } =
   it

(*
 * True is well formed.
 *
 * H >- wf{"true"}
 * by true_wf
 *)
prim true_wf 'H : :
   sequent { 'H >- wf{."true"} } =
   it

(*
 * True is a restricted formula.
 *)
prim true_res 'H : :
   sequent { 'H >- restricted{."true"} } =
   it

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
