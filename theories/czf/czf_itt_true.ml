(*
 * Logical true.
 *)

include Czf_itt_wf

declare "true"

primrw unfoldTrue : "true" <--> (0 = 0 in int)

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform true_df : "true" =
   `"true"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

(*
 * True is always true.
 *
 * H >- true
 * by true_intro
 *)
prim true_intro 'H : : sequent ['ext] { 'H >- "true" } =
   it

(*
 * True is well formed.
 *
 * H >- wf{"true"}
 * by true_wf
 *)
prim true_wf 'H : :
   sequent ['ext] { 'H >- wf{."true"} } =
   it

(*
 * True is a restricted formula.
 *)
prim true_res 'H : :
   sequent ['ext] { 'H >- restricted{."true"} } =
   it

(*
 * $Log$
 * Revision 1.1  1998/06/15 22:32:52  jyh
 * Added CZF.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
