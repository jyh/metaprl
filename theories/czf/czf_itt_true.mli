(*
 * Logical true.
 *)

include Czf_itt_set

declare "true"

(*
 * Definition of truth.
 *)
rewrite unfoldTrue : "true" <--> (0 = 0 in int)

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
 * True is a restricted formula.
 *)
axiom true_res 'H :
   sequent ['ext] { 'H >- restricted{."true"} }

(*
 * $Log$
 * Revision 1.2  1998/07/02 18:37:17  jyh
 * Refiner modules now raise RefineError exceptions directly.
 * Modules in this revision have two versions: one that raises
 * verbose exceptions, and another that uses a generic exception.
 *
 * Revision 1.1  1998/06/15 22:32:53  jyh
 * Added CZF.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
