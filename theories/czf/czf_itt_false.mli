(*
 * Logical false.
 *)

include Czf_itt_set
include Czf_itt_empty

open Tacticals

declare "false"

(*
 * Empty type.
 *)
rewrite unfold_false : "false" <--> void

(*
 * From false prove anything.
 *
 * H, x: false, J >> T
 * by false_elim i
 *)
axiom false_elim 'H 'J :
   sequent ['ext] { 'H; x: "false"; 'J['x] >- 'T['x] }

(*
 * False is well-formed.
 *)
axiom false_wf 'H :
   sequent ['ext] { 'H >- wf{."false"} }

(*
 * False is a type.
 *)
axiom false_type 'H :
   sequent ['ext] { 'H >- "type"{."false"} }

(*
 * False is a restricted formula.
 *)
axiom false_res 'H :
   sequent ['ext] { 'H >- restricted{x ."false"} }

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
