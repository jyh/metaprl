(*
 * Logical false.
 *)

include Czf_wf;;

declare false;;

(*
 * From false prove anything.
 *
 * H, x: false, J >> T
 * by false_elim i
 *)
axiom false_elim 'H :
   sequent { 'H; x: false; 'J['x] >> 'T['x] };;

(*
 * False is well-formed.
 *)
axiom false_wf :
   sequent { 'H >> wf{false} };;

(*
 * False is a restricted formula.
 *)
axiom false_res :
   sequent { 'H >> restricted{false} };;

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
