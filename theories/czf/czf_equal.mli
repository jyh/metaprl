(*
 * Equality on sets.
 * We make this dependent on membership, rather than the opposite.
 *)

include Czf_member;;
include Czf_all;;
include Czf_implies;;
include Czf_and;;

declare equal{'A; 'B};;

(*
 * Extensionality.
 * Perhaps there is a better way to formulate this.
 *)
axiom extensional_equal :
   sequent { 'H >> "all"{x. "all"{y. equal{'x; 'y} => "all"{z. member{'z; 'x} => member{'z; 'y}}}} };;

(*
 * Membership is functional.
 *)
axiom mem_fun :
   sequent { 'H >> "all"{x. "all"{y. "all"{z. (equal{'x; 'y} /\ member{'x; 'z}) => member{'y; 'z}}}} };;

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
