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
 * $Log$
 * Revision 1.1  1997/04/28 15:51:59  jyh
 * This is the initial checkin of Nuprl-Light.
 * I am porting the editor, so it is not included
 * in this checkin.
 *
 * Directories:
 *     refiner: logic engine
 *     filter: front end to the Ocaml compiler
 *     editor: Emacs proof editor
 *     util: utilities
 *     mk: Makefile templates
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
