(*
 * Collect the theory.
 *)

include Czf_wf;;
include Czf_member;;
include Czf_true;;
include Czf_false;;
include Czf_and;;
include Czf_or;;
include Czf_implies;;
include Czf_all;;
include Czf_exists;;

(*
 * $Log$
 * Revision 1.1  1997/04/28 15:52:03  jyh
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
