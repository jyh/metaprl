(*
 * Simple tester.
 *
 * $Log$
 * Revision 1.1  1997/04/28 15:52:38  jyh
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
 * Revision 1.4  1996/04/11 13:34:55  jyh
 * This is the final version with the old syntax for terms.
 *
 * Revision 1.3  1996/03/28 02:51:48  jyh
 * This is an initial version of the type theory.
 *
 * Revision 1.2  1996/03/05 19:59:56  jyh
 * Version just before LogicalFramework.
 *
 * Revision 1.1  1996/02/13 21:36:04  jyh
 * Intermediate checkin while matching is bing added to the refiner.
 *
 * Revision 1.3  1996/02/10 20:19:53  jyh
 * Initial checkin of filter (prlcomp).
 *
 * Revision 1.2  1996/02/07 23:41:14  jyh
 * First working version in CamlSpecialLight.
 *
 * Revision 1.1  1995/12/06 16:42:50  jyh
 * This is an ML version of a term rewriting system.
 * This checkin is partial, and provides a rewriter on
 * regular terms.
 *
 *)

open Debug;;
open Util;;

debug_string DebugLoad "Loading LF main...";;

let main argv =
   let argc = Array.length argv in
      ();;

(* Initialization *)
main Sys.argv;;

(*
 * Flush output files.
 *)
exit 0;;

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
