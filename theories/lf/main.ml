(*
 * Simple tester.
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
