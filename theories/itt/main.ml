(*
 * Simple tester.
 *)

open Printf
open Debug;;
open Util;;

(*
 * Show that the file is loading.
 *)
let _ =
   if !debug_load then
      eprintf "Loading Main%t" eflush

debug_string DebugLoad "Loading itt main...";;

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
