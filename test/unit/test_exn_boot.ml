(* Exn_boot.format_exn, the formatter the proof editor prints a failed
   command's exception with, which no unit test named (coverage recount
   11-10).  It adds two cases in front of Refine_exn.format_exn: the proof
   errors (ExtRefineError, ProofRefineError, which need a proof and are not
   covered here) and Unix.Unix_error, printed as
     UnixError: <function> (<argument>): <the errno's message>
   with the parenthesis left out when the argument is "".  Every other
   exception must format exactly as Refine_exn.format_exn formats it; that is
   checked byte for byte on a list of exceptions, and the Unix forms are
   printed at widths 80 and 20, with the errno's message (the platform's
   Unix.error_message, checked to end the text) shown as <message>. *)
open Refiner.Refiner

let show f w exn = let buf = Lm_rformat.new_buffer () in f Dform.null_base buf exn; Lm_rformat_text.print_text_string w buf

let () =
  let others =
    [ "Not_found", Not_found; "Failure", Failure "nth"; "Invalid_argument", Invalid_argument "List.nth";
      "RefineError StringError", RefineError.RefineError ("rwtactic", RefineError.StringError "assum number is out of range");
      "RefineError IntError", RefineError.RefineError ("nth_hyp", RefineError.IntError 3);
      "Sys_error", Sys_error "x: No such file or directory" ] in
  List.iter (fun (name, e) ->
      let a = show Exn_boot.format_exn 80 e and b = show Refine_exn.format_exn 80 e in
      Printf.printf "%-24s %s  %S\n" name (if a = b then "same as Refine_exn" else "DIFFERS from Refine_exn: " ^ String.escaped b) a)
    others;
  let unix =
    [ Unix.Unix_error (Unix.ENOENT, "open", "/no/such/file"); Unix.Unix_error (Unix.EACCES, "unlink", "");
      Unix.Unix_error (Unix.EINTR, "select", ""); Unix.Unix_error (Unix.EUNKNOWNERR 99999, "read", "fd 3") ] in
  (* The errno's message is the platform's (Unix.error_message), so it is checked against that and printed as <message>. *)
  List.iter (fun e ->
      let msg = match e with Unix.Unix_error (n, _, _) -> Unix.error_message n | _ -> assert false in
      List.iter (fun w ->
          let s = show Exn_boot.format_exn w e in
          let k = String.length s - String.length msg in
          if k >= 0 && String.sub s k (String.length msg) = msg then Printf.printf "width %2d  %S\n" w (String.sub s 0 k ^ "<message>")
          else Printf.printf "width %2d  DOES NOT END WITH Unix.error_message: %S\n" w s) [ 80; 20 ]) unix
