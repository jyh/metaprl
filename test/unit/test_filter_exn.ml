(* unit-link: filter *)
(*
 * Filter_exn (filter/base): how the filter prints an exception.
 *
 * format_exn is printed for each exception it names, at width 80, and
 * at width 30 for the location wrapper.  print_exn, stderr_exn and
 * handle_exn write to stderr; handle_exn then exits 2.  Each of those
 * runs in a child process (this program again), so that the exit is the
 * child's and so that OCAMLRUNPARAM is under the test's control: with
 * a 'b' in it, Refine_exn.backtrace is on and the exception passes
 * through unprinted.  The parent prints how each child ended.
 *
 * On a bisect build at 008a9607e the theory build and the proof census
 * reach none of format_exn's named cases, print_exn's handler,
 * stderr_exn or handle_exn's handler.
 *
 * The expected file is the output of the code.  Before the fix that
 * followed this test, BadCommand printed "Bad command:foo" (no space),
 * Bad_magic said "that is is either", and Bad_version put ", " after
 * the last supported version.
 *)
open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.RefineError
open Filter_type

let term s = mk_simple_term (Opname.make_opname [s]) []

let show w exn =
   let buf = Lm_rformat.new_buffer () in
      Filter_exn.format_exn Dform.null_base buf exn;
      Lm_rformat_text.print_text_string w buf

let v = File_type_base.pack_version

let cases = [
   "FormatError", Filter_ocaml.FormatError ("name", term "a");
   "BadParamCast", BadParamCast (make_param (Number (Lm_num.num_of_int 3)), "s");
   "ParseError", ParseError "unexpected token";
   "PrecNotFound", Filter_grammar.PrecNotFound (Refiner.Refiner.TermShape.shape_of_term (term "a"));
   "IterfImplemMismatch", IterfImplemMismatch "rule foo is missing";
   "BadCommand", BadCommand "foo";
   "EmptyModulePath", EmptyModulePath "string_of_path";
   "Bad_magic", File_type_base.Bad_magic "f.prla";
   "Bad_version", File_type_base.Bad_version ("f.prla", [v 1 0 0; v 1 2 3], v 2 0 0);
   "Ploc.Exc", Ploc.Exc (Ploc.make_loc "f.ml" 3 20 (25, 30) "", ParseError "inner");
   "Lm_parser.ParseError", Lm_parser.ParseError (Lm_location.create_loc (Lm_symbol.add "g.ml") 2 4 2 9, "bad");
   "Not_found (Exn_boot)", Not_found;
]

let child what =
   let f = function
      `Raise e -> raise e
    | `Return -> "returned"
   in
   let run name g =
      try Printf.printf "  %s: %s\n" name (g ()) with
         Refine_exn.ToploopIgnoreExn e -> Printf.printf "  %s: raised ToploopIgnoreExn (%s)\n" name (Printexc.to_string e)
       | RefineError (s, ToploopIgnoreError) -> Printf.printf "  %s: raised RefineError (%S, ToploopIgnoreError)\n" name s
       | RefineError (s, _) -> Printf.printf "  %s: raised RefineError (%S, _)\n" name s
       | e -> Printf.printf "  %s: raised %s\n" name (Printexc.to_string e)
   in
      Printf.printf "  backtrace %b\n" Refine_exn.backtrace;
      flush stdout;
      match what with
         "print_exn" ->
            run "print_exn None, a return" (fun () -> Filter_exn.print_exn Dform.null_base None f `Return);
            flush stdout;
            run "print_exn None, Not_found" (fun () -> Filter_exn.print_exn Dform.null_base None f (`Raise Not_found));
            flush stdout;
            run "print_exn (Some \"ctx\"), BadCommand" (fun () -> Filter_exn.print_exn Dform.null_base (Some "ctx") f (`Raise (BadCommand "x")));
            flush stdout;
            run "print_exn, a RefineError" (fun () ->
                  Filter_exn.print_exn Dform.null_base None f (`Raise (RefineError ("rw", StringError "no match"))));
            flush stdout;
            run "stderr_exn \"ctx\", ParseError" (fun () -> Filter_exn.stderr_exn "ctx" (ParseError "p"))
       | "handle_exn return" ->
            run "handle_exn, a return" (fun () ->
                  Filter_exn.handle_exn Dform.null_base None (Ploc.make_loc "h.ml" 1 0 (5, 9) "") (fun () -> "returned"))
       | "handle_exn plain" ->
            ignore (Filter_exn.handle_exn Dform.null_base (Some "ctx") (Ploc.make_loc "h.ml" 1 0 (5, 9) "")
                       (fun () -> raise (ParseError "plain")))
       | "handle_exn located" ->
            ignore (Filter_exn.handle_exn Dform.null_base None (Ploc.make_loc "h.ml" 1 0 (5, 9) "")
                       (fun () -> raise (Ploc.Exc (Ploc.make_loc "k.ml" 7 60 (61, 64) "", ParseError "located"))))
       | _ ->
            Printf.printf "  unknown case\n"

let run_child what backtrace =
   flush stdout;
   flush stderr;
   let env =
      List.filter (fun s ->
            let p k = String.length s >= String.length k && String.sub s 0 (String.length k) = k in
               not (p "OCAMLRUNPARAM=") && not (p "TEST_FILTER_EXN="))
         (Array.to_list (Unix.environment ()))
   in
   let env = ("TEST_FILTER_EXN=" ^ what) :: (if backtrace then ["OCAMLRUNPARAM=b"] else []) @ env in
   let pid =
      Unix.create_process_env Sys.executable_name [| Sys.executable_name |] (Array.of_list env)
         Unix.stdin Unix.stdout Unix.stdout
   in
      match Unix.waitpid [] pid with
         _, Unix.WEXITED n -> Printf.printf "  (exited %d)\n" n
       | _ -> Printf.printf "  (killed)\n"

let () =
   match Sys.getenv_opt "TEST_FILTER_EXN" with
      Some what -> child what
    | None ->
         Printf.printf "format_exn, width 80:\n";
         List.iter (fun (name, e) -> Printf.printf "  %-21s %S\n" name (show 80 e)) cases;
         Printf.printf "format_exn, width 30:\n";
         List.iter (fun (name, e) -> Printf.printf "  %-21s %S\n" name (show 30 e))
            (List.filter (fun (n, _) -> n = "Ploc.Exc" || n = "PrecNotFound") cases);
         List.iter (fun (what, bt) ->
               Printf.printf "%s%s:\n" what (if bt then ", OCAMLRUNPARAM=b" else "");
               run_child what bt)
            [ "print_exn", false; "print_exn", true;
              "handle_exn return", false; "handle_exn plain", false; "handle_exn located", false ]
