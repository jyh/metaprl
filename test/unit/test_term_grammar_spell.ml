(* unit-link: filter *)
(*
 * Term_grammar with spelling on (the "spell" debug flag, which the filter
 * sets for a theory build that checks its comments): the words of a doc
 * comment checked against Filter_spell's dictionary, the forms that turn
 * the check off (dform comments, @code, @misspelled, ...) or add a word
 * (@spelling), words joined by an apostrophe, and raise_spelling_error,
 * which reports the misspelled words on stderr and raises.  No unit test
 * turned the flag on before (bisect at a45cd0437: raise_spelling_error 10
 * points and parse_comment's spelling arms unreached).
 *
 * Filter_spell reads its dictionary from $(MPLIB), so the cases run in a
 * child process (this program again) whose MPLIB is a fresh directory
 * holding two small words files; nothing is written into the tree's lib.
 * The child's stdout and stderr are read through one pipe, in order.
 *
 * Pinned as found:
 * - raise_spelling_error names only the first word of its sorted list
 *   when the location has a line number: "alpha wrold betta wrold" reports
 *   betta alone (its print stops after the first word), and raises
 *   Failure "spelling (wrold)", the first word met;
 * - a doc comment is parsed in math mode, where Comment_parse names a term
 *   math_<name>, and the spelling switch knows only math_misspelled,
 *   math_tt, math_rulebox and math_defrule: in a doc comment the words of
 *   @url, @license and @comment are checked, and @spelling adds nothing.
 *   A topdoc comment is not in math mode, and there they work.
 * (@code's text is a parameter, never a word, so it is never checked.)
 *
 * The grammar is instantiated with its own entries and the permissive
 * parsing state of test_term_grammar_params.  Each case parses one
 * comment quotation and then calls raise_spelling_error, printing what it
 * reports and raises.  The expected file is the output of the code.
 *)
open Filter_type
open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermOp

let the_state = ref None

module Before : TermGrammarSig =
struct
   let parsing_state _ = match !the_state with Some s -> s | None -> failwith "no parsing state"
   let gram              = Pcaml.gram
   let opname            = Grammar.Entry.create gram "opname"
   let opname_name       = Grammar.Entry.create gram "opname_name"
   let term_eoi          = Grammar.Entry.create gram "term_eoi"
   let term              = Grammar.Entry.create gram "term"
   let parsed_term       = Grammar.Entry.create gram "parsed_term"
   let quote_term        = Grammar.Entry.create gram "quote_term"
   let mterm             = Grammar.Entry.create gram "mterm"
   let bmterm            = Grammar.Entry.create gram "mterm"
   let singleterm        = Grammar.Entry.create gram "singleterm"
   let parsed_bound_term = Grammar.Entry.create gram "bound_term"
   let xdform            = Grammar.Entry.create gram "xdform"
   let term_con_eoi      = Grammar.Entry.create gram "term_con_eoi"
end

module TG = Term_grammar.MakeTermGrammar (Before)

let () =
   the_state := Some {
      opname_prefix = (fun _ -> Opname.nil_opname);
      mk_opname_kind = (fun _ _ names _ _ -> Opname.make_opname names);
      find_shape_class = (fun _ _ -> Filter_shape.shape_normal);
      mk_var_contexts = (fun _ _ _ -> None);
      infer_term = (fun _ t -> t);
      check_rule = (fun _ _ _ -> ());
      check_rewrite = (fun _ _ _ -> ());
      check_type_rewrite = (fun _ _ _ -> ());
      check_dform = (fun _ _ _ -> ());
      check_iform = (fun _ _ -> ());
      check_production = (fun _ _ _ -> ());
      check_input_term = (fun _ _ -> ());
      check_input_mterm = (fun _ _ -> ());
      allow_seq_bindings = (fun _ _ -> true);
      apply_iforms = (fun _ _ t -> t);
      apply_iforms_mterm = (fun _ _ mt args -> mt, args);
      term_of_string = (fun _ _ _ _ -> failwith "term_of_string");
   }

let rec exn_string = function
   Ploc.Exc (_, e) -> exn_string e
 | Failure s -> "Failure " ^ s
 | e -> Printexc.to_string e

let case curr nm s =
   Printf.printf "%s in %s: %S\n%!" nm curr s;
   (match TG.parse_quotation Ploc.dummy curr nm s with
       _ -> ()
     | exception e -> Printf.printf "  parse refused: %s\n%!" (exn_string e));
   (match Term_grammar.raise_spelling_error () with
       () -> Printf.printf "  no spelling error\n%!"
     | exception e -> Lm_printf.eflush Lm_printf.stderr; Printf.printf "\n  raised: %s\n%!" (exn_string e))

let child () =
   Lm_debug.set_debug "spell" true;
   case "term" "doc" "alpha beta world";
   case "term" "doc" "alpha wrold betta wrold";
   case "term" "topdoc" "a betta here";
   case "term" "dform" "wrold betta";
   case "term" "doc" "@code{wrold}";
   case "term" "doc" "@misspelled{betta}";
   case "term" "doc" "@tt{zork}";
   case "term" "doc" "@url{qqq}";
   case "term" "doc" "@bf{wrold}";
   case "term" "doc" "@spelling{zork}";
   case "term" "doc" "zork";
   case "term" "doc" "@spelling{zork} zork";
   case "term" "doc" "don't and do'nt";
   case "term" "doc" "'tis and 'twas";
   (* topdoc comments are not parsed in math mode *)
   case "term" "topdoc" "@url{qqq}";
   case "term" "topdoc" "@license{qqq}";
   case "term" "topdoc" "@spelling{zork}";
   case "term" "doc" "zork"

let write_file file text =
   let out = open_out_bin file in
      output_string out text;
      close_out out

let rec remove_dir dir =
   Array.iter (fun f ->
         let p = Filename.concat dir f in
            if Sys.is_directory p then remove_dir p else Sys.remove p) (Sys.readdir dir);
   Unix.rmdir dir

let parent () =
   let dir = Filename.concat (Filename.get_temp_dir_name ()) (Printf.sprintf "test_term_grammar_spell_%d" (Unix.getpid ())) in
   Unix.mkdir dir 0o700;
   write_file (Filename.concat dir "words.metaprl") "alpha\nbeta\nworld\nand\ndon't\n'tis\n";
   write_file (Filename.concat dir "words.linux") "a\nhere\n";
   let keep e = not (String.length e >= 6 && String.sub e 0 6 = "MPLIB=") && not (String.length e >= 22 && String.sub e 0 22 = "TEST_TERM_GRAMMAR_SPEL") in
   let env = Array.of_list (("MPLIB=" ^ dir) :: "TEST_TERM_GRAMMAR_SPELL=child" :: List.filter keep (Array.to_list (Unix.environment ()))) in
   let r, w = Unix.pipe () in
   let pid = Unix.create_process_env Sys.executable_name [| Sys.executable_name |] env Unix.stdin w w in
   Unix.close w;
   let ic = Unix.in_channel_of_descr r in
   let rec lines () = match input_line ic with l -> print_endline l; lines () | exception End_of_file -> () in
   lines ();
   close_in ic;
   (match snd (Unix.waitpid [] pid) with
       Unix.WEXITED 0 -> ()
     | Unix.WEXITED n -> Printf.printf "child exited %d\n" n
     | _ -> print_endline "child killed");
   remove_dir dir

let () =
   match Sys.getenv_opt "TEST_TERM_GRAMMAR_SPELL" with
      Some "child" -> child ()
    | _ -> parent ()
