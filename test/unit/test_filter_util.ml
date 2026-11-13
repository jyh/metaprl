(* unit-link: filter *)
(*
 * Filter_util (filter/base): locations, rewrite specifications, opname
 * and module-path printing.
 *
 * adjust_pos places a location found inside a quotation (local, counted
 * from the quotation's text) in the file (globpos, the quotation's own
 * location, shifted past its opening "<<" or "<:name<").  Each case prints
 * the location as line, beginning of line, and [first, last).
 *
 * On a bisect build at 008a9607e the theory build and the proof census
 * reach none of mk_proper_loc, shift_pos, grammar_parse's exception arm,
 * unzip_rewrite's refusal, string_of_opname_list, translate_opname,
 * string_of_path or output_path, nor adjust_pos for a location past the
 * quotation's first line.
 *
 * The expected file is the output of the code.  Before the fix that
 * followed this test, adjust_pos counted the end from the quotation's
 * END, so [3, 5) in a quotation at [230, 250) gave [233, 255), past the
 * quotation; test_term_grammar_params shows the same on a syntax error.
 *)
open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Term_sig
open Filter_type

let show l =
   Printf.sprintf "%S line %d bol %d [%d, %d)" (Ploc.file_name l) (Ploc.line_nb l) (Ploc.bol_pos l) (Ploc.first_pos l) (Ploc.last_pos l)

let term s = mk_simple_term (Opname.make_opname [s]) []

let tstr t = Simple_print.SimplePrint.string_of_term t

let () =
   (* A quotation at characters 230-250 of f.ml, on line 10, which starts at 200. *)
   let glob = Ploc.make_loc "f.ml" 10 200 (230, 250) "" in
      Printf.printf "locations:\n";
      Printf.printf "  glob                      %s\n" (show glob);
      Printf.printf "  shift_pos glob 2          %s\n" (show (Filter_util.shift_pos glob 2));
      Printf.printf "  mk_proper_loc 4 9         %s\n"
         (show (Filter_util.mk_proper_loc (Lm_num.num_of_int 4) (Lm_num.num_of_int 9)));
      List.iter (fun (what, local) ->
            Printf.printf "  adjust_pos, %-12s %s\n                         -> %s\n"
               what (show local) (show (Filter_util.adjust_pos glob local)))
         [ "line 1", Ploc.make_loc "" 1 0 (3, 5) "";
           "line 3", Ploc.make_loc "" 3 12 (15, 18) "";
           "line 0", Ploc.make_loc "" 0 0 (0, 0) "" ];
      let p1 = { Lexing.pos_fname = "g.ml"; pos_lnum = 4; pos_bol = 40; pos_cnum = 44 } in
      let p2 = { p1 with Lexing.pos_cnum = 47 } in
         Printf.printf "  ploc_of_lexing            %s\n" (show (Filter_util.ploc_of_lexing (p1, p2)))

(*
 * grammar_parse resets Plexing's line counters for the parse and puts
 * the caller's back, on success and on an exception.
 *)
let () =
   Printf.printf "grammar_parse:\n";
   let entry =
      Grammar.Entry.of_parser (Grammar.gcreate (Plexer.gmake ())) "test_filter_util" (fun strm ->
            match Stream.next strm with
               ("", "!") -> failwith "a bang"
             | (_, s) -> Printf.sprintf "first token %S, line %d" s !(!Plexing.line_nb))
   in
   let lnum = ref 77 and bol = ref 88 in
      Plexing.line_nb := lnum;
      Plexing.bol_pos := bol;
      Pcaml.input_file := "caller.ml";
      let check what =
         Printf.printf "  %s: counters restored %b, input_file %S\n" what
            (!Plexing.line_nb == lnum && !Plexing.bol_pos == bol && !lnum = 77 && !bol = 88)
            !Pcaml.input_file
      in
         Printf.printf "  %s\n" (Filter_util.grammar_parse entry (Stream.of_string "hello world"));
         check "after a parse";
         (try
             ignore (Filter_util.grammar_parse entry (Stream.of_string "!"));
             Printf.printf "  no exception\n"
          with
             Ploc.Exc (_, Failure s) | Failure s -> Printf.printf "  raised Failure %S\n" s
           | exn -> Printf.printf "  raised %s\n" (Printexc.to_string exn));
         check "after an exception"

let () =
   Printf.printf "source_file_or:\n";
   Printf.printf "  unset: %S\n" (Filter_util.source_file_or "given.ml");
   Filter_util.source_file := "set.ml";
   Printf.printf "  set:   %S\n" (Filter_util.source_file_or "given.ml");
   Filter_util.source_file := ""

let () =
   Printf.printf "unzip_rewrite:\n";
   let show_rw mt =
      try
         let args, redex, contractum = Filter_util.unzip_rewrite "rw" mt in
            Printf.printf "  args [%s] redex %s contractum %s\n"
               (String.concat "; " (List.map tstr args)) (tstr redex) (tstr contractum)
      with
         BadCommand s -> Printf.printf "  refused: %s\n" s
   in
   let a = term "a" and b = term "b" and c = term "c" and d = term "d" in
      show_rw (MetaIff (MetaTheorem a, MetaTheorem b));
      show_rw (MetaImplies (MetaTheorem c, MetaImplies (MetaTheorem d, MetaIff (MetaTheorem a, MetaTheorem b))));
      show_rw (MetaTheorem a);
      show_rw (MetaImplies (MetaTheorem c, MetaTheorem a))

let () =
   Printf.printf "opnames:\n";
   List.iter (fun l ->
         Printf.printf "  string_of_opname_list [%s] = %S\n" (String.concat "; " l) (Filter_util.string_of_opname_list l))
      [ []; ["x"]; ["a"; "b"; "c"] ];
   List.iter (fun l ->
         let op = Opname.make_opname l in
            Printf.printf "  translate_opname (make_opname [%s]) = %S\n" (String.concat "; " l) (Filter_util.translate_opname op))
      [ []; ["x"]; ["a"; "b"; "c"] ]

let () =
   Printf.printf "module paths:\n";
   List.iter (fun p ->
         let s = try Printf.sprintf "%S" (Filter_util.string_of_path p) with EmptyModulePath s -> "EmptyModulePath " ^ s in
         let o =
            try Filter_util.output_path Lm_printf.stdstr p; Printf.sprintf "%S" (Lm_printf.flush_stdstr ())
            with EmptyModulePath s -> ignore (Lm_printf.flush_stdstr ()); "EmptyModulePath " ^ s
         in
            Printf.printf "  [%s]: string_of_path %s, output_path %s\n" (String.concat "; " p) s o)
      [ []; ["itt"]; ["itt_int"; "base"]; ["a"; "b"; "c"] ]
