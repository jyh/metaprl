(* unit-link: filter *)
(*
 * Filter_grammar's save path (what Filter_cache does to a module's
 * grammar before it is marshalled, and after it is loaded): is_empty,
 * is_modified, prepare_to_marshal (which names the grammar) and
 * unmarshal (which checks the name), none of which a unit test reached
 * (bisect at a45cd0437).  A one-token grammar is built through the
 * interface, as in test_filter_grammar_lexeme.  Each line prints what a
 * function answers, and unmarshal's complaints on stderr, captured.
 * Pinned as found: unmarshal of a grammar that was never named resets it
 * to the empty grammar, and reports its old name as '.empty' (the name of
 * the grammar it was built from).  The expected file is the output of the
 * code.
 *)
open Opname
open Refiner.Refiner
open TermType
open Term
open TermShape

let op s = mk_opname s nil_opname
let c s = mk_simple_term (op s) []
let res = c "res"

let make () =
   let g = Filter_grammar.empty in
   let g = Filter_grammar.add_token g (op "lex") (Lm_symbol.add "t_x") "x" (Some (c "tok_x")) in
   let g = Filter_grammar.add_token g (op "lex") (Lm_symbol.add "t_eof") "\\'" (Some (c "tok_eof")) in
   let g = Filter_grammar.add_production g (Lm_symbol.add "p_res") [ c "tok_x"; c "tok_eof" ] None res in
      Filter_grammar.add_start g "res" (shape_of_term res) (op "lex")

let capture f =
   let file = Filename.temp_file "tfgm" ".err" in
   flush stderr; Lm_printf.eflush Lm_printf.stderr;
   let saved = Unix.dup Unix.stderr in
   let fd = Unix.openfile file [ Unix.O_WRONLY; Unix.O_TRUNC ] 0o600 in
   Unix.dup2 fd Unix.stderr; Unix.close fd;
   let r = (try Ok (f ()) with e -> Error e) in
   flush stderr; Lm_printf.eflush Lm_printf.stderr;
   Unix.dup2 saved Unix.stderr; Unix.close saved;
   let ic = open_in_bin file in
   let s = really_input_string ic (in_channel_length ic) in
      close_in ic; Sys.remove file;
      List.iter (fun l ->
            let n = String.length l in
            let l = if n > 0 && l.[n - 1] = '\r' then String.sub l 0 (n - 1) else l in
               if l <> "" then Printf.printf "    stderr: %s\n" l) (String.split_on_char '\n' s);
      r

let say name b = Printf.printf "%-44s %b\n" name b

let () =
   let e = Filter_grammar.empty and g = make () in
   say "is_empty empty" (Filter_grammar.is_empty e);
   say "is_empty (one token, one production)" (Filter_grammar.is_empty g);
   say "is_empty (a production only)"
      (Filter_grammar.is_empty (Filter_grammar.add_production Filter_grammar.empty (Lm_symbol.add "p_only") [ c "tok_x" ] None res));
   say "is_modified empty" (Filter_grammar.is_modified e);
   say "is_modified the new grammar" (Filter_grammar.is_modified g);
   Printf.printf "unmarshal of the grammar before it is named:\n";
   (match capture (fun () -> Filter_grammar.unmarshal g) with
       Ok g' -> say "    the result is empty" (Filter_grammar.is_empty g')
     | Error x -> Printf.printf "    raised %s\n" (Printexc.to_string x));
   Filter_grammar.prepare_to_marshal g "test_module";
   say "after prepare_to_marshal: is_modified" (Filter_grammar.is_modified g);
   Filter_grammar.prepare_to_marshal g "another_name";
   say "prepared again: is_modified" (Filter_grammar.is_modified g);
   Printf.printf "unmarshal of the named grammar:\n";
   match capture (fun () -> Filter_grammar.unmarshal g) with
      Ok g' ->
         say "    the result is modified" (Filter_grammar.is_modified g');
         say "    it still parses \"x\"" (try ignore (Filter_grammar.parse { Filter_base_type.parse_quotation = (fun _ _ -> failwith "q"); parse_opname = (fun _ _ _ _ -> failwith "o"); parse_shape = (fun _ -> failwith "s"); parse_param = (fun _ -> failwith "p") } g' (shape_of_term res) Ploc.dummy "x"); true with _ -> false)
    | Error x -> Printf.printf "    raised %s\n" (Printexc.to_string x)
