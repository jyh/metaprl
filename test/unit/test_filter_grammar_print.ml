(* unit-link: filter *)
(*
 * Filter_grammar.pp_print_grammar and the parser's pp_print_symbol
 * (filter/base/filter_grammar.ml), which no unit test reached (bisect at
 * a45cd0437).  A one-token grammar is built through the interface, as in
 * test_filter_grammar_marshal, printed into Lm_printf's string channel,
 * and the "grammar" debug flag read before and after.
 * Pinned as found: printing a grammar turns the "grammar" debug flag on
 * (pp_print_grammar sets debug_grammar := true) and leaves it on.
 * The expected file is the output of the code.
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

let flag () = (Lm_debug.get_debug "grammar").Lm_debug.debug_value

let print name g =
   ignore (Lm_printf.flush_stdstr ());
   Lm_printf.fprintf Lm_printf.stdstr "%a@." Filter_grammar.pp_print_grammar g;
   let s = Lm_printf.flush_stdstr () in
   Printf.printf "== %s\n" name;
   List.iter (fun l ->
         let n = String.length l in
         let l = if n > 0 && l.[n - 1] = '\r' then String.sub l 0 (n - 1) else l in
            if String.trim l <> "" then Printf.printf "  %s\n" l) (String.split_on_char '\n' s)

let () =
   Printf.printf "\"grammar\" flag before printing: %b\n" (flag ());
   print "the empty grammar" Filter_grammar.empty;
   Printf.printf "\"grammar\" flag after printing: %b\n" (flag ());
   Lm_debug.set_debug "grammar" false;
   print "one token, one production, one start" (make ());
   Printf.printf "\"grammar\" flag after printing again: %b\n" (flag ())
