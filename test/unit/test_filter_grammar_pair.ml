(* unit-link: filter *)
(* Filter_grammar's matched-pair lexer (add_token_pair: lexer_match and
   trim_quotation_name), which no unit test, theory build or proof census
   reached (2026-11-18 rank737), although the base grammar declares its
   comment and quotation tokens as pairs (theories/meta/base/
   base_grammar.mli; also theories/experimental/compile/m_ast.mli), the
   quotation in the form tested here.  The grammar here has one pair
   token, opened by <:name< (or <<)
   and closed by >>, whose contractum takes the text, the quotation's
   name and the closing lexeme, as the lexer hands them; an end-of-input
   token; and res[x; y; z] <-- tok_q[x; y; z]; tok_eof.  Each case parses
   one input and prints the three strings, or the exception.
   Read from the output: a nested opener raises the level and its text
   is kept, to three levels; << names the quotation "term"; an
   unterminated quotation fails, nested or not.
   Pinned as found: the closing lexeme >> trims to nothing, so the third
   string is the quotation's name (trim_quotation_name's default); the
   end-of-file message names the opener untrimmed (<:foo<).
   The expected file is the output of the code as written (2026-11-18),
   never typed.  Mutants (2026-11-18, each rebuilt and relinked; an
   identity control unchanged): an opener not nesting, a closer not
   unnesting, an opener's text dropped, ':' not a quote character, no
   default name, the closing lexeme not trimmed: 6 of 6 RED. *)
open Opname
open Filter_base_type
open Refiner.Refiner
open TermType
open Term
open TermShape

let op s = mk_opname s nil_opname
let c s = mk_simple_term (op s) []
let mstrings s l = mk_term (mk_op (op s) (List.map (fun v -> make_param (MString (Lm_symbol.add v))) l)) []
let lexer_id = op "lex"
let res = mstrings "res" [ "x"; "y"; "z" ]

(* a quotation token <:name< ... >> whose contractum takes the text, the
   quotation's name and the closing lexeme, as the lexer hands them *)
let grammar =
  let g = Filter_grammar.empty in
  let g = Filter_grammar.add_token_pair g lexer_id (Lm_symbol.add "t_q") "<:?[a-z]*<" ">>" (Some (mstrings "tok_q" [ "lexeme"; "arg1"; "arg2" ])) in
  let g = Filter_grammar.add_token g lexer_id (Lm_symbol.add "t_eof") "\\'" (Some (c "tok_eof")) in
  let g = Filter_grammar.add_production g (Lm_symbol.add "p_res") [ mstrings "tok_q" [ "x"; "y"; "z" ]; c "tok_eof" ] None res in
  let g = Filter_grammar.add_start g "res" (shape_of_term res) lexer_id in
  Filter_grammar.compile g; g

let state =
  { parse_quotation = (fun _ _ -> failwith "no quotations here");
    parse_opname = (fun _ _ _ _ -> failwith "no opnames here");
    parse_shape = (fun _ -> failwith "no shapes here");
    parse_param = (fun _ -> failwith "no params here") }

let strings t = List.map (fun p -> match dest_param p with String s -> "\"" ^ String.escaped s ^ "\"" | _ -> "?") (dest_op (dest_term t).term_op).op_params

let case input =
  let out =
    try String.concat ", " (strings (Filter_grammar.parse state grammar (shape_of_term res) Ploc.dummy input)) with
    | Failure m -> "Failure " ^ m
    | Invalid_argument m -> "Invalid_argument " ^ m
    | Ploc.Exc (_, e) -> "Ploc.Exc " ^ Printexc.to_string e
    | e -> "raised " ^ Printexc.to_string e
  in
  Printf.printf "%-28s %s\n%!" (String.escaped input) out

let () =
  List.iter case [
    "<:foo<abc>>";
    "<<abc>>";
    "<:foo<>>";
    "<:foo<a<:b<x>>c>>";
    "<:foo<a<<x>>c>>";
    "<:foo<a<:b<x<:c<y>>>>z>>";
    "<:foo<abc";
    "<:foo<a<:b<x>>";
    "<:foo<a>b>>";
    "<:foo<a\nb>>";
  ]
