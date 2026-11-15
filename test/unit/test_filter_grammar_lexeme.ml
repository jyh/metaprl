(* unit-link: filter *)
(*
 * Filter_grammar: a grammar built and run through its own interface
 * (add_token, add_production, add_start, compile, parse), and what the
 * lexer hands a token's contractum.
 *
 * Every lexeme is rewritten from a term whose arguments are the lexeme,
 * a "string" form of it, and the regex's groups.  The string form is
 * string_of_lexeme (not exported): for a lexeme in double quotes it is the
 * text between the quotes with \n, \r, \t and three-digit decimal escapes
 * replaced; any other lexeme is itself.  No unit test built a grammar
 * before this one (bisect at 332a148a2: string_of_lexeme's 17 points
 * unreached), and no grammar in this tree uses the string argument: the
 * base grammar's string token takes its regex group (tok_string[arg1:s]),
 * so it sees the escapes as written.
 *
 * The grammar here has one quoted-string token, tok_str[lexeme; string],
 * an end-of-input token, and one production res[x; y] <-- tok_str[x; y];
 * tok_eof.  Each case parses one literal and prints its lexeme and string
 * with String.escaped, or the exception.
 *
 * The last two cases use a token of the base grammar's form, whose
 * contractum takes its regex group and not the string argument: the
 * string is computed anyway, so "\999" raised there too, before the fix.
 *
 * Pinned as found: a backslash before the closing quote is kept; \\ is
 * not an escape (both backslashes are kept); an escape with fewer than
 * three digits keeps its backslash.  Fixed after this test was written:
 * a decimal escape over 255 raised Invalid_argument "Char.chr" out of
 * parse; it now keeps its backslash, like any other non-escape.
 *)

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
let res = mstrings "res" [ "x"; "y" ]

(* The string token's regex and the arguments its contractum takes. *)
let make_grammar regex args =
   let g = Filter_grammar.empty in
   let g = Filter_grammar.add_token g lexer_id (Lm_symbol.add "t_str") regex (Some (mstrings "tok_str" args)) in
   let g = Filter_grammar.add_token g lexer_id (Lm_symbol.add "t_eof") "\\'" (Some (c "tok_eof")) in
   let g = Filter_grammar.add_production g (Lm_symbol.add "p_res") [ mstrings "tok_str" [ "x"; "y" ]; c "tok_eof" ] None res in
   let g = Filter_grammar.add_start g "res" (shape_of_term res) lexer_id in
      Filter_grammar.compile g;
      g

let grammar = make_grammar "\"[^\"]*\"" [ "lexeme"; "string" ]

(* The base grammar's form (theories/meta/base/base_grammar.mli): the
 * token takes its regex group and never the string argument. *)
let grammar_group = make_grammar "\"\\([^\"]*\\)\"" [ "lexeme"; "arg1" ]

let state =
   { parse_quotation = (fun _ _ -> failwith "no quotations here");
     parse_opname = (fun _ _ _ _ -> failwith "no opnames here");
     parse_shape = (fun _ -> failwith "no shapes here");
     parse_param = (fun _ -> failwith "no params here")
   }

let strings t =
   List.map (fun p -> match dest_param p with String s -> String.escaped s | _ -> "?") (dest_op (dest_term t).term_op).op_params

let case ?(grammar = grammar) ?(second = "string") input =
   let out =
      try
         match strings (Filter_grammar.parse state grammar (shape_of_term res) Ploc.dummy input) with
            [ x; y ] -> Printf.sprintf "lexeme \"%s\", %s \"%s\"" x second y
          | l -> "unexpected " ^ String.concat ", " l
      with
         Invalid_argument m -> "Invalid_argument " ^ m
       | Failure m -> "Failure " ^ m
   in
      Printf.printf "%-12s %s\n" (String.escaped input) out

let () =
   List.iter case
      [ {|"plain"|};
        {|""|};
        {|"a\nb"|};
        {|"\r\t"|};
        {|"\065\066"|};
        {|"\255"|};
        {|"\000x"|};
        {|"\q"|};
        {|"\06x"|};
        {|"\12"|};
        {|"x\\"|};
        {|"ab\"|};
        {|"\256"|};
        {|"\999"|} ];
   print_endline "-- a token that takes its regex group, not the string argument";
   List.iter (case ~grammar:grammar_group ~second:"arg1") [ {|"a\nb"|}; {|"\999"|} ]
