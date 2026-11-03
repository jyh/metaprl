(* Comment_parse (mllib), the lexer and parser for the structured comments
   of theory files (@opname[params]{args}, $math$, <<quotations>>,
   @begin[verbatim] blocks), which the filter's term grammar turns into doc
   terms. No unit test linked it (the 11-02 mllib coverage page). A table of
   comment strings, each printed with its parse: items as s-expressions,
   locations as line:column (column counted from 0), and a Parse_error with
   its message and span. The bool argument starts the parse in math mode.
   Each case is pinned as the parser answers today; the table is chosen to
   reach every token kind, each mode, and each named error.
   Recorded, not fixed (11-02):
   - a verbatim / iverbatim / literal / html block loses the lookahead the
     parser read while looking for more [params] or {args}: the newline after
     @begin[verbatim] (which reads as intended), but also the first word of
     text on the same line ("  two spaces" keeps " spaces") and a leading
     "[" or "{". parse_code_block clears the pushed-back tokens. All 29
     verbatim blocks in metaprl start on a new line, so none is affected.
   - a variable is written ''x (the lexer's varname already holds one quote);
     'x is a quote and a word.
   - @code{...} does not nest braces: the first } ends it. *)
open Comment_parse

let pos (p : Lexing.position) = Printf.sprintf "%d:%d" p.Lexing.pos_lnum (p.Lexing.pos_cnum - p.Lexing.pos_bol)
let span (a, b) = pos a ^ "-" ^ pos b

let rec items l = String.concat " " (List.map item l)
and item = function
  | White -> "_"
  | String s -> Printf.sprintf "%S" s
  | Variable s -> "var:" ^ s
  | Term ((name, l), params, args) ->
      Printf.sprintf "(@%s@%s [%s] %s)" (String.concat "!" name) (pos (fst l))
        (String.concat ";" (List.map (Printf.sprintf "%S") params))
        (String.concat " " (List.map (fun a -> "{" ^ items a ^ "}") args))
  | Quote (l, tag, s) -> Printf.sprintf "(quote@%s %S %S)" (pos (fst l)) tag s
  | Block t -> "{" ^ items t ^ "}"

let case math s =
  let r = try items (parse math s) with
    | Parse_error (m, l) -> Printf.sprintf "Parse_error %S at %s" m (span l)
    | e -> "raised " ^ Printexc.to_string e in
  Printf.printf "%s%S\n  => %s\n" (if math then "math " else "") s r

let () =
  List.iter (fun (m, s) -> case m s) [
    false, "";
    false, "plain words";
    false, "two\nlines";
    false, "a_b^c; d,e [f] !g";
    false, "@bf{bold} and @tt[x]";
    false, "@hrefterm[a; b,c]{one}{two}";
    false, "@foo_bar[x]";
    false, "@\"quoted name\"{x}";
    false, "{a {b}}";
    false, "'x and 'y1 and 'z'";
    false, "\"a string\" and \"esc \\\" quote\"";
    false, "before (* a (* nested *) comment *) after";
    false, "<<1 + 2>> and <:doc< x <<y>> >>";
    false, "$x_1 + y^2$";
    false, "$$a_{i}$$";
    true, "x_1^2";
    false, "@code{let x = {1}}";
    false, "@email{someone at example}";
    false, "@begin[doc] text @end[doc]";
    false, "@begin[verbatim] a { b @end[verbatim]";
    false, "@begin[literal]<x>@end[literal]";
    false, "@begin[iverbatim]i@end[iverbatim]";
    false, "@begin[html]<b>@end[html]";
    false, "@begin[doc]\nline two\n@end[doc]";
    false, "@begin[verbatim]\nlet x = 1\n@end[verbatim]";
    false, "@begin[verbatim]\n\nlet x = 1\n@end[verbatim]";
    false, "@begin[verbatim]  two spaces@end[verbatim]";
    false, "@begin[verbatim][x]@end[verbatim]";
    false, "@begin[verbatim]{x}@end[verbatim]";
    false, "''x and ''y'";
    false, "@foo{a; b}";
    false, "@code{a}b";
    (* errors *)
    false, "(* open comment";
    false, "<<open quotation";
    false, "\"open string";
    false, "@bf{unclosed";
    false, "{unclosed";
    false, "closed}";
    false, "$x";
    false, "@begin[doc] x @end[other]";
    false, "@begin[verbatim] never ended";
    false, "@code{never ended";
    false, "$x_$";
    false, "@foo[a{b}]";
    false, "@\"open name";
  ]
