(* unit-link: filter *)
(* Db's reader of the Nuprl-5 link's term text (library/db.ml):
   string_to_term (scan_term) and session_string_to_term
   (session_read_term), which no unit test, theory build or proof census
   reached (2026-11-15 rank).  The plain form is opid{value:type, ...}
   (bound terms; ...); a byte with 0x80 set is compressed: with 0xC0 it
   adds the item that follows (low 3 bits: 0 an opid, 4 a term, 5 a
   numeral) to a level table, otherwise it and the next byte look an item
   up (index ((b land 0x0F) lsl 8) + next).  A session term is t...t.
   Each line prints the term read (Simple_print) or the exception; Basic's
   Nuprl5_Exception is not exported, so its message is the line
   Basic.error prints first.
   Read from the output: a lookup before any add raises Failure "nth";
   make_operator's !metaprl_implementation arm refuses a first parameter
   that is not a list, or a list that is not of strings; its success arm
   needs a parameter list of strings, which string_to_parameter never
   makes, so text cannot reach it (stated).  Not reached: the l...l levels
   prefix (read_levels).
   The expected file is the output of the code as written (2026-11-15),
   never typed. *)
let flat t = String.concat " " (String.split_on_char '\n' (Simple_print.SimplePrint.string_of_term t))
let show name f s =
  let r = try flat (f s) with Failure m -> "Failure " ^ m | e -> Printexc.to_string e in
    Printf.printf "%-28s %s\n%!" name r

let () =
  List.iter (fun s -> show (String.escaped s) Db.string_to_term s)
    [ "foo{}()"; "foo{1:n}()"; "foo{1:n,abc:t}(bar{}())"; "foo{}(x.bar{}())"; "foo{}(bar{}();baz{}())";
      "!metaprl_implementation{a:s}()"; "!metaprl_implementation{%Aa:t}()" ];
  List.iter (fun s -> show ("session " ^ String.escaped s) Db.session_string_to_term s)
    [ "tfoo{}()t"; "x"; "t\xc0foo{}()t"; "t\xc0foo{}(\x80\x00{}())t"; "t\xc0foo{}(\x80\x00{1:n}();\x80\x00{}())t";
      "t\xc5\x07{}()t"; "t\xc4bar{}()t"; "t\x80\x00{}()t" ]
