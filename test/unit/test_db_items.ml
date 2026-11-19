(* unit-link: filter *)
(* Db's compressed items of the Nuprl-5 link's session term text
   (library/db.ml, scan_compressed and scan_item): a byte with 0xC0 set
   adds the item that follows to a level table (its low 3 bits name the
   kind), and a byte with 0x80 set and the next byte look one up.
   test_db_session_terms adds opids, terms and numerals; nothing reached
   (2026-11-15 rank) the other three kinds: a binding (1), a parameter (2)
   and an operator (3).  Each is added where it is read and looked up
   again where it is read next; then a lookup before any add, and a lookup
   of an item of the wrong kind (a binding where a parameter is read, a
   parameter where a binding is).  Each line prints the term read
   (Simple_print) or the exception; Basic's Nuprl5_Exception is not
   exported, so its message is the lines Basic.error prints first.
   Not reached, stated: with_open_static_file (the l...l levels prefix
   reads a level table from the link's database directory, and its error
   names the file's full path, which a public expected file must not hold).
   The expected file is the output of the code as written (2026-11-16),
   never typed. *)
let flat t = String.concat " " (String.split_on_char '\n' (Simple_print.SimplePrint.string_of_term t))
let show name f s =
  let r = try flat (f s) with Failure m -> "Failure " ^ m | e -> Printexc.to_string e in
    Printf.printf "%-34s %s\n%!" name r

let () =
  List.iter (fun s -> show ("session " ^ String.escaped s) Db.session_string_to_term s)
    [ "tfoo{}(\xc1x.bar{}())t";
      "tfoo{}(\xc1x.bar{}();\x80\x00.baz{}())t";
      "tfoo{\xc2abc:t}()t";
      "tfoo{\xc2abc:t}(bar{\x80\x00}())t";
      "tfoo{\xc27:n}(bar{\x80\x00}())t";
      "t\xc3foo{1:n}()t";
      "t\xc3foo{1:n}(\x80\x00())t";
      "t\xc3foo{1:n}(\x80\x00(bar{}()))t";
      "tfoo{}(\x80\x00.bar{}())t";
      "tfoo{\x80\x00}()t";
      "tfoo{}(\xc1x.bar{\x80\x00}())t";
      "tfoo{\xc2abc:t}(\x80\x00.bar{}())t" ]
