(* Ascii_io's by-name and by-file readers and its handling of a damaged
   .prla file (test_term_io covers write_term / read_table / get_term
   round trips): read_from_file, get_named_term, and read_table on files
   derived from one written by write_term — a line dropped, a line doubled,
   an unknown line kind, a reference to an undefined name, an empty file.
   The term is f{lam x. x; c}; its file names the term t4, the binder's
   body t, the lam term t2, and the opname c. Each case prints the term
   read (Simple_print) or the exception. Pinned as it reads today. *)
open Refiner.Refiner.Term
module A = Ascii_io.AsciiIO
module P = Simple_print.SimplePrint

let op s = Opname.make_opname [ s ]
let file = "test_ascii_io_files.prla"
let lines_of f = let ic = open_in_bin f in
  let rec go acc = match input_line ic with l -> go (l :: acc) | exception End_of_file -> List.rev acc in
  let l = go [] in close_in ic; l
let write_lines f l = let oc = open_out_bin f in List.iter (fun s -> output_string oc s; output_char oc '\n') l; close_out oc
let attempt name f = Printf.printf "%-46s %s\n" name (try P.string_of_term (f ()) with e -> "raised " ^ Printexc.to_string e)
let table_of l = write_lines file l; let ic = open_in_bin file in
  let t = try Ok (A.read_table ic) with e -> Error e in close_in ic; t

let () =
  let x = Lm_symbol.add "x" in
  let t = mk_simple_term (op "f") [ mk_term (mk_op (op "lam") []) [ mk_bterm [ x ] (mk_var_term x) ]; mk_simple_term (op "c") [] ] in
  let oc = open_out_bin file in A.write_term oc (A.initialize ()) t; close_out oc;
  let lines = lines_of file in
  Printf.printf "written: %d lines, first field of each: %s\n" (List.length lines)
    (String.concat " " (List.map (fun l -> String.sub l 0 1) lines));
  attempt "read_from_file t4 (the whole term)" (fun () -> A.read_from_file file "t4");
  attempt "read_from_file t2 (the lam term)" (fun () -> A.read_from_file file "t2");
  attempt "read_from_file t (the binder's body)" (fun () -> A.read_from_file file "t");
  attempt "read_from_file c (an opname, not a term)" (fun () -> A.read_from_file file "c");
  attempt "read_from_file zz (no such name)" (fun () -> A.read_from_file file "zz");
  attempt "read_from_file of a missing file" (fun () -> A.read_from_file "no_such_file.prla" "t4");
  let field1 l = List.nth (String.split_on_char '\t' l) 1 in
  let cases = [
    "the whole file", lines;
    "the line defining t2 dropped", List.filter (fun l -> field1 l <> "t2") lines;
    "the line defining t3 doubled", List.concat_map (fun l -> if field1 l = "t3" then [ l; l ] else [ l ]) lines;
    "t3 redefined as t (a second definition)", List.map (fun l -> if field1 l = "t3" then "T\tt3\to2" else l) lines @ [ "T\tt\to3" ];
    "an unknown line kind X", lines @ [ "X\tx1\tsomething" ];
    "the last line cut to two fields", (match List.rev lines with l :: r -> List.rev ((String.concat "\t" (List.filteri (fun i _ -> i < 2) (String.split_on_char '\t' l))) :: r) | [] -> []);
    "an empty file", [];
  ] in
  List.iter (fun (name, l) ->
      match table_of l with
      | Error e -> Printf.printf "%-46s read_table raised %s\n" name (Printexc.to_string e)
      | Ok tbl ->
          attempt (name ^ ": get_term") (fun () -> A.get_term tbl);
          attempt (name ^ ": get_named_term t2") (fun () -> A.get_named_term tbl "t2")) cases;
  Sys.remove file
