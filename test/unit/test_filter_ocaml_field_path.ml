(* unit-link: filter *)
(* unit-native: camlp5/o_keywords.cmx camlp5/pa_o.cmx camlp5/pr_o.cmx *)
(*
 * Filter_ocaml.mk_expr's field through a module path, e.M.f (camlp5 8's
 * ExFle with a module qualifier: the comps fold that builds one proj per
 * module name, each over the enclosing location), which no unit test,
 * theory build or proof census reached (2026-11-18 rank737; the rank's
 * "mk_expr@869 37" is the whole let rec chain).  Each item is parsed,
 * converted to a term and back as in test_filter_ocaml, and printed with
 * "same" when it prints back as it was read; its encoded term is printed
 * too, so the operator names and the locations are seen, not only what
 * decodes back.
 * Read from the output: every form round-trips: one, two and three
 * module names, a field of an application, a path after a field
 * (r.M.f.N.g), an assignment and a record update.
 * The expected file is the output of the code as written (2026-11-18),
 * never typed.  Mutants (2026-11-18, each rebuilt and relinked; an
 * identity control unchanged): the module names in reverse order, a
 * module name encoded as a lower-case name, and each proj given its
 * own name's location in place of the enclosing one: 3 of 3 RED; the
 * second and third only through the printed term (the decoder reads both
 * names back alike, and locations do not print).
 *)
module F = Filter_ocaml.FilterOCaml (Refiner.Refiner)

let parse_str s = fst (List.hd (fst (Pcaml.parse_implem (Stream.of_string s))))
let pr_str si = Eprinter.apply Pcaml.pr_str_item Pprintf.empty_pc si

let parse_sig s = fst (List.hd (fst (Pcaml.parse_interf (Stream.of_string s))))
let pr_sig si = Eprinter.apply Pcaml.pr_sig_item Pprintf.empty_pc si

let one_line s = String.concat " " (List.filter (( <> ) "") (List.map String.trim (String.split_on_char '\n' s)))

let rec str s =
   flush stdout; str1 s; flush stdout
and str1 s =
   match parse_str s with
      exception e -> Printf.printf "PARSE %s: %S\n" (Printexc.to_string e) s
    | si ->
         let a = one_line (pr_str si) in
         match F.str_item_of_term (F.term_of_str_item [] si) with
            si' -> let b = one_line (pr_str si') in
               if a = b then Printf.printf "same      %s\n" a else Printf.printf "DIFFERS   %s\n       ->  %s\n" a b
          | exception e -> Printf.printf "RAISES    %s\n       ->  %s\n" a (match e with Filter_ocaml.FormatError (m, _) -> "FormatError " ^ m | e -> Printexc.to_string e)

(* the encoded term of each item's expression, so its operator names and
   locations are seen, not only what decodes back *)
let term s =
   match parse_str s with
      exception e -> Printf.printf "PARSE %s\n" (Printexc.to_string e)
    | si -> Printf.printf "   term   %s\n%!" (Simple_print.SimplePrint.string_of_term (F.term_of_str_item [] si))

let () =
   List.iter (fun s -> str s; term s) [
      "let a = r.M.f;;"; "let b = r.M.N.f;;"; "let c = r.M.N.O.f;;"; "let d = (g x).M.f;;";
      "let e = r.M.f.N.g;;"; "let h = r.M.f <- 1;;"; "let k = { r with M.f = 1 }.M.f;;";
   ]
