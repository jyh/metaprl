(* unit-link: filter *)
(* unit-native: camlp5/o_keywords.cmx camlp5/pa_o.cmx camlp5/pr_o.cmx *)
(*
 * Filter_ocaml's resource encoders (filter/base): term_of_resource_sig /
 * resource_sig_of_term and term_of_resource_str / resource_str_of_term,
 * which Filter_cache uses for a module's resource declarations and
 * definitions; no unit test reached them (bisect at a45cd0437).  Types and
 * expressions are parsed by camlp5's OCaml parser (pa_o) and printed by
 * its printer (pr_o), as in test_filter_ocaml.
 * Cases: each round trip; the old file format (ASCII IO <= 1.0.12, Term IO
 * <= 1.0.9), where a resource definition is a bare expression and reads
 * back with both types set to Filter_ocaml.fake_ctyp_made_for_old_file_
 * format_compatibility; a new-format term read with another resource
 * operator (taken for the old format); and a term of the wrong shape.
 * The expected file is the output of the code.
 *)
open Filter_type

module F = Filter_ocaml.FilterOCaml (Refiner.Refiner)

let ctyp s = Grammar.Entry.parse Pcaml.ctyp (Stream.of_string s)
let expr s = Grammar.Entry.parse Pcaml.expr (Stream.of_string s)
let pr_ctyp t = Eprinter.apply Pcaml.pr_ctyp Pprintf.empty_pc t
let pr_expr e = Eprinter.apply Pcaml.pr_expr Pprintf.empty_pc e
let one_line s = String.concat " " (List.filter (fun w -> w <> "") (String.split_on_char ' ' (String.concat " " (String.split_on_char '\n' s))))

let rop = Opname.make_opname [ "resource_def"; "Test" ]
let other = Opname.make_opname [ "other_def"; "Test" ]

let show_exn = function
  | Refiner.Refiner.RefineError.RefineError (s, _) -> "RefineError (" ^ s ^ ")"
  | Filter_ocaml.FormatError (s, _) -> "FormatError (" ^ s ^ ")"
  | e -> Printexc.to_string e

let line name f =
  Printf.printf "%-40s %s\n" name (try f () with e -> "raised " ^ show_exn e)

let sig_trip i o () =
  let r = F.resource_sig_of_term (F.term_of_resource_sig rop { resource_input = ctyp i; resource_output = ctyp o }) in
  "input " ^ one_line (pr_ctyp r.resource_input) ^ ", output " ^ one_line (pr_ctyp r.resource_output)

let show_str r =
  "input " ^ one_line (pr_ctyp r.res_input) ^ ", output " ^ one_line (pr_ctyp r.res_output) ^ ", body " ^ one_line (pr_expr r.res_body)

let () =
  print_endline "== resource_sig";
  line "int -> bool" (sig_trip "int" "bool");
  line "'a list -> (string * int) option" (sig_trip "'a list" "(string * int) option");
  line "a term of one subterm" (fun () ->
      ignore (F.resource_sig_of_term (F.term_of_type (ctyp "int"))); "read");
  print_endline "== resource_str";
  let r = { res_input = ctyp "int"; res_output = ctyp "bool"; res_body = expr "fun x -> x > 0" } in
  let t = F.term_of_resource_str rop r in
  line "int, bool, fun x -> x > 0" (fun () -> show_str (F.resource_str_of_term rop t));
  line "read with another operator" (fun () -> show_str (F.resource_str_of_term other t));
  line "old format: the bare expression" (fun () -> show_str (F.resource_str_of_term rop (F.term_of_expr [] (expr "List.rev"))))
