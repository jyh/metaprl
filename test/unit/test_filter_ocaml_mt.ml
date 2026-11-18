(* unit-link: filter *)
(* unit-native: camlp5/o_keywords.cmx camlp5/pa_o.cmx camlp5/pr_o.cmx *)
(*
 * Filter_ocaml's module types named by a lowercase path (dest_lid_mt, and
 * dest_proj_mt's MtLongLid arm: M.s), the quoted module type
 * (dest_quot_mt), and the refusals of dest_proj_mt and dest_apply_mt ("not
 * a module type path"), which no unit test, theory build or proof census
 * reached (2026-11-15 rank).  The round trip is test_filter_ocaml's: parse
 * (pa_o), term_of_sig_item, sig_item_of_term, print (pr_o, one line).
 * A quoted module type ('a) and the refusals cannot be written in OCaml's
 * own syntax (pa_o refuses "'a"), so the last block parses an item,
 * renames operators in its term (mt_lid to mt_quot; mt_uid to mt_lid,
 * which makes a path's head not a path), and turns that term back.
 * Read from the output: a quoted module type comes back as a node pr_o
 * prints as nothing ("module type T").
 * The expected file is the output of the code as written (2026-11-15),
 * never typed.
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

let rec sg s =
   flush stdout; sg1 s; flush stdout
and sg1 s =
   match parse_sig s with
      exception e -> Printf.printf "PARSE %s: %S\n" (Printexc.to_string e) s
    | si ->
         let a = one_line (pr_sig si) in
         match F.sig_item_of_term (F.term_of_sig_item si) with
            si' -> let b = one_line (pr_sig si') in
               if a = b then Printf.printf "same      %s\n" a else Printf.printf "DIFFERS   %s\n       ->  %s\n" a b
          | exception e -> Printf.printf "RAISES    %s\n       ->  %s\n" a (match e with Filter_ocaml.FormatError (m, _) -> "FormatError " ^ m | e -> Printexc.to_string e)

let () =
   List.iter sg [
      "module type T = s;;"; "module type T = M.s;;"; "module type T = M.N.s;;"; "module type T = F(X).s;;";
      "module type T = 'a;;"; "module M : s;;"; "module type T = functor (X : s) -> M.s;;";
      "include M.s;;"
   ]

(* Term surgery: each operator whose name is a renamed to b, everywhere. *)
open Refiner.Refiner.Term
open Refiner.Refiner.TermType
open Term_sig
let rec rename a b t =
   if is_var_term t then t
   else
      let { term_op = op; term_terms = bts } = dest_term t in
      let { op_name = o; op_params = ps } = dest_op op in
      let o = match Opname.dest_opname o with
                 x :: rest when x = a -> Opname.make_opname (b :: rest)
               | _ -> o in
      let bts = List.map (fun bt -> let { bvars = vs; bterm = t } = dest_bterm bt in mk_bterm vs (rename a b t)) bts in
         mk_term (mk_op o ps) bts

let surg what a b s =
   flush stdout;
   (match parse_sig s with
       exception e -> Printf.printf "PARSE %s: %S\n" (Printexc.to_string e) s
     | si ->
          let t = rename a b (F.term_of_sig_item si) in
          match F.sig_item_of_term t with
             si' -> Printf.printf "%-22s %s\n" what (one_line (pr_sig si'))
           | exception e -> Printf.printf "%-22s RAISES %s\n" what (match e with Filter_ocaml.FormatError (m, _) -> "FormatError " ^ m | e -> Printexc.to_string e));
   flush stdout

let () =
   surg "s as a quotation" "mt_lid" "mt_quot" "module type T = s;;";
   surg "M.s, M lowercase" "mt_uid" "mt_lid" "module type T = M.s;;";
   surg "F(X).s, F lowercase" "mt_uid" "mt_lid" "module type T = F(X).s;;";
   surg "F(X), F lowercase" "mt_uid" "mt_lid" "module type T = F(X).S;;"
