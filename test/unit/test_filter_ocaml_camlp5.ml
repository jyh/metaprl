(* unit-link: filter *)
(* unit-native: camlp5/o_keywords.cmx camlp5/pa_o.cmx camlp5/pr_o.cmx *)
(*
 * Filter_ocaml on camlp5's own syntax nodes, which OCaml's syntax cannot
 * write and so test_filter_ocaml cannot parse: a signature group
 * (MLast.SgDcl, "declare ... end"), a class signature group (CgDcl), and
 * a class-type extension (CtXtr, with and without a body), each built as
 * camlp5 syntax and taken to a term (term_of_sig_item) and back
 * (sig_item_of_term), then printed by pr_o where it can be ("(term same)"
 * when the term of the item that comes back is alpha_equal to the
 * first).  Then the refusals of a class type path whose head is not a
 * module path (dest_acc_ct, dest_app_ct), reached by renaming a String
 * parameter of a parsed item's term to lowercase.  None of these arms was
 * reached by a unit test, the theory build or the proof census
 * (2026-11-15 rank).
 * Pinned as found: term_of_sig_item writes a signature group with one
 * subterm per item, and sig_item_of_term reads one list subterm, so the
 * group is refused ("bad arity"); it writes a class-type extension with
 * its name as a parameter and one subterm, and reads two subterms, so the
 * extension is refused too.  pr_o cannot print a class signature group.
 * The expected file is the output of the code as written (2026-11-15),
 * never typed.
 *)
module F = Filter_ocaml.FilterOCaml (Refiner.Refiner)

let parse_str s = fst (List.hd (fst (Pcaml.parse_implem (Stream.of_string s))))
let pr_str si = Eprinter.apply Pcaml.pr_str_item Pprintf.empty_pc si

let parse_sig s = fst (List.hd (fst (Pcaml.parse_interf (Stream.of_string s))))
let pr_sig si = Eprinter.apply Pcaml.pr_sig_item Pprintf.empty_pc si

let one_line s = String.concat " " (List.filter (( <> ) "") (List.map String.trim (String.split_on_char '\n' s)))

let back name si =
   flush stdout;
   let t = F.term_of_sig_item si in
   (match F.sig_item_of_term t with
       si' ->
          let same = Refiner.Refiner.TermSubst.alpha_equal t (F.term_of_sig_item si') in
          Printf.printf "%-26s %s%s\n" name (try one_line (pr_sig si') with e -> "(pr_o: " ^ Printexc.to_string e ^ ")")
            (if same then "  (term same)" else "  (term DIFFERS)")
     | exception e -> Printf.printf "%-26s RAISES %s\n" name (match e with Filter_ocaml.FormatError (m, _) -> "FormatError " ^ m | e -> Printexc.to_string e));
   flush stdout

let loc = Ploc.dummy
let ci_of s = match parse_sig s with MLast.SgClt (_, Ploc.VaVal [ ci ]) -> ci | _ -> failwith "not one class type"
let with_exp ci e = MLast.SgClt (loc, Ploc.VaVal [ { ci with MLast.ciExp = e } ])

let () =
   (* declare ... end: camlp5's group of signature items *)
   back "declare val x; type t end" (MLast.SgDcl (loc, Ploc.VaVal [ parse_sig "val x : int;;"; parse_sig "type t;;" ]));
   back "declare end" (MLast.SgDcl (loc, Ploc.VaVal []));
   let ci = ci_of "class type c = object method m : int method n : bool end;;" in
   (match ci.MLast.ciExp with
       MLast.CtSig (l, self, Ploc.VaVal csis) ->
          back "object declare m; n end end" (with_exp ci (MLast.CtSig (l, self, Ploc.VaVal [ MLast.CgDcl (loc, Ploc.VaVal csis) ])))
     | _ -> print_endline "not a CtSig");
   back "an extension [%x]" (with_exp ci (MLast.CtXtr (loc, "x", None)));
   back "an extension with a body" (with_exp ci (MLast.CtXtr (loc, "x", Some (Ploc.VaVal ci.MLast.ciExp))))

(* Term surgery: a String parameter a renamed to b, everywhere (a class path's head made lowercase). *)
open Refiner.Refiner.Term
open Refiner.Refiner.TermType
open Term_sig
let rec rename_param a b t =
   if is_var_term t then t
   else
      let { term_op = op; term_terms = bts } = dest_term t in
      let { op_name = o; op_params = ps } = dest_op op in
      let ps = List.map (fun p -> match dest_param p with String x when x = a -> make_param (String b) | _ -> p) ps in
      let bts = List.map (fun bt -> let { bvars = vs; bterm = t } = dest_bterm bt in mk_bterm vs (rename_param a b t)) bts in
         mk_term (mk_op o ps) bts

let surg name a b s =
   flush stdout;
   (match F.sig_item_of_term (rename_param a b (F.term_of_sig_item (parse_sig s))) with
       si' -> Printf.printf "%-26s %s\n" name (one_line (pr_sig si'))
     | exception e -> Printf.printf "%-26s RAISES %s\n" name (match e with Filter_ocaml.FormatError (m, _) -> "FormatError " ^ m | e -> Printexc.to_string e));
   flush stdout

let () =
   surg "M.ct as written" "M" "M" "class c : M.ct;;";
   surg "m.ct, m lowercase" "M" "m" "class c : M.ct;;";
   surg "F(M).ct as written" "F" "F" "class c : F(M).ct;;";
   surg "f(M).ct, f lowercase" "F" "f" "class c : F(M).ct;;"
