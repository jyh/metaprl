(* unit-link: filter *)
(*
 * Filter_reflection's rule quoting: mk_rule_term (sweep_rulequote_term,
 * the "ugly" step-checking function) and mk_intro_thm (the intro theorem,
 * sweep_min_rulequote_term), each on the same rules.  Their sweeps had
 * arms nothing reached (2026-11-15 rank): in sweep_rulequote_term the
 * refusal of a context and an unquote; in sweep_min_rulequote_term an
 * unquote and a context term (its body and arguments swept, the new
 * context variable added to its contexts).
 *
 * The parse state is test_filter_reflection_quote's (every operator
 * Reflect!<name>).  Each line prints the quoted term, or each premise and
 * the goal of the theorem joined by "-->" (Simple_print, whitespace
 * collapsed), or the refusal.
 *
 * Pinned as found: in mk_intro_thm a second-order variable and a
 * sequent's context hypothesis each add a well-formedness premise
 * (Reflect!equal{BTerm ...}, Reflect!equal{CVar ...}), and a context TERM
 * adds none: sweep_min_rulequote_term's context arm never records it.
 *
 * The expected file is the output of the code as written (2026-11-16),
 * never typed.
 *)
open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMeta
open Refiner.Refiner.RefineError

let v = Lm_symbol.add
let op s = Opname.make_opname [ s; "Test" ]
let k s = mk_simple_term (op s) []
let var x = mk_var_term (v x)
let pair a b = mk_simple_term (op "pair") [ a; b ]
let unq t = mk_dep0_term (Opname.mk_opname "xunquote" (Opname.mk_opname "Perv" Opname.nil_opname)) t
let ctx h t args = mk_context_term (v h) t [] args
let seq hyps concl = mk_sequent_term { sequent_args = k "sa"; sequent_hyps = SeqHyp.of_list hyps; sequent_concl = concl }

let state = {
  Filter_base_type.parse_quotation = (fun _ _ -> failwith "parse_quotation");
  parse_opname = (fun _ names _ _ -> Opname.make_opname (List.rev names @ [ "Reflect" ]));
  parse_shape = (fun _ -> failwith "parse_shape");
  parse_param = (fun _ -> failwith "parse_param");
}
let info = Filter_reflection.create_parse_info state
let flat s = String.concat " " (List.filter (( <> ) "") (String.split_on_char ' ' (String.map (fun c -> if c = '\n' then ' ' else c) s)))
let st t = flat (Simple_print.SimplePrint.string_of_term t)
let smt m = let ps, g = unzip_mfunction m in String.concat " --> " (List.map (fun (_, _, p) -> st p) ps @ [ st g ])
let guard f = try f () with
  | RefineError (s, StringTermError (m, _)) -> "refused (" ^ s ^ ": " ^ m ^ ")"
  | RefineError (s, _) -> "RefineError " ^ s
  | RefineForceError (_, s, _) -> "RefineForceError " ^ s
  | Failure s -> "Failure " ^ s
  | Invalid_argument s -> "Invalid_argument " ^ s

let cases = [
  "c", Term_sig.MetaTheorem (k "c");
  "xunquote{c}", Term_sig.MetaTheorem (unq (k "c"));
  "pair{xunquote{x}; c}", Term_sig.MetaTheorem (pair (unq (var "x")) (k "c"));
  "<H>[c]", Term_sig.MetaTheorem (ctx "H" (k "c") []);
  "<H>[c] with an argument", Term_sig.MetaTheorem (ctx "H" (k "c") [ k "a" ]);
  "c --> xunquote{c}", Term_sig.MetaImplies (Term_sig.MetaTheorem (k "c"), Term_sig.MetaTheorem (unq (k "c")));
  "<H>[c] --> c", Term_sig.MetaImplies (Term_sig.MetaTheorem (ctx "H" (k "c") []), Term_sig.MetaTheorem (k "c"));
  "'a[c]", Term_sig.MetaTheorem (mk_so_var_term (v "a") [] [ k "c" ]);
  "sequent <J> >- c", Term_sig.MetaTheorem (seq [ Term_sig.Context (v "J", [], []) ] (k "c"));
]

let () =
  print_endline "mk_rule_term (sweep_rulequote_term):";
  List.iter (fun (name, m) -> Printf.printf "  %-26s %s\n" name (guard (fun () -> st (Filter_reflection.mk_rule_term info m)))) cases;
  print_endline "mk_intro_thm (sweep_min_rulequote_term):";
  List.iter (fun (name, m) ->
      Printf.printf "  %-26s %s\n" name (guard (fun () ->
          let _, m', _ = Filter_reflection.mk_intro_thm info (k "logic") Filter_base_type.ProvableSequent m [] in smt m'))) cases
