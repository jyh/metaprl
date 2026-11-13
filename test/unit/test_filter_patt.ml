(* unit-link: filter *)
(* unit-native: filter/filter/filter_patt.cmx camlp5/o_keywords.cmx camlp5/pr_o.cmx *)
(*
 * Filter_patt (filter/filter): build_term_patt, which turns a term into
 * the OCaml pattern that matches its explode_term form (MatchTerm, or
 * MatchSequent for a sequent).  The filter uses it for the term
 * patterns of ML code in theories.
 *
 * Filter_patt is built only into the filter executable, as a native
 * object, so this test names it (and camlp5's OCaml printer, which prints
 * the patterns) on its second line, and run.sh links it with ocamlopt.
 * Each case gives the term built and either the pattern or the
 * Invalid_argument raised.
 *
 * On a bisect build at 008a9607e the theory build and the proof census
 * reach build_term_patt for a few operator shapes only: no String,
 * MString, MToken, MShape, MOperator, Var, Token or MLevel parameter,
 * no wildcard bterm, no sequent, and none of the refusals.
 *
 * The expected file is the output of the code.
 *)
open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Term_sig

let sym = Lm_symbol.add
let op s = Opname.make_opname [s]
let perv s = Opname.mk_opname s (Opname.mk_opname "Perv" Opname.nil_opname)
let fso v = mk_so_var_term (sym v) [] []
let num n = make_param (Number (Lm_num.num_of_int n))
let tm name params bterms = mk_term (mk_op (op name) params) bterms
let bt vars t = mk_bterm (List.map sym vars) t
let xconcl = mk_simple_term (perv "xconcl") []

let pr_patt p = Eprinter.apply Pcaml.pr_patt Pprintf.empty_pc p

let show name t =
   match Filter_patt.build_term_patt t with
      p -> Printf.printf "%s\n  term:    %s\n  pattern: %s\n" name (Simple_print.SimplePrint.string_of_term t) (pr_patt p)
    | exception Invalid_argument s ->
         Printf.printf "%s\n  term:    %s\n  refused: %S\n" name (Simple_print.SimplePrint.string_of_term t) s

let level v k = mk_level 0 [mk_level_var (sym v) k]

let () =
   show "a variable" (mk_var_term (sym "x"));
   show "no parameters, no subterms" (tm "foo" [] []);
   show "the number parameter 3" (tm "foo" [num 3] []);
   show "string parameter" (tm "foo" [make_param (String "s\"q")] []);
   show "meta parameters n s t sh op" (tm "foo" (List.map make_param [MNumber (sym "n"); MString (sym "s"); MToken (sym "t"); MShape (sym "sh"); MOperator (sym "o")]) []);
   show "wildcard names: _ and __x, but not _x" (tm "foo" (List.map make_param [MNumber (sym "_"); MString (sym "__x"); MToken (sym "_x")]) []);
   show "variable parameter" (tm "foo" [make_param (Var (sym "v"))] []);
   show "token parameter a!b" (tm "foo" [make_param (Token (Opname.make_opname ["b"; "a"]))] []);
   show "level parameter l" (tm "foo" [make_param (MLevel (level "l" 0))] []);
   show "level l+1 (refused)" (tm "foo" [make_param (MLevel (level "l" 1))] []);
   show "level max(1, l) (refused)" (tm "foo" [make_param (MLevel (mk_level 1 [mk_level_var (sym "l") 0]))] []);
   show "quote parameter (refused)" (tm "foo" [make_param Quote] []);
   show "parameter list (refused)" (tm "foo" [make_param (ParamList [num 1])] []);
   show "subterms: a, x.b, an xconcl" (tm "foo" [] [bt [] (fso "a"); bt ["x"; "_"] (fso "b"); bt [] xconcl]);
   show "a subterm that is not a variable (refused)" (tm "foo" [] [bt [] (tm "bar" [] [])])

let seq hyps concl =
   mk_sequent_term { sequent_args = tm "sequent_arg" [] []; sequent_hyps = SeqHyp.of_list hyps; sequent_concl = concl }

let () =
   show "sequent: x: A; H >- C" (seq [Hypothesis (sym "x", fso "A"); Context (sym "H", [], [])] (fso "C"));
   show "sequent with no context: x: A >- xconcl" (seq [Hypothesis (sym "x", fso "A")] xconcl);
   show "sequent: H; x: A >- C (refused)" (seq [Context (sym "H", [], []); Hypothesis (sym "x", fso "A")] (fso "C"));
   show "sequent whose conclusion is not a variable (refused)" (seq [] (tm "bar" [] []))
