(* Dform's default printing of sequents, meta-terms, second-order variables
   and contexts, through the null base (no theory's forms): format_sequent
   and its format_hyp, format_mterm over every meta-term constructor, and
   print_term's conversion of free variables, second-order variables and
   context terms into their display terms.  No test printed a sequent or a
   meta-term, and no theory build or proof replay uses the null base
   (bisect at c013b0579 for the unit tests, 008a9607e for the build and
   the replay: format_hyp 48 points, format_mterm 17 and print_term's
   conversions unreached).

   Each case prints the term at the default width and at width 20, so the
   breaks show.  The expected file is the output of the code as written.
   Pinned as found:
   - meta-terms are printed with no parentheses, so (A --> B) --> C and
     A --> (B --> C) print alike, as do (A <--> B) --> C and
     A <--> (B --> C);
   - a labelled meta-term prints with a leading space;
   - a hypothesis prints its variable only when the variable is used
     later (the term form drops an unused binding), and one with no
     variable prints its term alone;
   - a Context entry reaches format_hyp as a hypothesis with an empty
     variable whose term is the display form's df_context wrapper, and
     prints as <...>; such a hypothesis built by hand prints the same;
   - a free variable prints with "<|!|>", a second-order variable or a
     context with no contexts with "<|!!|>". *)
open Lm_symbol
open Opname
open Term_sig
open Refiner.Refiner
open TermType
open Term
open TermMan
open Dform

let op s = mk_opname s nil_opname
let c s = mk_simple_term (op s) []
let f s l = mk_simple_term (op s) l
let v s = mk_var_term (Lm_symbol.add s)
let sov s ts = mk_so_var_term (Lm_symbol.add s) [] ts
let sovc s conts ts = mk_so_var_term (Lm_symbol.add s) (List.map Lm_symbol.add conts) ts

let seq ?(args = mk_xlist_term []) hyps concl =
  mk_sequent_term { sequent_args = args; sequent_hyps = SeqHyp.of_list hyps; sequent_concl = concl }
let hyp x t = Hypothesis (Lm_symbol.add x, t)
let cont x conts ts = Context (Lm_symbol.add x, List.map Lm_symbol.add conts, ts)

(* The display form's own context wrapper, as Dform builds it for a
   context term (dform.ml, print_term). *)
let df_context x = mk_term (mk_op (mk_opname "df_context" (mk_opname "Base_dform" nil_opname)) []) [ mk_bterm [] (sov x []) ]

let attempt f = try f () with e -> "EXCEPTION " ^ Printexc.to_string e

let show name t =
  Printf.printf "== %s\n%s\n" name (attempt (fun () -> string_of_term null_base t));
  Printf.printf "-- width 20\n%s\n" (attempt (fun () ->
      let buf = Lm_rformat.new_buffer () in
        format_term null_base buf t;
        Lm_rformat_text.print_text_string 20 buf))

let show_m name m =
  Printf.printf "== %s\n%s\n" name (attempt (fun () -> string_of_mterm null_base m))

let () =
  print_endline "SEQUENTS";
  show "no hypotheses" (seq [] (c "C"));
  show "one named hypothesis" (seq [ hyp "x" (c "A") ] (c "C"));
  show "three hypotheses" (seq [ hyp "x" (c "A"); hyp "y" (f "B" [ v "x" ]); hyp "z" (c "D") ] (f "C" [ v "x"; v "y" ]));
  show "a hypothesis with no variable" (seq [ hyp "" (c "A") ] (c "C"));
  show "a context" (seq [ cont "H" [] []; hyp "x" (c "A") ] (c "C"));
  show "a context with contexts and arguments" (seq [ cont "J" [ "H" ] [ v "x" ] ] (c "C"));
  show "a df_context hypothesis" (seq [ hyp "" (df_context "K") ] (c "C"));
  show "sequent arguments" (seq ~args:(mk_xlist_term [ c "arg1"; c "arg2" ]) [ hyp "x" (c "A") ] (c "C"));
  show "a sequent in a hypothesis" (seq [ hyp "x" (seq [ hyp "y" (c "B") ] (c "B")) ] (c "C"));
  show "a long sequent" (seq (List.init 6 (fun i -> hyp (Printf.sprintf "x%d" i) (c (Printf.sprintf "Hypothesis%d" i)))) (c "Conclusion"));

  print_endline "VARIABLES";
  show "a variable" (v "x");
  show "a second-order variable" (sov "F" [ v "x"; c "a" ]);
  show "a second-order variable with contexts" (sovc "G" [ "H"; "J" ] [ v "x" ]);
  show "a context term" (mk_context_term (Lm_symbol.add "H") (c "body") [ Lm_symbol.add "J" ] [ v "x" ]);
  show "a free variable" (mk_term (mk_op (op "wrap") []) [ mk_bterm [ Lm_symbol.add "y" ] (v "y") ]);

  print_endline "META-TERMS";
  show_m "MetaTheorem" (MetaTheorem (c "A"));
  show_m "MetaImplies" (MetaImplies (MetaTheorem (c "A"), MetaTheorem (c "B")));
  show_m "MetaFunction" (MetaFunction (c "f", MetaTheorem (c "A"), MetaTheorem (c "B")));
  show_m "MetaIff" (MetaIff (MetaTheorem (c "A"), MetaTheorem (c "B")));
  show_m "MetaLabeled" (MetaLabeled ("lab", MetaTheorem (c "A")));
  let a, b, cc = MetaTheorem (c "A"), MetaTheorem (c "B"), MetaTheorem (c "C") in
  show_m "(A --> B) --> C" (MetaImplies (MetaImplies (a, b), cc));
  show_m "A --> (B --> C)" (MetaImplies (a, MetaImplies (b, cc)));
  show_m "(A <--> B) --> C" (MetaImplies (MetaIff (a, b), cc));
  show_m "A <--> (B --> C)" (MetaIff (a, MetaImplies (b, cc)));
  show_m "nested" (MetaImplies (MetaLabeled ("h", MetaTheorem (seq [ hyp "x" (c "A") ] (c "B"))),
                                MetaIff (MetaFunction (v "g", MetaTheorem (c "A"), MetaTheorem (c "B")), MetaTheorem (c "C"))))
