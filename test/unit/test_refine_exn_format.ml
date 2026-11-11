(* Refine_exn.format_refine_error, the printer every refusal in the proof
   editor goes through, on the error forms only the proof census printed
   (2026-11-11 reach census: 21 lines of refine_exn.ml reached by the census
   and by no unit test): StringIntError, StringStringError, StringVarError,
   StringTermError, and RewriteBadMatch with each match_type -- ParamMatch,
   VarMatch, TermMatch, TermMatch2, BTermMatch and HypMatch, whose
   hypotheses print as Context(...) or Hypothesis(...), the latter without
   its variable when the variable's name is empty.
   Each error is printed with Dform.null_base at width 200 (one line) and
   at width 24 (to show where it breaks), and through format_exn as a
   RefineError; the text is the code's own (measured 2026-11-11).
   Pinned as found, not changed: HypMatch prints its hypotheses with no
   separator between them (...)Hypothesis(...), and a Context's subterms
   are each followed by a newline, so its ")" starts a line. *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.RefineError

let op s = Opname.make_opname [ s ]
let v = Lm_symbol.add
let a = mk_simple_term (op "a") []
let g x = mk_simple_term (op "g") [ x ]
let print w f = let buf = Lm_rformat.new_buffer () in f buf; Lm_rformat_text.print_text_string w buf

let hyps = SeqHyp.of_list [ Term_sig.Context (v "H", [ v "J" ], [ a ]); Term_sig.Hypothesis (v "x", g a); Term_sig.Hypothesis (v "", a) ]
let errors =
  [ "StringIntError", StringIntError ("depth", 3);
    "StringStringError", StringStringError ("no such rule", "and_intro");
    "StringVarError", StringVarError ("free variable", v "y");
    "StringTermError", StringTermError ("not a redex", g a);
    "BadMatch ParamMatch", RewriteBadMatch (ParamMatch (make_param (Term_sig.Number (Lm_num.num_of_int 7))));
    "BadMatch VarMatch", RewriteBadMatch (VarMatch (v "z"));
    "BadMatch TermMatch", RewriteBadMatch (TermMatch (g a));
    "BadMatch TermMatch2", RewriteBadMatch (TermMatch2 (g a, a));
    "BadMatch BTermMatch", RewriteBadMatch (BTermMatch (mk_bterm [ v "x" ] (g (mk_var_term (v "x")))));
    "BadMatch HypMatch", RewriteBadMatch (HypMatch hyps) ]

let () =
  List.iter (fun (name, e) ->
      Printf.printf "%s\n  w200 %S\n  w24  %S\n" name
        (print 200 (fun buf -> Refine_exn.format_refine_error Dform.null_base buf "rw" e))
        (print 24 (fun buf -> Refine_exn.format_refine_error Dform.null_base buf "rw" e));
      let x = print 200 (fun buf -> Refine_exn.format_exn Dform.null_base buf (RefineError ("rw", e))) in
      Printf.printf "  format_exn %S\n" x)
    errors
