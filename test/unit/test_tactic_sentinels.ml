(* Tactic_boot's sentinels and rule tactics (tactics/proof/tactic_boot.ml
   get_theory, Tactic.sentinal_of_refiner, sentinal_of_refiner_object,
   create, compile_rule with labels, compile_ml_rule, tactic_of_rule) and
   the attribute and goal helpers only the proof census reached
   (2026-11-11 reach census: 28 lines of tactic_boot.ml reached by the
   census and by no unit test, the open PRs' tests included): get_strings,
   tactic_arg_alpha_equal_concl on sequents, argfun2T.
   A theory "tsent" is recorded (Theory.record_theory) with two primitive
   rules, r1  c --> r1{c}  then r2  c --> c --> r2{c}, justified in that
   order.  Each case runs a rule's tactic, through Tactic.tactic_of_rule,
   on a tactic_arg made by Tactic.create with the sentinel named, and
   prints the subgoals' labels and goals or the refusal; every outcome is
   the code's own (measured 2026-11-11).
   Fixed cases:
     - the theory's sentinel accepts both rules; the sentinel of the object
       r2 accepts r1 and refuses r2 (it is the refiner as r2 found it); of
       an object the theory lacks, it warns on stderr and accepts both;
     - a theory that was never recorded: the sentinel's function is
       declared lazy, but in this (unthreaded) build share calls it at
       once, so TAKING the sentinel is refused (get_theory);
     - compile_rule's labels name the subgoals (None keeps the goal's
       label) and too few labels are refused; compile_ml_rule keeps the
       goal's label on every subgoal;
     - get_strings returns every value under a name, in the order they
       were added (the outermost withStringT first);
     - tactic_arg_alpha_equal_concl compares conclusions: a sequent's
       hypotheses are ignored, and a sequent equals its bare conclusion.
   Not covered: the remote (threaded) refiner server, main_loop. *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Tactic_boot

let op s = Opname.make_opname [ s ]
let mk s ts = mk_simple_term (op s) ts
let c = mk "c" []
let sov x = mk_so_var_term (Lm_symbol.add x) [] []
let flat s = String.concat " " (List.filter (( <> ) "") (List.map String.trim (String.split_on_char '\n' s)))
let sp t = flat (Simple_print.SimplePrint.string_of_term t)

(* the theory: two primitive rules, r1 then r2 *)
let build = Refine.null_refiner "tsent"
let rule name subs =
  let mt = List.fold_right (fun s acc -> Term_sig.MetaImplies (Term_sig.MetaTheorem s, acc)) subs (Term_sig.MetaTheorem (mk name [ c ])) in
  let tac = Refine.create_rule build name Rewrite.empty_args_spec [] mt in
  Refine.prim_rule build name Rewrite.empty_args_spec [] mt (List.map (fun _ -> sov "e") subs) c;
  tac
let r1 = rule "r1" [ c ]
let r2 = rule "r2" [ c; c ]
let () = Theory.record_theory { Theory.thy_name = "tsent"; thy_group = "test"; thy_groupdesc = "test"; thy_refiner = Refine.refiner_of_build build }

let goal name = Refine.mk_msequent (mk name [ c ]) []
let show_sub (p : TacticInternalType.tactic_arg) = p.ref_label ^ ": " ^ sp (Refine.msequent_goal p.ref_goal)
let run label sent pre name =
  let arg = Tactic.create sent (goal name) Mp_resource.empty_bookmark in
  Printf.printf "%-52s %s\n%!" label
    (match TacticInternal.refine (Tactic.tactic_of_rule pre Rewrite.empty_rw_args []) arg with
     | gs, _ -> String.concat " || " (List.map show_sub gs)
     | exception RefineError.RefineError (n, _) -> "refused (" ^ n ^ ")"
     | exception e -> "EXCEPTION " ^ Printexc.to_string e)

let () =
  let p1 = Tactic.compile_rule build [ None ] r1 and p2 = Tactic.compile_rule build [ Some "wf"; None ] r2 in
  let thy = Tactic.sentinal_of_refiner "tsent" in
  run "theory sentinel, r1" thy p1 "r1";
  run "theory sentinel, r2 (labels wf, None)" thy p2 "r2";
  let obj = Tactic.sentinal_of_refiner_object "tsent" "r2" in
  run "sentinel of object r2, r1" obj p1 "r1";
  run "sentinel of object r2, r2" obj p2 "r2";
  let none = Tactic.sentinal_of_refiner_object "tsent" "nosuch" in
  run "sentinel of object nosuch (a warning), r2" none p2 "r2";
  Printf.printf "%-52s %s\n" "taking the sentinel of a theory never recorded"
    (match Tactic.sentinal_of_refiner "nosuchthy" with
     | s -> (try ignore (TacticInternal.refine (Tactic.tactic_of_rule p1 Rewrite.empty_rw_args []) (Tactic.create s (goal "r1") Mp_resource.empty_bookmark)); "taken; a rule then succeeds"
             with RefineError.RefineError (n, _) -> "taken; a rule is then refused (" ^ n ^ ")")
     | exception RefineError.RefineError (n, RefineError.StringStringError (m, x)) -> "refused (" ^ n ^ ": " ^ m ^ " " ^ x ^ ")");
  run "null_sentinal, r1" Tactic.null_sentinal p1 "r1";
  run "compile_rule with one label for two subgoals" thy (Tactic.compile_rule build [ Some "wf" ] r2) "r2";
  run "compile_rule with three labels for two subgoals" thy (Tactic.compile_rule build [ Some "a"; Some "b"; Some "c" ] r2) "r2";
  run "compile_ml_rule on r2" thy (Tactic.compile_ml_rule build r2) "r2";
  (* attributes and goals *)
  let arg = Tactic.create thy (goal "r1") Mp_resource.empty_bookmark in
  let read = ref [] in
  let tac = TacticInternal.withStringT "k" "x" (TacticInternal.withStringT "j" "y" (TacticInternal.withStringT "k" "z"
      (TacticInternal.funT (fun p -> read := [ TacticInternal.get_strings p "k"; TacticInternal.get_strings p "none" ]; TacticInternal.idT)))) in
  ignore (TacticInternal.refine tac arg);
  List.iter2 (fun l v -> Printf.printf "%-52s [%s]\n" l (String.concat "; " v))
    [ "get_strings k  (withStringT k x (j y (k z ...)))"; "get_strings none" ] !read;
  let seq hyps concl = mk_sequent_term { TermType.sequent_args = mk_xlist_term [];
      sequent_hyps = SeqHyp.of_list (List.mapi (fun k h -> Term_sig.Hypothesis (Lm_symbol.add ("x" ^ string_of_int k), h)) hyps); sequent_concl = concl } in
  let with_goal t = { arg with TacticInternalType.ref_goal = Refine.mk_msequent t [] } in
  let eqc a b = string_of_bool (TacticInternal.tactic_arg_alpha_equal_concl (with_goal a) (with_goal b)) in
  Printf.printf "%-52s %s\n" "alpha_equal_concl  c |- r1{c}  vs  |- r1{c}" (eqc (seq [ c ] (mk "r1" [ c ])) (seq [] (mk "r1" [ c ])));
  Printf.printf "%-52s %s\n" "alpha_equal_concl  |- r1{c}  vs  r1{c}" (eqc (seq [] (mk "r1" [ c ])) (mk "r1" [ c ]));
  Printf.printf "%-52s %s\n" "alpha_equal_concl  |- r1{c}  vs  |- r2{c}" (eqc (seq [] (mk "r1" [ c ])) (seq [] (mk "r2" [ c ])));
  let got = ref "" in
  let t = TacticInternal.argfun2T (fun x y p -> got := x ^ y ^ " " ^ p.TacticInternalType.ref_label; TacticInternal.idT) "a" "b" in
  ignore (TacticInternal.refine t arg);
  Printf.printf "%-52s %s\n" "argfun2T (fun x y p -> ...) \"a\" \"b\"" !got
