(* Tacticals of Tacticals_boot.Tacticals that no unit test, theory build or
   proof replay ran (bisect at c013b0579 for the unit tests, 008a9607e for
   the build and the replay): labProgressT, untilFailT, whileT and untilT,
   ifT, ifOnHypT and ifThenOnHypT, keepingLabelT, ifAT, seqOnSameConclT,
   prefix_then_OnSameConclT, onAnyHypT and onAllMClausesOfAssumT.  The
   harness is test_tacticals_rest's: a "fan" tactic cuts the goal C into
   subgoals labelled wf (W), equality (E), assertion (P) and main (C); a
   recorder logs the label and goal of each subgoal it reaches and is idT; a
   counter tactic relabels its goal "n<k>" while its budget lasts and then
   fails.  Each case prints the labels of the subgoals left, or "refused",
   and the log.  progressT is run beside labProgressT as the control.  The
   expected file is the output of the code as written.

   Pinned as found:
   - onAnyHypT tries the hypotheses last first under orelseT, but its idT
     base is reached only with no hypotheses (or a context last), so when
     no hypothesis works it fails as onSomeHypT does.
   - progressT ignores labels, so whileT stops after one step of a tactic
     that only relabels.
   - the conclusion tacticals (seqOnSameConclT, prefix_then_OnSameConclT)
     raise on a goal that is not a sequent.
   Fixed after this test was written: labProgressT was inverted (with one
   subgoal it applied idT when goal and label were unchanged and failed
   when either changed); onAllMClausesOfAssumT tac n counted the
   hypotheses of assumption n but listed those of assumption n+1, so it
   skipped hypotheses and raised Failure "nth" on the last assumption. *)
open Refiner.Refiner
open Refiner.Refiner.TermType
open Tactic_boot
open Tacticals_boot.Tacticals
open Sequent_boot

let op s = Opname.make_opname [ s ]
let t name = Term.mk_simple_term (op name) []
let v = Lm_symbol.add
let sp = Simple_print.SimplePrint.string_of_term
let goal_c = t "C"

(* A sequent  x1 : A1; ...; xn : An >- C  *)
let mkseq hyps concl =
  TermMan.mk_sequent_term
    { sequent_args = TermMan.mk_xlist_term [];
      sequent_hyps = Term.SeqHyp.of_list (List.mapi (fun k h -> Term_sig.Hypothesis (v (Printf.sprintf "x%d" (k + 1)), t h)) hyps);
      sequent_concl = t concl }

let arg ?(assums = []) goal =
  { TacticInternalType.ref_goal = Refine.mk_msequent goal assums; ref_label = "main";
    ref_attributes = TacticInternal.attribute_info_of_raw_attributes [];
    ref_bookmark = Mp_resource.empty_bookmark; ref_sentinal = Tactic.null_sentinal }

let log = ref []
let say s = log := s :: !log
let name_of g = match Opname.dest_opname (Term.opname_of_term g) with s :: _ -> s | [] -> "?"
let short g = if TermMan.is_sequent_term g then ">-" ^ name_of (TermMan.concl g) else name_of g
let recT name = funT (fun p -> say (Printf.sprintf "%s@%s:%s" name (Sequent.label p) (short (Sequent.goal p))); idT)

let fanT =
  prefix_thenLT (cutT (t "W"))
    [ addHiddenLabelT "wf";
      prefix_thenLT (cutT (t "E")) [ addHiddenLabelT "equality"; prefix_thenLT (cutT (t "P")) [ addHiddenLabelT "assertion"; idT ] ] ]

let budget = ref 0
let countT =
  funT (fun p ->
      if !budget = 0 then (say "count:fail"; failWithT "countT")
      else (decr budget; say (Printf.sprintf "count@%s" (Sequent.label p)); addHiddenLabelT (Printf.sprintf "n%d" !budget)))

let run ?assums ?(goal = goal_c) ?(b = 0) name tac =
  log := []; budget := b;
  let r =
    match TacticInternal.refine tac (arg ?assums goal) with
    | gs, _ -> String.concat " " (List.map (fun (g : TacticInternalType.tactic_arg) -> g.ref_label) gs)
    | exception RefineError.RefineError (s, _) -> "refused (" ^ s ^ ")"
    | exception e -> "raises " ^ Printexc.to_string e
  in
  Printf.printf "%-40s left [%s]  log [%s]\n%!" name r (String.concat "; " (List.rev !log))

let is name g = short g = name

let () =
  print_endline "== progress";
  run "progressT idT" (progressT idT);
  run "labProgressT idT" (labProgressT idT);
  run "progressT (relabel)" (progressT (addHiddenLabelT "wf"));
  run "labProgressT (relabel)" (labProgressT (addHiddenLabelT "wf"));
  run "progressT (cut: two subgoals)" (progressT (cutT (t "W")));
  run "labProgressT (cut: two subgoals)" (labProgressT (cutT (t "W")));
  run "progressT (fail)" (progressT (failWithT "f"));
  run "labProgressT (fail)" (labProgressT (failWithT "f"));

  print_endline "== repetition";
  run ~b:3 "untilFailT count (3)" (untilFailT countT);
  run ~b:0 "untilFailT count (0)" (untilFailT countT);
  run ~b:3 "whileT (goal is C) count (3)" (whileT (is "C") countT);
  run ~b:3 "whileT (goal is D) count (3)" (whileT (is "D") countT);
  run ~b:3 "untilT (goal is C) count (3)" (untilT (is "C") countT);
  run ~b:3 "whileT (goal is C) idT" (whileT (is "C") (prefix_thenT idT (recT "w")));

  print_endline "== conditionals";
  run "ifT (label main) a b" (ifT (fun p -> Sequent.label p = "main") (recT "a") (recT "b"));
  run "ifT (label wf) a b" (ifT (fun p -> Sequent.label p = "wf") (recT "a") (recT "b"));
  let g3 = mkseq [ "A"; "B"; "A" ] "C" in
  let hypT name i = recT (Printf.sprintf "%s%d" name i) in
  run ~goal:g3 "ifOnHypT (is A) yes no 1" (ifOnHypT (is "A") (hypT "yes") (hypT "no") 1);
  run ~goal:g3 "ifOnHypT (is A) yes no 2" (ifOnHypT (is "A") (hypT "yes") (hypT "no") 2);
  run ~goal:g3 "ifThenOnHypT (is A) yes 3" (ifThenOnHypT (is "A") (hypT "yes") 3);
  run ~goal:g3 "ifThenOnHypT (is A) yes 2" (ifThenOnHypT (is "A") (hypT "yes") 2);

  print_endline "== labels";
  run "keepingLabelT (relabel wf)" (keepingLabelT (addHiddenLabelT "wf"));
  run "keepingLabelT fan" (keepingLabelT fanT);
  run "fan thenT ifAT rec" (prefix_thenT fanT (ifAT (recT "a")));

  (* The conclusion tacticals need a sequent goal: on C they raise. *)
  print_endline "== same conclusion";
  let gs = mkseq [ "A" ] "C" in
  run "seqOnSameConclT [] (goal C)" (seqOnSameConclT []);
  run "seqOnSameConclT [fan; a] (goal C)" (seqOnSameConclT [ fanT; recT "a" ]);
  (* A >- C  ==>  assertion: A >- W · main: A >- C, each a sequent *)
  let cutsT = prefix_thenLT (cutT (mkseq [ "A" ] "W")) [ addHiddenLabelT "assertion"; idT ] in
  run ~goal:gs "seqOnSameConclT [cut; a; b]" (seqOnSameConclT [ cutsT; recT "a"; recT "b" ]);
  run ~goal:gs "seqOnSameConclT [cut; cut; a]" (seqOnSameConclT [ cutsT; cutsT; recT "a" ]);
  run ~goal:gs "seqOnSameConclT [relabel; a]" (seqOnSameConclT [ addHiddenLabelT "wf"; recT "a" ]);
  run ~goal:gs "seqOnSameConclT [idT; idT; a]" (seqOnSameConclT [ idT; idT; recT "a" ]);
  run ~goal:gs "then_OnSameConclT cut a" (prefix_then_OnSameConclT cutsT (recT "a"));

  print_endline "== hypotheses";
  let pick ok name i = funT (fun p -> say (Printf.sprintf "%s%d" name i); if List.mem i ok then idT else failWithT "no") in
  run ~goal:g3 "onAnyHypT (works on 2)" (onAnyHypT (pick [ 2 ] "h"));
  run ~goal:g3 "onAnyHypT (works on none)" (onAnyHypT (pick [] "h"));
  run ~goal:g3 "onSomeHypT (works on none)" (onSomeHypT (pick [] "h"));
  run ~goal:(mkseq [] "C") "onAnyHypT (no hypotheses)" (onAnyHypT (pick [] "h"));
  let clause a i = recT (Printf.sprintf "c%d.%d" a i) in
  run ~assums:[ mkseq [ "A"; "B" ] "D"; mkseq [ "E" ] "F" ] "onAllMClausesOfAssumT 1" (onAllMClausesOfAssumT clause 1);
  run ~assums:[ mkseq [ "A"; "B" ] "D"; mkseq [ "E" ] "F" ] "onAllMClausesOfAssumT 2" (onAllMClausesOfAssumT clause 2);
  run ~assums:[ mkseq [ "A"; "B" ] "D" ] "onAllMClausesOfAssumT 1 (one assum)" (onAllMClausesOfAssumT clause 1);
  run ~assums:[ mkseq [ "A"; "B"; "G" ] "D"; mkseq [ "E" ] "F"; mkseq [] "H" ] "onAllMClausesOfAssumT 2 (three)" (onAllMClausesOfAssumT clause 2)
