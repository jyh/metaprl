(* Tacticals_boot.completeMT, which no theory, census or unit test used
   (2026-11-15 profile): completeMT tac is tac thenMT failWithT, so it
   refuses when tac leaves a subgoal labelled main and accepts one that
   leaves only other labels.  test_tacticals_rest's harness: the fan tactic
   cuts C into wf, equality, assertion and main subgoals.
   The expected file is the output of the code as written, never typed. *)
open Refiner.Refiner
open Refiner.Refiner.TermType
open Tactic_boot
open Tacticals_boot.Tacticals
open Sequent_boot

let op s = Opname.make_opname [ s ]
let t name = Term.mk_simple_term (op name) []
let sp = Simple_print.SimplePrint.string_of_term
let goal_c = t "C"

let arg ?(assums = []) goal =
  { TacticInternalType.ref_goal = Refine.mk_msequent goal assums; ref_label = "main";
    ref_attributes = TacticInternal.attribute_info_of_raw_attributes [];
    ref_bookmark = Mp_resource.empty_bookmark; ref_sentinal = Tactic.null_sentinal }

let log = ref []
let say s = log := s :: !log
let recT name = funT (fun p -> say (Printf.sprintf "%s@%s:%s" name (Sequent.label p) (sp (Sequent.goal p))); idT)

(* C  ==>  wf: W · equality: E · assertion: P · main: C *)
let fanT =
  prefix_thenLT (cutT (t "W"))
    [ addHiddenLabelT "wf";
      prefix_thenLT (cutT (t "E")) [ addHiddenLabelT "equality"; prefix_thenLT (cutT (t "P")) [ addHiddenLabelT "assertion"; idT ] ] ]

let run ?assums name tac =
  log := [];
  let r =
    match TacticInternal.refine tac (arg ?assums goal_c) with
    | gs, _ -> String.concat " " (List.map (fun (g : TacticInternalType.tactic_arg) -> g.ref_label) gs)
    | exception RefineError.RefineError (s, _) -> "refused (" ^ s ^ ")"
  in
  Printf.printf "%-34s left [%s]  log [%s]\n" name r (String.concat "; " (List.rev !log))

let () =
  run "completeMT idT" (completeMT idT);
  run "completeMT fan (main C left)" (completeMT fanT);
  run "completeMT (fan thenMT nthAssumT 1), C assumed" ~assums:[ goal_c ] (completeMT (prefix_thenMT fanT (nthAssumT 1)));
  run "completeMT (nthAssumT 1), C assumed" ~assums:[ goal_c ] (completeMT (nthAssumT 1));
  run "completeMT (addHiddenLabelT wf)" (completeMT (addHiddenLabelT "wf"))
