(* Tacticals_boot and Tactic_boot, the lines the proof census runs and
   neither test_tacticals_rest nor test_tactic_attrs reaches (2026-11-11
   reach census, 4 lines each): whileProgressMT stopping when the main
   goal no longer changes, onSomeHypT on a goal that has hypotheses,
   get_thinning_arg's default, withoutIntT, and TacticInternal's
   get_resource, get_options and set_options.  The harness is
   test_tacticals_rest's: a recorder tactic logs the label and conclusion
   of each subgoal it reaches, and each case prints the log and the
   labels of the subgoals left, or "refused".  The expected file is the
   output of the code as written (2026-11-11). *)
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

let run ?assums ?(goal = goal_c) name tac =
  log := [];
  let r =
    match TacticInternal.refine tac (arg ?assums goal) with
    | gs, _ -> String.concat " " (List.map (fun (g : TacticInternalType.tactic_arg) -> g.ref_label) gs)
    | exception RefineError.RefineError (s, _) -> "refused (" ^ s ^ ")"
  in
  Printf.printf "%-34s left [%s]  log [%s]\n" name r (String.concat "; " (List.rev !log))

let seq hyps concl =
  TermMan.mk_sequent_term { sequent_args = t "arg"; sequent_hyps = Term.SeqHyp.of_list hyps; sequent_concl = concl }
let hseq = seq [ Term_sig.Hypothesis (Lm_symbol.add "x", t "A"); Term_sig.Hypothesis (Lm_symbol.add "y", t "B") ] goal_c

let () =
  print_endline "== whileProgressMT";
  run "whileProgressMT (cut P)" (whileProgressMT (funT (fun p -> say "step"; cutT (t "P"))));
  run "whileProgressMT rec" (whileProgressMT (recT "r"));
  print_endline "== onSomeHypT on x: A; y: B >- C";
  run ~goal:hseq "onSomeHypT (only 1 succeeds)" (onSomeHypT (fun i -> say (Printf.sprintf "try %d" i); if i = 1 then recT "h1" else failT));
  run ~goal:hseq "onSomeHypT (only 2 succeeds)" (onSomeHypT (fun i -> say (Printf.sprintf "try %d" i); if i = 2 then recT "h2" else failT));
  run ~goal:hseq "onSomeHypT (none succeeds)" (onSomeHypT (fun i -> say (Printf.sprintf "try %d" i); failT));
  print_endline "== arguments";
  let thin = funT (fun p -> say ("thin " ^ string_of_bool (get_thinning_arg p)); idT) in
  run "get_thinning_arg" thin;
  run "withBoolT thin false get_thinning_arg" (withBoolT "thin" false thin);
  let n = funT (fun p -> say ("n " ^ (match Sequent.get_int_arg p "n" with Some k -> string_of_int k | None -> "none")); idT) in
  run "withIntT n 3" (withIntT "n" 3 n);
  run "withIntT n 3 (withoutIntT n)" (withIntT "n" 3 (withoutIntT "n" n));
  run "withoutIntT n" (withoutIntT "n" n);
  run "withIntT n 3 (withIntT m 4 (withoutIntT m))" (withIntT "n" 3 (withIntT "m" 4 (withoutIntT "m" n)));
  print_endline "== TacticInternal";
  let a = arg goal_c in
  Printf.printf "get_resource calls its function with the bookmark's resource: %s\n"
    (TacticInternal.get_resource a (fun _ -> "called"));
  let a' = TacticInternal.set_options a (TacticInternal.get_options a) in
  Printf.printf "set_options (get_options): goal kept %b, label %s\n"
    (Refiner.Refiner.TermSubst.alpha_equal (Refine.msequent_goal a'.TacticInternalType.ref_goal) goal_c) a'.TacticInternalType.ref_label
