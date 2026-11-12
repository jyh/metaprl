(* The tacticals of Tacticals_boot.Tacticals that the proof census runs and
   no unit test did (2026-11-11 reach census, 63 lines): the label filters
   thenWT, thenET, thenPT, thenMLT, ifWT, ifMT (ifET is reached through thenET); seqOnMT; repeatMForT;
   orthenT; the assumption tacticals onSomeAssumT, onAllAssumT,
   onAllMAssumT and onSomeHypT; and the argument tacticals withT, selT,
   withIntT with get_with_arg, get_with_args, get_sel_arg, get_univ_arg and
   get_thinning_arg.  A "fan" tactic cuts the goal C into subgoals labelled
   wf (conclusion W), equality (E), assertion (P) and main (C); a recorder
   tactic logs the label and conclusion of each subgoal it reaches and is
   idT.  Each case prints the log and the labels of the subgoals left, or
   "refused".  The expected file is the output of the code as written
   (2026-11-11), never typed. *)
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
  print_endline "== label filters";
  run "fan" fanT;
  run "fan thenWT rec" (prefix_thenWT fanT (recT "r"));
  run "fan thenET rec" (prefix_thenET fanT (recT "r"));
  run "fan thenPT rec" (prefix_thenPT fanT (recT "r"));
  run "fan thenMT rec" (prefix_thenMT fanT (recT "r"));
  run "fan thenAT rec" (prefix_thenAT fanT (recT "r"));
  run "fan thenMLT [a]" (prefix_thenMLT fanT [ recT "a" ]);
  run "fan thenMLT [a; b] (one main)" (prefix_thenMLT fanT [ recT "a"; recT "b" ]);
  run "fan thenT ifWT rec" (prefix_thenT fanT (ifWT (recT "r")));
  run "fan thenT ifMT rec" (prefix_thenT fanT (ifMT (recT "r")));
  print_endline "== sequencing";
  run "seqOnMT [a; b]" (seqOnMT [ recT "a"; recT "b" ]);
  run "seqOnMT [fan; b]" (seqOnMT [ fanT; recT "b" ]);
  run "seqOnMT []" (seqOnMT []);
  run "repeatMForT 0 fan" (repeatMForT 0 fanT);
  run "repeatMForT 1 fan" (repeatMForT 1 fanT);
  run "repeatMForT 2 fan" (repeatMForT 2 fanT);
  run "repeatMT (cut P on main once)" (repeatMT (funT (fun p -> if Sequent.num_assums p = 0 then cutT (t "P") else failT)));
  run "failT orthenT rec" (prefix_orthenT failT (recT "r"));
  run "rec orthenT failT" (prefix_orthenT (recT "a") failT);
  run "fan orthenT rec" (prefix_orthenT fanT (recT "r"));
  print_endline "== assumptions";
  let assums = [ t "A1"; t "A2"; t "A3" ] in
  let at k i = funT (fun p -> say (Printf.sprintf "try %d on %s" i (Sequent.label p)); if i = k then idT else failT) in
  let any i = funT (fun _ -> say (Printf.sprintf "at %d" i); idT) in
  run ~assums "onSomeAssumT (succeeds at 2)" (onSomeAssumT (at 2));
  run ~assums "onSomeAssumT (succeeds nowhere)" (onSomeAssumT (at 9));
  run "onSomeAssumT, no assumptions" (onSomeAssumT (at 1));
  run ~assums "onAllAssumT" (onAllAssumT any);
  run ~assums "onAllMAssumT (each cuts)" (onAllMAssumT (fun i -> prefix_thenT (any i) (cutT (t "Q"))));
  run "onSomeHypT on a goal that is no sequent" (onSomeHypT any);
  print_endline "== argument tacticals";
  let show_args = funT (fun p ->
      let opt f = match f with Some x -> x | None -> "none" in
      say (Printf.sprintf "with=%s withs=%s sel=%s univ=%s thin=%b"
             (opt (Option.map sp (get_with_arg p)))
             (opt (Option.map (fun l -> string_of_int (List.length l)) (get_with_args p)))
             (opt (Option.map string_of_int (get_sel_arg p)))
             (opt (Option.map sp (get_univ_arg p)))
             (get_thinning_arg p));
      idT) in
  run "no arguments" show_args;
  run "withT X" (withT (t "X") show_args);
  run "withT X (withT Y ...)" (withT (t "X") (withT (t "Y") show_args));
  run "selT 2" (selT 2 show_args);
  run "withIntT sel 3" (withIntT "sel" 3 show_args);
  run "withT X, then on the subgoals" (withT (t "X") (prefix_thenMT fanT show_args))
