(* Conversionals_boot.Conversionals: the rewrite tactics on sequent clauses
   and assumptions, and two conversionals, which the proof census runs and
   no unit test did (2026-11-11 reach census, 17 lines): rw, rwc, rwcAll,
   rwAll, rwAllAll, their higherC forms (rwh, rwch, rwhAll, rwchAll,
   rwhAllAll) and applyAllC forms (rwa, rwaAll, rwaAllAll), allSubThenC and
   sweepUpFailC.  The goal is the sequent x: g{a}; y: f{a; b} >- g{f{a; b}}
   with one assumption, the sequent z: g{c} >- f{c; a}; the conversions are
   ung (g{'a} --> 'a) and swap (f{'a; 'b} --> f{'b; 'a}).  Each case
   prints the subgoals (conclusion, then the assumptions) or "refused".
   The expected file is the output of the code as written (2026-11-11),
   never typed. *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Tactic_boot
open Rewrite_boot.Rewrite
open Conversionals_boot.Conversionals

let op s = Opname.make_opname [ s ]
let sov x = TermMan.mk_so_var_term (Lm_symbol.add x) [] []
let c0 s = mk_simple_term (op s) []
let g x = mk_simple_term (op "g") [ x ]
let f x y = mk_simple_term (op "f") [ x; y ]
let a = c0 "a" and b = c0 "b" and c = c0 "c"
let seq hyps concl =
  TermMan.mk_sequent_term
    { TermType.sequent_args = c0 "arg";
      sequent_hyps = SeqHyp.of_list (List.map (fun (x, t) -> Term_sig.Hypothesis (Lm_symbol.add x, t)) hyps);
      sequent_concl = concl }

let swap = create_iform "swap" false (f (sov "a") (sov "b")) (f (sov "b") (sov "a"))
let ung = create_iform "ung" false (g (sov "a")) (sov "a")

let goal = seq [ "x", g a; "y", f a b ] (g (f a b))
let assum = seq [ "z", g c ] (f c a)
let p0 = TacticInternal.debug_arg Mp_resource.empty_bookmark a
let arg ?(goal = goal) () = { p0 with TacticInternalType.ref_goal = Refine.mk_msequent goal [ assum ] }

let flat s = String.concat " " (List.filter (( <> ) "") (List.map String.trim (String.split_on_char '\n' s)))
let sp t = flat (Simple_print.SimplePrint.string_of_term t)

let run ?goal name tac =
  let r =
    match TacticInternal.refine tac (arg ?goal ()) with
    | gs, _ ->
        String.concat "  ||  " (List.map (fun (p : TacticInternalType.tactic_arg) ->
            let cl, asl = Refine.dest_msequent p.ref_goal in
            sp cl ^ "  with  " ^ String.concat " ; " (List.map sp asl)) gs)
    | exception RefineError.RefineError (s, _) -> "refused (" ^ s ^ ")"
    | exception e -> "EXCEPTION " ^ Printexc.to_string e
  in
  Printf.printf "%-28s %s\n" name r

let () =
  print_endline "== clauses of the goal (rw, rwc)";
  run "rw ung 0 (the conclusion)" (rw ung 0);
  run "rw ung 1 (x: g{a})" (rw ung 1);
  run "rw swap 2 (y: f{a; b})" (rw swap 2);
  run "rw ung 2 (no g there)" (rw ung 2);
  run "rw ung 5 (no such clause)" (rw ung 5);
  run "rwc ung 1 1 (assumption 1)" (rwc ung 1 1);
  run "rwc swap 1 0" (rwc swap 1 0);
  print_endline "== every subterm (rwcAll, rwAll, rwAllAll)";
  run "rwAll ung" (rwAll ung);
  run "rwAll (tryC ung)" (rwAll (tryC ung));
  run "rwcAll (tryC ung) 1" (rwcAll (tryC ung) 1);
  run "rwAllAll (tryC ung)" (rwAllAll (tryC ung));
  print_endline "== higherC forms";
  run "rwh ung 0" (rwh ung 0);
  run "rwch ung 1 0" (rwch ung 1 0);
  run "rwhAll ung" (rwhAll ung);
  run "rwchAll ung 1" (rwchAll ung 1);
  run "rwhAllAll ung" (rwhAllAll ung);
  print_endline "== applyAllC forms";
  run "rwa [ung; swap] 0" (rwa [ ung; swap ] 0);
  run "rwa [ung; swap] 2" (rwa [ ung; swap ] 2);
  run "rwaAll [ung]" (rwaAll [ ung ]);
  run "rwaAllAll [ung]" (rwaAllAll [ ung ]);
  print_endline "== allSubThenC, sweepUpFailC";
  let gga = seq [] (g (g a)) in
  run ~goal:gga "allSubThenC ung idC on g{g{a}}" (rw (allSubThenC ung idC) 0);
  run "allSubThenC ung idC on g{f{a;b}}" (rw (allSubThenC ung idC) 0);
  run ~goal:gga "sweepUpFailC ung on g{g{a}}" (rw (sweepUpFailC ung) 0);
  run ~goal:gga "sweepUpC ung on g{g{a}}" (rw (sweepUpC ung) 0)
