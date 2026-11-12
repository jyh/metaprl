(* Proof_boot.Proof: expand after the goal has changed, and
   initialize_goal, which the proof census runs and no unit test did
   (2026-11-12 census at one sha: find_leaf_guess's fallbacks, the
   hypothesis match tactic_arg_match, initialize_goal).  test_proof_expand
   expands unchanged proofs, where every leaf has an exact match; here
   set_goal changes the root's goal first (atoms with another assumption,
   another conclusion; sequents with a hypothesis added, reordered, removed
   or changed), so expand must place the stored sub-proofs by its fuzzy
   matches.  Each tree prints every address's goal (conclusion[assumptions])
   and whether it is a leaf.  The expected file is the output of the code
   as written (2026-11-12), never typed.  Recorded:
     - with another conclusion (C [A] -> E [A]), cutT C's stored sub-proof
       for C [A, C] matches neither new subgoal and is kept among the step's
       extras (rule_extras, which an address past the subgoals indexes: [3]
       of a two-subgoal step), so the work is not lost;
     - initialize_goal at [1] with its own goal replaces [1] in place; with
       another goal it leaves [1] an open leaf and the initialized node,
       carrying [1]'s old sub-proof, goes to the root step's extras ([3]).
       Its one caller, Proof_edit.initialize_goal, passes the root.
   Pinned as found, possibly a defect, not changed:
     - on sequent goals, the nthAssumT 1 step made for [2] (the goal with
       itself assumed) is attached at [1] (the goal with no assumption) and
       [2] becomes an open leaf: the hypothesis match reads the sequent's
       hypotheses, never the msequent's assumptions.
   A mutant forcing tactic_arg_match to false survives: the conclusion-only
   fallback then attaches the same sub-proofs here. *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Tactic_boot
open Tactic_boot_sig
open Proof_boot
open Tacticals_boot.Tacticals

let at n = mk_simple_term (Opname.make_opname [ n ]) []
let ex name = MLast.ExLid (Ploc.dummy, Ploc.VaVal name)
let st = function Proof.StatusBad -> "bad" | Proof.StatusIncomplete -> "incomplete" | Proof.StatusPartial -> "partial" | Proof.StatusComplete -> "complete"
let s t = String.concat " " (List.filter (( <> ) "") (String.split_on_char ' ' (String.map (fun c -> if c = '\n' then ' ' else c) (Simple_print.SimplePrint.string_of_term t))))
let gkey (a : TacticInternalType.tactic_arg) = let c, l = Refine.dest_msequent a.ref_goal in s c ^ "[" ^ String.concat "," (List.map s l) ^ "]"
let handler f = try Some (f ()) with RefineError.RefineError _ -> None
let nc p = let a, b = Proof.node_count p in Printf.sprintf "%d/%d" a b
let upd x = x
let rec tree p a ind =
  match Proof.goal p a with
  | exception RefineError.RefineError _ -> ()
  | g ->
      Printf.printf "%s%-6s %-30s %s\n" ind (if a = [] then "root" else String.concat "." (List.map string_of_int a)) (gkey g)
        (if Proof.is_leaf p a then "leaf" else "node");
      if not (Proof.is_leaf p a) then
        let rec kids i = match Proof.goal p (a @ [ i ]) with exception RefineError.RefineError _ -> () | _ -> tree p (a @ [ i ]) (ind ^ "  "); kids (i + 1) in
        kids 1
let show name p = Printf.printf "== %s: nodes %s, %s\n" name (nc p) (st (Proof.status p [])); tree p [] "  "
let refine p a name tac = Proof.refine upd p a name (ex name) tac

let () =
  let base = TacticInternal.debug_arg Mp_resource.empty_bookmark (at "A") in
  let a0 = { base with TacticInternalType.ref_goal = Refine.mk_msequent (at "C") [ at "A" ] } in
  (* C [A]: cutT C gives [1] C [A] (left open) and [2] C [A, C], closed by nthAssumT 2;
     [1] is refined by cutT A: [1.1] A [A] closed by nthAssumT 1, [1.2] C [A, A] left open *)
  let p = Proof.create a0 in
  let p = refine p [] "cutT C" (cutT (at "C")) in
  let p = refine p [ 2 ] "nthAssumT 2" (nthAssumT 2) in
  let p = refine p [ 1 ] "cutT A" (cutT (at "A")) in
  let p = refine p [ 1; 1 ] "nthAssumT 1" (nthAssumT 1) in
  show "built" p;
  let p1 = Proof.set_goal upd p [] (Refine.mk_msequent (at "C") [ at "D"; at "A" ]) in
  show "set_goal C [D, A]" p1;
  show "then expand" (Proof.expand upd handler p1 []);
  let p2 = Proof.set_goal upd p [] (Refine.mk_msequent (at "C") [ at "A"; at "D" ]) in
  show "set_goal C [A, D], then expand" (Proof.expand upd handler p2 []);
  let p3 = Proof.set_goal upd p [] (Refine.mk_msequent (at "C") []) in
  show "set_goal C [], then expand" (Proof.expand upd handler p3 []);
  let p4 = Proof.set_goal upd p [] (Refine.mk_msequent (at "E") [ at "A" ]) in
  show "set_goal E [A], then expand" (Proof.expand upd handler p4 []);
  print_endline "== initialize_goal";
  let marked = ref 0 in
  let init (a : TacticInternalType.tactic_arg) = incr marked; { a with TacticInternalType.ref_label = "init" } in
  let p5 = Proof.initialize_goal upd p [ 1 ] (Refine.mk_msequent (at "B") [ at "A"; at "D" ]) init in
  Printf.printf "init called %d time(s); label at [1]: %s\n" !marked (Proof.goal p5 [ 1 ]).TacticInternalType.ref_label;
  show "initialize_goal at [1] with B [A, D]" p5;
  let p6 = Proof.initialize_goal upd p [ 1 ] (Refine.mk_msequent (at "C") [ at "A" ]) init in
  Printf.printf "label at [1] after initialize_goal with its own goal C [A]: %s\n" (Proof.goal p6 [ 1 ]).TacticInternalType.ref_label;
  show "initialize_goal at [1] with its own goal C [A]" p6

(* Goals that are sequents: set_goal adds or removes a sequent hypothesis, so
   expand's leaves differ from the stored ones and are matched by their
   hypotheses (tactic_arg_match), in either direction. *)
let sq hyps c =
  TermMan.mk_sequent_term
    { TermType.sequent_args = at "sequent"; sequent_hyps = SeqHyp.of_list (List.map (fun (v, t) -> Term_sig.Hypothesis (Lm_symbol.add v, at t)) hyps);
      sequent_concl = at c }

let () =
  print_endline "== sequent goals";
  let base = TacticInternal.debug_arg Mp_resource.empty_bookmark (at "A") in
  let g0 = sq [ "x", "A" ] "C" in
  let a0 = { base with TacticInternalType.ref_goal = Refine.mk_msequent g0 [] } in
  let p = Proof.create a0 in
  (* cutT of the goal itself: [1] the goal, open; [2] the goal with itself assumed, closed by nthAssumT 1 *)
  let p = refine p [] "cutT (x: A >- C)" (cutT g0) in
  let p = refine p [ 2 ] "nthAssumT 1" (nthAssumT 1) in
  show "built (x: A >- C)" p;
  let ex_set name g = show name (Proof.expand upd handler (Proof.set_goal upd p [] (Refine.mk_msequent g [])) []) in
  ex_set "set_goal x: A; y: B >- C, then expand" (sq [ "x", "A"; "y", "B" ] "C");
  ex_set "set_goal y: B; x: A >- C, then expand" (sq [ "y", "B"; "x", "A" ] "C");
  ex_set "set_goal >- C, then expand" (sq [] "C");
  ex_set "set_goal x: B >- C, then expand" (sq [ "x", "B" ] "C")
