(* Proof_boot.replace_child's Pending arm, which no unit test, theory
   build or proof census reached (2026-11-15 rank).  Proof.post caches a
   Pending node for the posted goal, and get_cache hands the cache back
   as proofs; a refine on such an entry at [1] folds the new child up
   through its root, the Pending node (fold_up_proof), which forces it and
   rebuilds the rule box.  E by cutT F is posted, so goal E has two
   entries: the Pending node (entry 0) and the rule box the refine cached
   (entry 1).  Each entry is pasted at [1] of D by cutT E, then refined
   itself at [1].  The expected file is the output of the code as written
   (2026-11-15), never typed.
   This is the only route: get_cache has no caller outside the tests,
   post stores the Pending node in the cache only (the tree gets a Locked
   node), and paste and copy go through replace_goal_ext, which turns
   every node but a Goal or a RuleBox into Unjustified.
   Pinned as found: pasting the Pending entry gives an Unjustified node
   (its justification is dropped), where pasting the rule-box entry keeps
   the rule.  The arm's other cases, a node select_child refuses (Goal,
   Identity, Annotate, Extract, Unjustified, and Wrapped at an index other
   than 0), are not reachable: fold_up_proof selects the same child
   first, and select_child refuses the same nodes. *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Tactic_boot
open Tactic_boot_sig
open Proof_boot
open Tacticals_boot.Tacticals

let at n = mk_simple_term (Opname.make_opname [ n ]) []
let ex name = MLast.ExLid (Ploc.dummy, Ploc.VaVal name)
let id x = x
let st = function Proof.StatusBad -> "bad" | Proof.StatusIncomplete -> "incomplete" | Proof.StatusPartial -> "partial" | Proof.StatusComplete -> "complete"
let rec expr = function
  | Proof.ExprGoal -> "goal" | Proof.ExprIdentity -> "identity" | Proof.ExprUnjustified -> "unjustified"
  | Proof.ExprAnnotate -> "annotate" | Proof.ExprExtract _ -> "extract"
  | Proof.ExprCompose e -> "compose(" ^ expr e ^ ")" | Proof.ExprWrapped _ -> "wrapped"
  | Proof.ExprRule (text, _) -> "rule " ^ text
let info p a = try let i = Proof.info p a in Printf.sprintf "%s/%d" (expr i.Proof.step_expr) (List.length i.Proof.step_subgoals) with RefineError.RefineError (n, _) -> "refused (" ^ n ^ ")"
let show p =
  let r, n = Proof.node_count p in
  Printf.sprintf "nodes (%d, %d), %s, root %s" r n (st (Proof.status p [])) (info p [])

let goal c hyps =
  let base = TacticInternal.debug_arg Mp_resource.empty_bookmark (at c) in
  { base with TacticInternalType.ref_goal = Refine.mk_msequent (at c) (List.map at hyps) }
let fresh c hyps = Proof.create (goal c hyps)
let refine p a text tac = Proof.refine id p a text (ex text) tac

let cache name p a =
  let l = try Proof.get_cache p a with RefineError.RefineError (n, _) -> (Printf.printf "  %-26s refused (%s)\n" name n; [ ]) in
  Printf.printf "  %-26s %d entr%s\n" name (List.length l) (if List.length l = 1 then "y" else "ies");
  List.iteri (fun i q -> Printf.printf "    %d: %s\n" i
      (try show q with RefineError.RefineError (n, _) -> "raised RefineError (" ^ n ^ ")")) l

let line name f = Printf.printf "  %-26s %s\n" name (try f () with RefineError.RefineError (n, _) -> "refused (" ^ n ^ ")" | Invalid_argument s -> "Invalid_argument " ^ s)

let () =
  print_endline "E by cutT F, posted; D by cutT E";
  let e = refine (fresh "E" []) [] "cutT F" (cutT (at "F")) in
  line "E" (fun () -> show e);
  ignore (Proof.post (fun () -> e) []);
  let d = refine (fresh "D" []) [] "cutT E" (cutT (at "E")) in
  line "D" (fun () -> show d);
  let cached = Proof.get_cache d [ 1 ] in
  Printf.printf "  %-26s %d\n" "cached for D [1]" (List.length cached);
  List.iteri (fun k c ->
      Printf.printf "entry %d: %s\n" k (try show c with RefineError.RefineError (n, _) -> "refused (" ^ n ^ ")");
      line "pasted at D [1]" (fun () -> info (Proof.paste id d [ 1 ] c) [ 1 ]);
      print_endline "  refine the entry itself at [1] (F by cutT G)";
      line "result" (fun () -> show (refine c [ 1 ] "cutT G" (cutT (at "G"))));
      line "result [1]" (fun () -> info (refine c [ 1 ] "cutT G" (cutT (at "G"))) [ 1 ]);
      line "the entry after" (fun () -> show c)) cached
