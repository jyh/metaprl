(* Proof_boot's proof cache: Proof.post (the editor posts after every edit,
   support/shell/proof_edit.ml update_fun) and Proof.get_cache.  No unit
   test read the cache back after the posted proof changed, so post's
   Pending node (compute_ext) was never forced.  post f addr stores, under
   the goal at addr, a Pending node that calls f again when it is read: if
   the node at addr in the new proof has the same goal it is the answer,
   otherwise the node seen before.  Each case prints the cache for a goal,
   one line per entry (a refine also caches its rule box, so a refined and
   posted goal has two).  The expected file is the output of the code as
   written, never typed.
   When the posted address no longer exists in the new proof, reading the
   entry gives the node seen before.  It raised RefineError
   "Proof_boot.index" while compute_ext called index, which turns the
   ProofRefineError its handler catches into a RefineError. *)
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
  (* 1: post a refined root; the cache answers for the same goal only *)
  print_endline "post at [] (A by nthAssumT 1, A in hyps)";
  let p = refine (fresh "A" [ "A" ]) [] "nthAssumT 1" (nthAssumT 1) in
  line "proof" (fun () -> show p);
  let q = Proof.post (fun () -> p) [] in
  line "post returns" (fun () -> show q);
  cache "get_cache A|A" (fresh "A" [ "A" ]) [];
  cache "get_cache A|-" (fresh "A" []) [];
  cache "get_cache B|A" (fresh "B" [ "A" ]) [];
  (* 2: post at a subgoal *)
  print_endline "post at [1] (D by cutT E, subgoal 1 is E)";
  let p = refine (fresh "D" []) [] "cutT E" (cutT (at "E")) in
  line "proof" (fun () -> show p);
  line "goal [1]" (fun () -> info p [ 1 ]);
  let q = Proof.post (fun () -> p) [ 1 ] in
  line "post returns" (fun () -> show q);
  cache "get_cache E|-" (fresh "E" []) [];
  cache "get_cache p [1]" p [ 1 ];
  (* 3: the posted function is called again: same goal => the new proof *)
  print_endline "re-read after the proof changes (goal F)";
  let r = ref (fresh "F" [ "F" ]) in
  ignore (Proof.post (fun () -> !r) []);
  cache "unchanged" (fresh "F" [ "F" ]) [];
  r := refine (fresh "F" [ "F" ]) [] "nthAssumT 1" (nthAssumT 1);
  cache "same goal, refined" (fresh "F" [ "F" ]) [];
  r := refine (fresh "G" [ "G" ]) [] "nthAssumT 1" (nthAssumT 1);
  cache "goal changed to G" (fresh "F" [ "F" ]) [];
  (* 4: the address stops existing *)
  print_endline "address [1] disappears (goal H by cutT K)";
  let r = ref (refine (fresh "H" []) [] "cutT K" (cutT (at "K"))) in
  ignore (Proof.post (fun () -> !r) [ 1 ]);
  cache "posted" (fresh "K" []) [];
  r := fresh "H" [];
  cache "after unrefine" (fresh "K" []) [];
  (* 5: posting twice *)
  print_endline "post twice (goal M)";
  let p = refine (fresh "M" [ "M" ]) [] "nthAssumT 1" (nthAssumT 1) in
  ignore (Proof.post (fun () -> p) []);
  ignore (Proof.post (fun () -> fresh "M" [ "M" ]) []);
  cache "get_cache M|M" (fresh "M" [ "M" ]) []
