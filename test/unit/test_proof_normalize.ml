(* Proof_boot's normalizer of composed steps (normalize, replace_goal,
   replace_subg_aux) on sixteen composite tactics refined at a fresh root,
   then read through Proof.info (which normalizes): the step, its
   find_subgoal answers, and the extract's own tree at addresses [0],
   [0.k], [0.k.j].  Nothing reached replace_goal's or replace_subg_aux's
   Wrapped, Identity and Annotate arms (2026-11-16 rank).  Two things make
   them reachable: prefix_thenT drops idT itself by physical equality, so
   the identity step here is i p = idT p; and a rebuild arm runs only when
   the goal object changes, so setLabelT (a new goal record) is composed
   on either side.
   Reach probes (an arm made to raise) fire in replace_goal's Wrapped,
   Identity and Annotate arms, replace_subg_aux's Wrapped and Annotate
   arms and normalize's Wrapped arm; NOT in replace_subg_aux's Identity
   arm (stated: no shape here makes all-identity subgoals under a changed
   goal).
   Read from the output: after setLabelT l thenT t, the step's own goal
   reads label l (setLabelT's extract is the identity of the relabeled
   goal, and normalization makes it the composition's goal).
   The expected file is the output of the code as written (2026-11-16),
   never typed. *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Tactic_boot
open Tactic_boot_sig
open Proof_boot
open Tacticals_boot.Tacticals

let at n = mk_simple_term (Opname.make_opname [ n ]) []
let ex name = MLast.ExLid (Ploc.dummy, Ploc.VaVal name)
let sa a = "[" ^ String.concat "." (List.map string_of_int a) ^ "]"
let try_s f = try f () with RefineError.RefineError (n, _) -> "refused (" ^ n ^ ")" | Invalid_argument m -> "Invalid_argument " ^ m | e -> "raised " ^ Printexc.to_string e
let s t = Simple_print.SimplePrint.string_of_term t
let gkey (a : TacticInternalType.tactic_arg) = let c, l = Refine.dest_msequent a.ref_goal in a.ref_label ^ ":" ^ s c ^ "[" ^ String.concat "," (List.map s l) ^ "]"
let root () =
  let base = TacticInternal.debug_arg Mp_resource.empty_bookmark (at "A") in
  Proof.create { base with TacticInternalType.ref_goal = Refine.mk_msequent (at "A") [] }
let rf p a name tac = Proof.refine (fun x -> x) p a name (ex name) tac
let fs p a i = try_s (fun () -> sa (Proof.find_subgoal p a i))
let show tag p a =
  let i = Proof.info p a in
  Printf.printf "%s at %s: goal %s, %d subgoals, node_count %d/%d\n" tag (sa a) (gkey (Proof.goal p a)) (List.length i.Proof.step_subgoals)
    (fst (Proof.node_count p)) (snd (Proof.node_count p));
  for k = 0 to List.length i.Proof.step_subgoals + 1 do
    Printf.printf "  find_subgoal %d: %s\n" k (fs p a k)
  done;
  List.iteri (fun k l -> Printf.printf "  subgoal %d: %s\n" (k + 1) (String.concat " | " (List.map (fun q -> gkey (Proof.goal q [])) l))) i.Proof.step_subgoals

let w t = TacticInternal.wrapT (IntArgList ("w", 7)) t
let cut x = cutT (at x)
let ann = addTermT "n" (at "N")
(* an identity step that prefix_thenT cannot drop: it removes idT itself by physical equality *)
let i p = idT p
let cases = [
  "i thenT i", prefix_thenT i i;
  "i thenT addTermT", prefix_thenT i ann;
  "i thenT wrapT (cutT X)", prefix_thenT i (w (cut "X"));
  "wrapT (cutT X) thenT i", prefix_thenT (w (cut "X")) i;
  "addTermT thenT i", prefix_thenT ann i;
  "addTermT thenT cutT X", prefix_thenT ann (cut "X");
  "wrapT (i thenT cutT X)", w (prefix_thenT i (cut "X"));
  "wrapT (cutT X thenT i)", w (prefix_thenT (cut "X") i);
  "(i thenT cutT X) thenT i", prefix_thenT (prefix_thenT i (cut "X")) i;
  "cutT X thenLT [i; wrapT (cutT Y)]", prefix_thenLT (cut "X") [ i; w (cut "Y") ];
  (* setLabelT makes a NEW goal record, so the normalizer's rebuild arms run *)
  "setLabelT l thenT i", prefix_thenT (TacticInternal.setLabelT "l") i;
  "i thenT setLabelT l", prefix_thenT i (TacticInternal.setLabelT "l");
  "setLabelT l thenT wrapT (cutT X)", prefix_thenT (TacticInternal.setLabelT "l") (w (cut "X"));
  "wrapT (cutT X) thenT setLabelT l", prefix_thenT (w (cut "X")) (TacticInternal.setLabelT "l");
  "addTermT thenT setLabelT l", prefix_thenT ann (TacticInternal.setLabelT "l");
  "setLabelT l thenT addTermT", prefix_thenT (TacticInternal.setLabelT "l") ann;
]
let rec expr = function
  | Proof.ExprGoal -> "goal" | Proof.ExprIdentity -> "identity" | Proof.ExprUnjustified -> "unjustified"
  | Proof.ExprExtract _ -> "extract" | Proof.ExprCompose e -> "compose(" ^ expr e ^ ")" | Proof.ExprWrapped _ -> "wrapped"
  | Proof.ExprRule (s, _) -> "rule " ^ s | Proof.ExprAnnotate -> "annotate"
let rec tree p a depth =
  match Proof.info p a with
  | exception _ -> ()
  | i ->
     Printf.printf "    %s %s, goal %s, %d subgoals\n" (sa a) (expr i.Proof.step_expr) (gkey (Proof.goal p a)) (List.length i.Proof.step_subgoals);
     if depth > 0 then List.iter (fun k -> tree p (a @ [ k ]) (depth - 1)) [ 0; 1; 2; 3 ]
let () =
  List.iter (fun (name, tac) ->
      let p = rf (root ()) [] name tac in
      try show name p []; tree p [ 0 ] 2 with e -> Printf.printf "%s raised %s\n" name (Printexc.to_string e)) cases
