(* Proof_boot.find_subgoal and count_leaves on the shapes no other unit
   test reaches (the 2026-11-15 reach table left them unreached):
   - find_subgoal from a node whose rule box has never been normalized:
     find_subgoal i = 0 at a child walks up to the first ancestor whose goal
     differs and searches that ancestor's box, normalizing it first.  A
     fresh call is made before anything else reads the tree, and again
     after, under a nested composition (the answer must not change);
   - a subgoal number past the step's subgoals is refused with
     Invalid_argument "Proof_boot.find_subgoal" (List.nth's Failure turned
     into it); -1 reaches List.nth's own Invalid_argument;
   - count_leaves over an annotation (addTermT) and a wrapper (wrapT) among
     the inner subgoals of a nested composition (t1 thenLT [...]) thenT t2,
     which normalization joins (join_subgoals splits the outer subgoals by
     each inner subgoal's leaf count).
   Every step prints its goal, subgoal count, node_count and find_subgoal
   for 0 .. one past its last subgoal.  As find_subgoal reads today, its
   answer is an address inside the searched step's extract, not a proof
   address (test_proof_ops_nested).  Not reached here, stated: find_subgoal's
   Goal, Identity and Annotate arms (find_subgoal compares msequents only,
   and each of these extracts has the msequent of its own subgoal, so the
   node above it matches first) and its Pending arm (only the proof cache
   holds Pending nodes); count_leaves' Goal, Unjustified, RuleBox, Pending
   and Locked arms.  The expected file is the output of the code as
   written, never typed. *)
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
let gkey (a : TacticInternalType.tactic_arg) = let c, l = Refine.dest_msequent a.ref_goal in s c ^ "[" ^ String.concat "," (List.map s l) ^ "]"
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

let () =
  (* 1: a composite step, never normalized, and a child refined under it *)
  let p = rf (root ()) [] "cutT B thenT cutT C" (prefix_thenT (cutT (at "B")) (cutT (at "C"))) in
  let p = rf p [ 1 ] "cutT X" (cutT (at "X")) in
  Printf.printf "fresh find_subgoal [1] 0: %s\n" (fs p [ 1 ] 0);
  Printf.printf "fresh find_subgoal [1] 1: %s\n" (fs p [ 1 ] 1);
  show "1" p [];
  show "1" p [ 1 ];
  (* 2: a nested composition with an annotation and a wrapper among the inner subgoals *)
  let t2 = prefix_thenT (prefix_thenLT (cutT (at "B")) [ addTermT "n" (at "N"); wrapT (IntArgList ("w", 7)) (cutT (at "C")) ]) (cutT (at "D")) in
  let p = rf (root ()) [] "nested" t2 in
  let p = rf p [ 6 ] "cutT Y" (cutT (at "Y")) in
  Printf.printf "2 fresh find_subgoal [6] 0: %s\n" (fs p [ 6 ] 0);
  Printf.printf "2 again find_subgoal [6] 0: %s\n" (fs p [ 6 ] 0);
  show "2" p [];
  (* 3: idT thenT cutT X, whose composition normalizes to cutT X's own extract *)
  let p = rf (root ()) [] "idT thenT cutT X" (prefix_thenT idT (cutT (at "X"))) in
  let p = rf p [ 1 ] "cutT Y" (cutT (at "Y")) in
  Printf.printf "3 fresh find_subgoal [1] 0: %s\n" (fs p [ 1 ] 0);
  Printf.printf "3 again find_subgoal [1] 0: %s\n" (fs p [ 1 ] 0);
  show "3" p [];
  Printf.printf "  find_subgoal -1: %s\n" (fs p [] (-1))
