(* Proof_boot's editor operations below the root: proofs refined in two
   or three steps (a leaf of the first step refined again), so that the
   nodes under a step are themselves rule boxes and compositions.  The
   2026-11-11 reach census, after test_proof_ops_kinds, left 331 of
   proof_boot.ml's 864 points reached by nothing, among them info, copy,
   paste and find_subgoal at nested addresses.  For each proof, every
   address in the tree prints its info (expression, subgoal and extras
   counts), status and whether it is a leaf, and find_subgoal for each of
   its subgoals; then paste of a one-step proof onto each leaf, copy of a
   refined leaf onto another leaf, and the node count and status after.
   Pinned as it reads today, including: find_subgoal answers an address
   INSIDE the step's own extract (where the subgoal appears in the rule
   box's composition, [0] under a wrapper), not a proof-tree address, so
   a one-tactic step answers [] for each of its subgoals. *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Tactic_boot
open Tactic_boot_sig
open Proof_boot
open Tacticals_boot.Tacticals

let at n = mk_simple_term (Opname.make_opname [ n ]) []
let ex name = MLast.ExLid (Ploc.dummy, Ploc.VaVal name)
let say fmt = Printf.ksprintf (fun s -> print_string s; flush stdout) fmt
let st = function Proof.StatusBad -> "bad" | Proof.StatusIncomplete -> "incomplete" | Proof.StatusPartial -> "partial" | Proof.StatusComplete -> "complete"
let nc (a, b) = Printf.sprintf "%d/%d" a b
let upd p = p
let try_s f = try f () with RefineError.RefineError (n, _) -> "refused (" ^ n ^ ")" | e -> "raised " ^ Printexc.to_string e
let sa a = "[" ^ String.concat "." (List.map string_of_int a) ^ "]"
let rec expr = function
  | Proof.ExprGoal -> "goal" | Proof.ExprIdentity -> "identity" | Proof.ExprUnjustified -> "unjustified"
  | Proof.ExprExtract _ -> "extract" | Proof.ExprCompose e -> "compose(" ^ expr e ^ ")" | Proof.ExprWrapped _ -> "wrapped"
  | Proof.ExprRule (s, _) -> "rule " ^ s | Proof.ExprAnnotate -> "annotate"

let base () =
  let b = TacticInternal.debug_arg Mp_resource.empty_bookmark (at "A") in
  { b with TacticInternalType.ref_goal = Refine.mk_msequent (at "A") [ at "A" ] }

let rec addresses p addr =
  if Proof.is_leaf p addr then [ addr ]
  else addr :: List.concat (List.mapi (fun i _ -> addresses p (addr @ [ i + 1 ])) (Proof.info p addr).Proof.step_subgoals)

let tree label p =
  say "  %s: nodes %s, status %s\n" label (try_s (fun () -> nc (Proof.node_count p))) (try_s (fun () -> st (Proof.status p [])));
  List.iter (fun a ->
      say "    %-8s %s\n" (sa a) (try_s (fun () ->
          let i = Proof.info p a in
          Printf.sprintf "%s | goal %d, subgoals %d, extras %d | %s%s | find_subgoal 0: %s, %s" (expr i.Proof.step_expr) (List.length i.Proof.step_goal) (List.length i.Proof.step_subgoals)
            (List.length i.Proof.step_extras) (st (Proof.status p a)) (if Proof.is_leaf p a then ", leaf" else "") (try_s (fun () -> sa (Proof.find_subgoal p a 0)))
            (String.concat " " (List.mapi (fun k _ -> try_s (fun () -> sa (Proof.find_subgoal p a (k + 1)))) i.Proof.step_subgoals)))))
    (try addresses p [] with _ -> [])

let refine p a name tac = Proof.refine upd p a name (ex name) tac

let () =
  let b = at "B" and c = at "C" in
  let steps = [
    "cutT B, then cutT C at [1]", [ [], "cutT B", cutT b; [ 1 ], "cutT C", cutT c ];
    "cutT B, then nthAssumT 1 at [2]", [ [], "cutT B", cutT b; [ 2 ], "nthAssumT 1", nthAssumT 1 ];
    "addIntT k 3, then cutT B at [1], then idT at [1.2]", [ [], "addIntT k 3", TacticInternal.addIntT "k" 3; [ 1 ], "cutT B", cutT b; [ 1; 2 ], "idT", idT ];
    "withTermT w C (cutT B), then wrapT (cutT C) at [1]", [ [], "withTermT", TacticInternal.withTermT "w" c (cutT b); [ 1 ], "wrapT", TacticInternal.wrapT (IntArgList ("w", 1)) (cutT c) ];
    "cutT B thenLT [idT; idT], then nthAssumT 1 at [2]", [ [], "thenLT", prefix_thenLT (cutT b) [ idT; idT ]; [ 2 ], "nthAssumT 1", nthAssumT 1 ];
    "cutT B thenLT [cutT C; idT] (subgoals from two branches)", [ [], "thenLT2", prefix_thenLT (cutT b) [ cutT c; idT ] ];
    "cutT B thenLT [idT; cutT C]", [ [], "thenLT3", prefix_thenLT (cutT b) [ idT; cutT c ] ];
  ] in
  List.iter (fun (name, sts) ->
      say "== %s\n" name;
      Proof.clear_cache ();
      match List.fold_left (fun p (a, n, t) -> refine p a n t) (Proof.create (base ())) sts with
      | exception e -> say "  refine raised %s\n" (Printexc.to_string e)
      | p ->
          tree "proof" p;
          let leaves = List.filter (fun a -> try Proof.is_leaf p a with _ -> false) (try addresses p [] with _ -> []) in
          List.iter (fun l ->
              let one = refine (Proof.create (Proof.goal p l)) [] "cutT C" (cutT c) in
              say "  paste a one-step proof (cutT C) at %s: %s\n" (sa l)
                (try_s (fun () -> let q = Proof.paste upd p l one in Printf.sprintf "nodes %s, status %s" (nc (Proof.node_count q)) (st (Proof.status q [])))))
            leaves;
          (match leaves with
           | l1 :: l2 :: _ ->
               say "  copy %s onto %s: %s\n" (sa l1) (sa l2) (try_s (fun () -> let q = Proof.copy upd p l1 l2 in Printf.sprintf "nodes %s, status %s" (nc (Proof.node_count q)) (st (Proof.status q []))));
               (match refine p l1 "idT" idT with
                | p1 -> say "  idT at %s, then copy it onto %s: %s\n" (sa l1) (sa l2)
                          (try_s (fun () -> let q = Proof.copy upd p1 l1 l2 in Printf.sprintf "nodes %s, status %s" (nc (Proof.node_count q)) (st (Proof.status q []))))
                | exception e -> say "  idT at %s raised %s\n" (sa l1) (Printexc.to_string e))
           | _ -> ()))
    steps
