(* Proof_boot.Proof on refinements by COMPOSITE tactics, whose rule box
   holds a composed extract that Proof normalizes when the box is indexed
   (tactics/proof/proof_boot.ml normalize, replace_subg, join_subgoals,
   count_leaves, goal_ext, status_ext, node_count_ext, post): the paths
   only the proof census reached (2026-11-11 reach census: 106 lines of
   proof_boot.ml reached by the census and by no unit test, the open PRs'
   tests included).  test_proof_boot refines with one tactic at a time.
   Random tactics are trees of idT, cutT X and nthAssumT i (X an atom A, B,
   C; i from 1) joined by thenT, thenLT (one tactic per subgoal) and
   orelseT.  For each, a random goal with 0-2 assumptions is refined twice:
   by TacticInternal.refine, the reference, and by Proof.refine at the root
   of a fresh proof; then each subgoal of the proof is closed by
   nthAssumT when its goal is among its assumptions.  The proof is
   compared with the reference:
     - refused by one exactly when refused by the other;
     - the goal at address [i] is the reference's i-th subgoal (label,
       goal, assumptions), [i] is a leaf, and [n+1] is refused;
     - the goal at [0], the normalized extract, is the root goal;
     - the root's status is complete exactly when no subgoal is left open
       after the closing pass, else partial;
     - once a leaf has been closed, the open leaves (goal and assumptions,
       the label not compared) are the reference's subgoals that cannot be
       closed, each once, in the reference's order;
     - Proof.post of the proof gives the same status and open leaves.
   Each closable leaf (its goal among its assumptions) is closed by
   nthAssumT, re-reading the leaves after each close.
   Pinned as found, not changed: the subgoals of a composite refinement
   are listed in full after it (duplicates included), and deduplicated
   (equal goal, assumptions and attributes; the label is not compared)
   at the next refinement under it, so the addresses of the later leaves
   shift.  The fixed case at the end prints one: closing [3]
   of  cutT B thenT cutT B thenT cutT B  on A leaves 4 of 8.
   Two mutants of proof_boot.ml survive and are declared: remove_duplicates
   disabled (remove_duplicates_onto removes the same duplicates in every
   path this test reaches; disabling THAT one is red), and join_subgoals'
   all-identity shortcut disabled (the general path builds the same
   subgoals: equivalent, as far as this test can see).
   node_count is printed in aggregate, not modelled (a composed extract
   counts its inner steps).  The generator is a fixed linear congruential
   sequence, not Random. *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Tactic_boot
open Proof_boot
open Tacticals_boot.Tacticals

let state = ref 1117
let next () = state := (!state * 1103515245 + 12345) land 0x7fffffff; !state lsr 8
let pick n = next () mod n

let atoms = [| "A"; "B"; "C" |]
let at n = mk_simple_term (Opname.make_opname [ n ]) []
let ex name = MLast.ExLid (Ploc.dummy, Ploc.VaVal name)
let st = function Proof.StatusBad -> "bad" | Proof.StatusIncomplete -> "incomplete" | Proof.StatusPartial -> "partial" | Proof.StatusComplete -> "complete"
let s t = Simple_print.SimplePrint.string_of_term t
let gkey (a : TacticInternalType.tactic_arg) = let c, l = Refine.dest_msequent a.ref_goal in a.ref_label ^ ":" ^ s c ^ "[" ^ String.concat "," (List.map s l) ^ "]"

type t = Id | Cut of string | Assum of int | Then of t * t | ThenL of t * t list | Else of t * t
let rec show = function
  | Id -> "idT" | Cut x -> "cutT " ^ x | Assum i -> "nthAssumT " ^ string_of_int i
  | Then (a, b) -> "(" ^ show a ^ " thenT " ^ show b ^ ")"
  | ThenL (a, bs) -> "(" ^ show a ^ " thenLT [" ^ String.concat "; " (List.map show bs) ^ "])"
  | Else (a, b) -> "(" ^ show a ^ " orelseT " ^ show b ^ ")"
let rec gen d =
  let atom () = match pick 4 with 0 -> Id | 1 | 2 -> Cut atoms.(pick 3) | _ -> Assum (1 + pick 3) in
  if d = 0 then atom () else
  match pick 6 with
  | 0 | 1 -> atom ()
  | 2 | 3 -> Then (gen (d - 1), gen (d - 1))
  | 4 -> let a = gen (d - 1) in ThenL (a, List.init (pick 3) (fun _ -> gen (d - 1)))
  | _ -> Else (gen (d - 1), gen (d - 1))
let rec real = function
  | Id -> idT | Cut x -> cutT (at x) | Assum i -> nthAssumT i
  | Then (a, b) -> prefix_thenT (real a) (real b)
  | ThenL (a, bs) -> prefix_thenLT (real a) (List.map real bs)
  | Else (a, b) -> prefix_orelseT (real a) (real b)

let base = TacticInternal.debug_arg Mp_resource.empty_bookmark (at "A")
let closer (a : TacticInternalType.tactic_arg) =
  let c, l = Refine.dest_msequent a.ref_goal in
  let rec find i = function [] -> None | h :: t -> if TermSubst.alpha_equal h c then Some i else find (i + 1) t in
  find 1 l

let () =
  let n = 600 and good = ref 0 and refused = ref 0 and subgoals = ref 0 and closed = ref 0 and composite = ref 0 and nodes = ref 0 and first = ref None in
  for _ = 1 to n do
    let tac = gen 3 in
    let goal = Refine.mk_msequent (at atoms.(pick 3)) (List.init (pick 3) (fun _ -> at atoms.(pick 3))) in
    let a0 = { base with TacticInternalType.ref_goal = goal } in
    let reference = match TacticInternal.refine (real tac) a0 with subs, _ -> Some subs | exception RefineError.RefineError _ -> None in
    let p0 = Proof.create a0 in
    let proof = match Proof.refine (fun x -> x) p0 [] (show tac) (ex "t") (real tac) with p -> Some p | exception RefineError.RefineError _ -> None in
    let bad = ref [] in
    let chk what b = if not b then bad := what :: !bad in
    (match tac with Id | Cut _ | Assum _ -> () | _ -> incr composite);
    let stage = ref "start" in
    (try (match reference, proof with
     | None, None -> incr refused
     | Some _, None -> chk "refused by Proof only" false
     | None, Some _ -> chk "refused by refine only" false
     | Some subs, Some p ->
        let k = List.length subs in
        subgoals := !subgoals + k;
        stage := "goals"; List.iteri (fun i a ->
            chk (Printf.sprintf "goal [%d]" (i + 1)) (gkey (Proof.goal p [ i + 1 ]) = gkey a);
            chk (Printf.sprintf "is_leaf [%d]" (i + 1)) (Proof.is_leaf p [ i + 1 ])) subs;
        chk "past the end" (match Proof.goal p [ k + 1 ] with _ -> false | exception RefineError.RefineError _ -> true);
        stage := "goal 0"; chk "goal [0]" (gkey (Proof.goal p [ 0 ]) = gkey a0);
        stage := "close";
        (* close what can be closed: the leaves are re-read after each close,
           because the list is deduplicated then (see the header) *)
        let rec leaves p i = match Proof.goal p [ i ] with
          | a -> (if Proof.is_leaf p [ i ] then [ i, a ] else []) @ leaves p (i + 1)
          | exception RefineError.RefineError _ -> [] in
        let closed_here = ref 0 in
        let rec close p n =
          match List.find_opt (fun (_, a) -> closer a <> None) (leaves p 1) with
          | Some (i, a) when n < 50 ->
             incr closed; incr closed_here; close (Proof.refine (fun x -> x) p [ i ] "close" (ex "close") (nthAssumT (Option.get (closer a)))) (n + 1)
          | _ -> p in
        let p = close p 0 in
        let opened = List.length (List.filter (fun a -> closer a = None) subs) in
        stage := "status"; let want = if opened = 0 then "complete" else "partial" in
        chk "status" (st (Proof.status p []) = want);
        stage := "post"; let q = Proof.post (fun () -> p) [] in
        chk "post status" (st (Proof.status q []) = want);
        stage := "open leaves";
        let nolabel (a : TacticInternalType.tactic_arg) = let c, l = Refine.dest_msequent a.ref_goal in s c ^ "[" ^ String.concat "," (List.map s l) ^ "]" in
        let rec uniq seen = function [] -> [] | x :: t -> if List.mem x seen then uniq seen t else x :: uniq (x :: seen) t in
        let want_open = uniq [] (List.map nolabel (List.filter (fun a -> closer a = None) subs)) in
        let got_open = List.map (fun (_, a) -> nolabel a) (leaves p 1) in
        chk "open leaves" (if !closed_here > 0 then got_open = want_open else true);
        chk "post leaves" (List.map (fun (_, a) -> gkey a) (leaves q 1) = List.map (fun (_, a) -> gkey a) (leaves p 1));
        stage := "node_count"; nodes := !nodes + snd (Proof.node_count p))
     with RefineError.RefineError (n, _) -> chk ("RefineError " ^ n ^ " at " ^ !stage) false);
    if !bad = [] then incr good
    else if !first = None then first := Some (Printf.sprintf "%s on %s: %s" (show tac) (gkey a0) (String.concat ", " (List.rev !bad)))
  done;
  Printf.printf "%-48s %d of %d\n" "proofs agreeing with TacticInternal.refine" !good n;
  Printf.printf "%-48s %d\n" "composite tactics" !composite;
  Printf.printf "%-48s %d\n" "refused by both" !refused;
  Printf.printf "%-48s %d (%d closed by nthAssumT)\n" "subgoals" !subgoals !closed;
  Printf.printf "%-48s %d\n" "nodes (node_count, summed)" !nodes;
  (match !first with Some f -> Printf.printf "first disagreement: %s\n" f | None -> ());
  let a0 = { base with TacticInternalType.ref_goal = Refine.mk_msequent (at "A") [] } in
  let p = Proof.refine (fun x -> x) (Proof.create a0) [] "t" (ex "t") (real (Then (Cut "B", Then (Cut "B", Cut "B")))) in
  let rec goals p i = match Proof.goal p [ i ] with a -> gkey a :: goals p (i + 1) | exception RefineError.RefineError _ -> [] in
  Printf.printf "cutT B thenT cutT B thenT cutT B on A\n  %s\n" (String.concat " | " (goals p 1));
  let p = Proof.refine (fun x -> x) p [ 3 ] "close" (ex "close") (nthAssumT 1) in
  Printf.printf "after nthAssumT 1 at [3]\n  %s\n" (String.concat " | " (goals p 1))
