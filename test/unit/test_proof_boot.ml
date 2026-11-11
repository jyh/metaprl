(* Proof_boot.Proof's tree accessors: index (through is_leaf and goal),
   status, path_status and node_count, which no unit test named (coverage
   recount 11-10).  Random proofs are built without a theory as in
   test_proof_convert (Proof.create, then 0-8 refinements with idT, cutT X
   and nthAssumT i at random open leaves, a third of them under
   TacticInternal.wrapT), and a shadow tree is kept beside each: a leaf is
   an open goal, a node is a refinement (wrapped or not) with its subgoals.
   At every address of the shadow tree, at child 0 of every node, and at one
   child past the end of every node and leaf, the proof is compared with a
   model read from proof_boot.ml:
     is_leaf / goal   a leaf is an open goal; child 0 of a node is the node's
                      own extract (not a leaf, the node's goal); child 0.0 is
                      the wrapped extract under it for a wrapped refinement
                      and is refused otherwise; a child past the end is
                      refused (Proof_boot.index)
     status           an open goal is partial; a node is complete when all
                      its subgoals are (none: complete), else partial
     path_status      the status of each node from the root down the path;
                      a last step that does not exist is dropped
     node_count       (refinements, nodes): a leaf is 1 node, a refinement 2
                      (the rule box and its extract), 3 when wrapped, plus
                      its subgoals'
   The generator is a fixed linear congruential sequence, not Random. *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Tactic_boot
open Tactic_boot_sig
open Proof_boot
open Tacticals_boot.Tacticals

let state = ref 1116
let next () = state := (!state * 1103515245 + 12345) land 0x7fffffff; !state lsr 8
let pick n = next () mod n

let atoms = [| "A"; "B"; "C" |]
let at n = mk_simple_term (Opname.make_opname [ n ]) []
let ex name = MLast.ExLid (Ploc.dummy, Ploc.VaVal name)
let st = function Proof.StatusBad -> "bad" | Proof.StatusIncomplete -> "incomplete" | Proof.StatusPartial -> "partial" | Proof.StatusComplete -> "complete"
let s t = Simple_print.SimplePrint.string_of_term t
let gkey (a : TacticInternalType.tactic_arg) = let c, l = Refine.dest_msequent a.ref_goal in a.ref_label ^ ":" ^ s c ^ "[" ^ String.concat "," (List.map s l) ^ "]"

type sh = Leaf of string | Node of string * bool * sh list   (* the goal's key; wrapped *)
let rec get t = function [] -> t | i :: r -> (match t with Node (_, _, cs) -> get (List.nth cs (i - 1)) r | Leaf _ -> assert false)
let rec set t p x = match p, t with
  | [], _ -> x
  | i :: r, Node (g, w, cs) -> Node (g, w, List.mapi (fun j c -> if j = i - 1 then set c r x else c) cs)
  | _ -> assert false
let key = function Leaf g | Node (g, _, _) -> g
let rec status = function Leaf _ -> "partial" | Node (_, _, cs) -> if List.for_all (fun c -> status c = "complete") cs then "complete" else "partial"
let rec count = function Leaf _ -> (0, 1) | Node (_, w, cs) -> List.fold_left (fun (r, n) c -> let r', n' = count c in r + r', n + n') (1, if w then 3 else 2) cs
let rec addrs t p = p :: (match t with Leaf _ -> [] | Node (_, _, cs) -> List.concat (List.mapi (fun i c -> addrs c (p @ [ i + 1 ])) cs))
let rec prefixes = function [] -> [ [] ] | p -> prefixes (List.rev (List.tl (List.rev p))) @ [ p ]

let build () =
  let goal = Refine.mk_msequent (at atoms.(pick 3)) (List.init (pick 3) (fun _ -> at atoms.(pick 3))) in
  let base = TacticInternal.debug_arg Mp_resource.empty_bookmark (at "A") in
  let a0 = { base with TacticInternalType.ref_goal = goal } in
  let p = ref (Proof.create a0) and sh = ref (Leaf (gkey a0)) and leaves = ref [ [] ] in
  for _ = 1 to pick 9 do
    if !leaves <> [] then begin
      let l = List.nth !leaves (pick (List.length !leaves)) in
      let name, tac = match pick 4 with
        | 0 -> "idT", idT
        | 1 | 2 -> let x = atoms.(pick 3) in "cutT " ^ x, cutT (at x)
        | _ -> let i = 1 + pick 3 in Printf.sprintf "nthAssumT %d" i, nthAssumT i in
      let wrapped = pick 3 = 0 in
      let name, tac = if wrapped then "wrapped " ^ name, TacticInternal.wrapT (IntArgList ("wrapped", 7)) tac else name, tac in
      match TacticInternal.refine tac (Proof.goal !p l) with
      | exception RefineError.RefineError _ -> ()
      | subs, _ ->
         p := Proof.refine (fun x -> x) !p l name (ex name) tac;
         sh := set !sh l (Node (key (get !sh l), wrapped, List.map (fun a -> Leaf (gkey a)) subs));
         leaves := List.filter (fun x -> x <> l) !leaves @ List.init (List.length subs) (fun i -> l @ [ i + 1 ])
    end
  done;
  !p, !sh

let () =
  let n = 300 and good = ref 0 and checks = ref 0 and rules = ref 0 and partial = ref 0 and complete = ref 0 and closed = ref 0 and wrapped = ref 0 and wrapped_closed = ref 0 in
  for k = 1 to n do
    let p, sh = build () in
    let bad = ref [] in
    let chk what b = incr checks; if not b then bad := what :: !bad in
    let ps a = String.concat "." (List.map string_of_int a) in
    let refused f = match f () with _ -> false | exception RefineError.RefineError _ -> true in
    chk "node_count" (Proof.node_count p = count sh);
    rules := !rules + fst (count sh);
    List.iter (fun a ->
        let t = get sh a in
        (match status t with "complete" -> incr complete | _ -> incr partial);
        (match t with Node (_, w, []) -> incr closed; if w then incr wrapped_closed | _ -> ());
        (match t with Node (_, true, _) -> incr wrapped | _ -> ());
        chk ("is_leaf " ^ ps a) (Proof.is_leaf p a = (match t with Leaf _ -> true | Node _ -> false));
        chk ("goal " ^ ps a) (gkey (Proof.goal p a) = key t);
        chk ("status " ^ ps a) (st (Proof.status p a) = status t);
        chk ("path_status " ^ ps a) (List.map st (Proof.path_status p a) = List.map (fun q -> status (get sh q)) (prefixes a));
        let past = a @ [ (match t with Leaf _ -> 1 | Node (_, _, cs) -> List.length cs + 1) ] in
        chk ("refused " ^ ps past) (refused (fun () -> Proof.is_leaf p past));
        chk ("path_status past " ^ ps past) (List.map st (Proof.path_status p past) = List.map (fun q -> status (get sh q)) (prefixes a));
        (match t with
         | Node (g, w, _) ->
            chk ("child 0 of " ^ ps a) (not (Proof.is_leaf p (a @ [ 0 ])) && gkey (Proof.goal p (a @ [ 0 ])) = g);
            if w then chk ("child 0.0 of " ^ ps a) (not (Proof.is_leaf p (a @ [ 0; 0 ])) && gkey (Proof.goal p (a @ [ 0; 0 ])) = g)
            else chk ("refused 0.0 of " ^ ps a) (refused (fun () -> Proof.is_leaf p (a @ [ 0; 0 ])))
         | Leaf _ -> ()))
      (addrs sh []);
    if !bad = [] then incr good else Printf.printf "proof %d: FAILED %s\n" k (String.concat ", " (List.rev !bad))
  done;
  Printf.printf "random: %d/%d proofs agree with the model (%d checks, %d refinements)\n" !good n !checks !rules;
  Printf.printf "addresses by model status: %d partial, %d complete (%d of them closed by a refinement with no subgoal); %d wrapped refinements (%d closing)\n" !partial !complete !closed !wrapped !wrapped_closed
