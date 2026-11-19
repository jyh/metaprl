(* Proof_boot.Proof.refine AT A NODE THAT IS ALREADY REFINED: the new step
   replaces the old one (replace_step_rule, reached through every arm a
   built proof has: a plain rule box and a Wrapped one), and the old
   step's subgoals are matched to the new step's leaves (match_subgoals):
   each new leaf takes the first remaining OLD child that was itself
   refined and whose goal and assumptions are alpha-equal to the leaf's
   (labels are not compared), and is an open goal otherwise; old refined
   children nobody takes become extras, which node_count does not count,
   and a LATER re-refinement of the same node matches its old subgoals and
   then its extras, in that order.
   Random proofs as in test_proof_boot (a fixed linear congruential
   sequence, idT, cutT X and nthAssumT i, a third under wrapT); then up to
   three re-refinements at random refined nodes, each with a random
   tactic that applies there.  After each, a shadow tree updated by that
   model is compared with the proof at every address: is_leaf, the goal
   (with its label: a kept child keeps its own), status, node_count. *)
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

type sh = Leaf of string | Node of string * bool * sh list * sh list   (* the goal's key; wrapped; extras *)
let rec get t = function [] -> t | i :: r -> (match t with Node (_, _, cs, _) -> get (List.nth cs (i - 1)) r | Leaf _ -> assert false)
let rec set t p x = match p, t with
  | [], _ -> x
  | i :: r, Node (g, w, cs, ex) -> Node (g, w, List.mapi (fun j c -> if j = i - 1 then set c r x else c) cs, ex)
  | _ -> assert false
let key = function Leaf g | Node (g, _, _, _) -> g
let rec status = function Leaf _ -> "partial" | Node (_, _, cs, _) -> if List.for_all (fun c -> status c = "complete") cs then "complete" else "partial"
let rec count = function Leaf _ -> (0, 1) | Node (_, w, cs, _) -> List.fold_left (fun (r, n) c -> let r', n' = count c in r + r', n + n') (1, if w then 3 else 2) cs
let rec addrs t p = p :: (match t with Leaf _ -> [] | Node (_, _, cs, _) -> List.concat (List.mapi (fun i c -> addrs c (p @ [ i + 1 ])) cs))
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
         sh := set !sh l (Node (key (get !sh l), wrapped, List.map (fun a -> Leaf (gkey a)) subs, []));
         leaves := List.filter (fun x -> x <> l) !leaves @ List.init (List.length subs) (fun i -> l @ [ i + 1 ])
    end
  done;
  !p, !sh


let mkey g = match String.index_opt g ':' with Some i -> String.sub g (i + 1) (String.length g - i - 1) | None -> g
let rec take k = function
  | [] -> None, []
  | (Node (g, _, _, _) as c) :: r when mkey g = k -> Some c, r
  | c :: r -> let x, r' = take k r in x, c :: r'
let rec nodes t p = match t with Leaf _ -> [] | Node (_, _, cs, _) -> p :: List.concat (List.mapi (fun i c -> nodes c (p @ [ i + 1 ])) cs)

let () =
  let n = 300 and good = ref 0 and checks = ref 0 and rer = ref 0 and kept = ref 0 and opened = ref 0 and dropped = ref 0 and wr = ref 0 in
  for k = 1 to n do
    let p, sh = build () in
    let p = ref p and sh = ref sh in
    let bad = ref [] in
    let chk what b = incr checks; if not b then bad := what :: !bad in
    let ps a = String.concat "." (List.map string_of_int a) in
    for _ = 1 to 3 do
      let ns = nodes !sh [] in
      if ns <> [] then begin
        let a = List.nth ns (pick (List.length ns)) in
        let name, tac = match pick 4 with
          | 0 -> "idT", idT
          | 1 | 2 -> let x = atoms.(pick 3) in "cutT " ^ x, cutT (at x)
          | _ -> let i = 1 + pick 3 in Printf.sprintf "nthAssumT %d" i, nthAssumT i in
        let wrapped = pick 3 = 0 in
        let name, tac = if wrapped then "wrapped " ^ name, TacticInternal.wrapT (IntArgList ("wrapped", 7)) tac else name, tac in
        match TacticInternal.refine tac (Proof.goal !p a) with
        | exception RefineError.RefineError _ -> ()
        | subs, _ ->
           incr rer; if wrapped then incr wr;
           (match get !sh a with
            | Node (g, _, cs, ex) ->
               let rest = ref (cs @ ex) in
               let cs' = List.map (fun s -> let gk = gkey s in match take (mkey gk) !rest with
                 | Some c, r -> rest := r; incr kept; c
                 | None, r -> rest := r; incr opened; Leaf gk) subs in
               let extras = List.filter (function Node _ -> true | Leaf _ -> false) !rest in
               dropped := !dropped + List.length extras;
               sh := set !sh a (Node (g, wrapped, cs', extras))
            | Leaf _ -> assert false);
           p := Proof.refine (fun x -> x) !p a name (ex name) tac;
           chk ("node_count after " ^ ps a) (Proof.node_count !p = count !sh);
           List.iter (fun b ->
               let t = get !sh b in
               chk ("is_leaf " ^ ps b) (Proof.is_leaf !p b = (match t with Leaf _ -> true | Node _ -> false));
               chk ("goal " ^ ps b) (gkey (Proof.goal !p b) = key t);
               chk ("status " ^ ps b) (st (Proof.status !p b) = status t))
             (addrs !sh [])
      end
    done;
    if !bad = [] then incr good else Printf.printf "proof %d: FAILED %s\n" k (String.concat ", " (List.rev !bad))
  done;
  Printf.printf "re-refined: %d/%d proofs agree with the model (%d checks, %d re-refinements, %d wrapped)\n" !good n !checks !rer !wr;
  Printf.printf "old children: %d kept, %d leaves opened, %d refined children left as extras\n" !kept !opened !dropped
