(* Proof_boot.Proof: expand and kreitz, the operations that re-run or
   reshape a stored proof, which the proof census runs and no unit test did
   (2026-11-11 reach census: of proof_boot.ml's census lines, 130 run by no
   unit test, most in expand_ext, replace_goal / replace_subg,
   find_leaf_guess and the subgoal matching).  300 random proofs are built
   as in test_proof_boot (idT, cutT X and nthAssumT i, a third under
   wrapT).  expand gets a handler that catches a refinement's failure and
   returns None, as its interface asks (Refine_exn.print "or a similar
   wrapper").  Pinned as found:
     - expand of an unchanged proof keeps the node count and the root's
       status, but in some proofs it MOVES a sub-proof to a different
       subgoal: update_subgoals matches the re-run step's new leaves in
       order, each first exactly, then by a hypothesis-subset match
       (tactic_arg_match), then by the conclusion alone, and open goals
       are not candidates, so an earlier leaf can take a sub-proof made
       for a later leaf that is an exact match for it (removing either
       fallback alone still moves them; removing both moves none).  The count is printed, and the first such proof
       is printed before and after;
     - kreitz collapses a proof into one step and marks it incomplete;
       its node counts on the first ten proofs are printed.
   The generator is a fixed linear congruential sequence, not Random. *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Tactic_boot
open Tactic_boot_sig
open Proof_boot
open Tacticals_boot.Tacticals

let state = ref 2117
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


let handler f = try Some (f ()) with RefineError.RefineError _ -> None
let nc p = let a, b = Proof.node_count p in Printf.sprintf "%d/%d" a b
let shape p sh = List.map (fun a -> try Some (gkey (Proof.goal p a), Proof.is_leaf p a) with RefineError.RefineError _ -> None) (addrs sh [])
let show_at p a = try Printf.sprintf "%s %s" (gkey (Proof.goal p a)) (if Proof.is_leaf p a then "leaf" else "node") with RefineError.RefineError _ -> "-"

let () =
  let n = 300 in
  let kept = ref 0 and moved = ref 0 and counts_ok = ref 0 and sub_ok = ref 0 and sub_n = ref 0 and kstatus = Hashtbl.create 4 in
  let shown = ref 0 and example = ref false in
  for k = 1 to n do
    let p, sh = build () in
    let e = Proof.expand (fun x -> x) handler p [] in
    if Proof.node_count e = Proof.node_count p && Proof.status e [] = Proof.status p [] then incr counts_ok;
    if shape e sh = shape p sh then incr kept
    else begin
      incr moved;
      if not !example then begin
        example := true;
        Printf.printf "first proof whose expand moves a sub-proof: proof %d\n" k;
        List.iter (fun a ->
            Printf.printf "  %-7s before %-24s after %s\n" (String.concat "." (List.map string_of_int a)) (show_at p a) (show_at e a))
          (addrs sh [])
      end
    end;
    let kp = Proof.kreitz (fun x -> x) p [] in
    let ks = st (Proof.status kp []) in
    Hashtbl.replace kstatus ks (1 + try Hashtbl.find kstatus ks with Not_found -> 0);
    if !shown < 10 then begin
      incr shown; Printf.printf "  kreitz on proof %d (%s, %s): %s -> %s, %s\n" k (nc p) (st (Proof.status p [])) (nc p) (nc kp) ks
    end;
    (match addrs sh [] with
     | _ :: a :: _ ->
         incr sub_n;
         ignore (Proof.expand (fun x -> x) handler p a);
         incr sub_ok
     | _ -> ())
  done;
  Printf.printf "%d proofs\n" n;
  Printf.printf "expand keeps node count and root status        %4d of %4d\n" !counts_ok n;
  Printf.printf "expand keeps every sub-proof at its subgoal    %4d of %4d (moved in %d)\n" !kept n !moved;
  Printf.printf "expand at the first child returns              %4d of %4d\n" !sub_ok !sub_n;
  Printf.printf "kreitz root status: %s\n"
    (String.concat ", " (List.sort compare (Hashtbl.fold (fun k v l -> Printf.sprintf "%s %d" k v :: l) kstatus [])))
