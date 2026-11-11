(* Proof_boot.Proof's editing operations copy, make_assum, squash and clean,
   which no unit test named (coverage recount 11-10).  Random proofs are
   built as in test_proof_boot (refinements with idT, cutT X and nthAssumT i
   at open leaves, a third under wrapT) beside a shadow tree; one editing
   operation is applied at random addresses, and is_leaf, goal, status and
   node_count are then compared at every address with a model read from
   proof_boot.ml:
     copy from to   the subtree at from replaces the one at to; a copied node
                    takes to's msequent, keeps from's label, loses its Wrapped
                    node and needs re-checking (even onto itself); the copied
                    nodes below keep their own goals; a copied leaf leaves
                    to's goal as it was (the parent's recorded subgoal), except
                    at the root, where it keeps from's label
     squash a       the extracts under a are dropped: each rule node there
                    loses its Wrapped node and needs re-checking, except an
                    unwrapped idT, whose Identity extract stays
     clean a        drops extras; these proofs have none, so nothing changes
                    (a mutant that makes clean a no-op survives this test)
     make_assum a   see below; every node's goal changes, and every rule node
                    but an idT needs re-checking
     status         a rule node that needs re-checking is incomplete; incomplete wins over
                    partial in its ancestors, which win over complete
   make_assum a adds the conclusion of the goal at a as an assumption to
   every node, inserted at the root's assumption count.  (Until this test's
   companion fix, make_assum_arg rebound the name goal to each node's own
   conclusion, so every node got ITS OWN conclusion instead; the fixed case
   at the end prints the chosen goal and every node's assumptions.)
   The generator is a fixed linear congruential sequence, not Random. *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Tactic_boot
open Tactic_boot_sig
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
type g = { l : string; c : string; a : string list }
let gof (x : TacticInternalType.tactic_arg) = let c, a = Refine.dest_msequent x.ref_goal in { l = x.ref_label; c = s c; a = List.map s a }
let gshow g = g.l ^ ":" ^ g.c ^ "[" ^ String.concat "," g.a ^ "]"

(* A leaf is an open goal; a node is a refinement: goal, wrapped, idT (an Identity extract), dirty (needs re-checking), subgoals. *)
type sh = Leaf of g | Node of g * bool * bool * bool * sh list
let rec get t = function [] -> t | i :: r -> (match t with Node (_, _, _, _, cs) -> get (List.nth cs (i - 1)) r | Leaf _ -> raise Not_found)
let rec set t p x = match p, t with
  | [], _ -> x
  | i :: r, Node (g, w, id, d, cs) -> Node (g, w, id, d, List.mapi (fun j c -> if j = i - 1 then set c r x else c) cs)
  | _ -> assert false
let goal_of = function Leaf g | Node (g, _, _, _, _) -> g
let rec status = function
  | Leaf _ -> "partial"
  | Node (_, _, _, d, cs) ->
     let ss = (if d then "incomplete" else "complete") :: List.map status cs in
     if List.mem "incomplete" ss then "incomplete" else if List.mem "partial" ss then "partial" else "complete"
let rec count = function Leaf _ -> (0, 1) | Node (_, w, _, _, cs) -> List.fold_left (fun (r, n) c -> let r', n' = count c in r + r', n + n') (1, if w then 3 else 2) cs
let rec addrs t p = p :: (match t with Leaf _ -> [] | Node (_, _, _, _, cs) -> List.concat (List.mapi (fun i c -> addrs c (p @ [ i + 1 ])) cs))
let rec map_goals f = function Leaf g -> Leaf (f g) | Node (g, w, id, d, cs) -> Node (f g, w, id, d || not id, List.map (map_goals f) cs)
let rec squash = function Leaf g -> Leaf g | Node (g, w, id, d, cs) -> Node (g, false, id, d || w || not id, List.map squash cs)
let rec insert_nth i x l = if i = 0 then x :: l else match l with [] -> [ x ] | h :: t -> h :: insert_nth (i - 1) x t

let build () =
  let goal = Refine.mk_msequent (at atoms.(pick 3)) (List.init (pick 3) (fun _ -> at atoms.(pick 3))) in
  let base = TacticInternal.debug_arg Mp_resource.empty_bookmark (at "A") in
  let a0 = { base with TacticInternalType.ref_goal = goal } in
  let p = ref (Proof.create a0) and sh = ref (Leaf (gof a0)) and leaves = ref [ [] ] in
  for _ = 1 to 1 + pick 8 do
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
         sh := set !sh l (Node (goal_of (get !sh l), wrapped, tac == idT || name = "wrapped idT", false, List.map (fun a -> Leaf (gof a)) subs));
         leaves := List.filter (fun x -> x <> l) !leaves @ List.init (List.length subs) (fun i -> l @ [ i + 1 ])
    end
  done;
  !p, !sh

type op = Copy of int list * int list | Squash of int list | Clean of int list | MakeAssum of int list
let ps a = if a = [] then "." else String.concat "." (List.map string_of_int a)
let oshow = function Copy (f, t) -> "copy " ^ ps f ^ " -> " ^ ps t | Squash a -> "squash " ^ ps a | Clean a -> "clean " ^ ps a | MakeAssum a -> "make_assum " ^ ps a
let apply_real p = function
  | Copy (f, t) -> Proof.copy (fun x -> x) p f t | Squash a -> Proof.squash (fun x -> x) p a
  | Clean a -> Proof.clean (fun x -> x) p a | MakeAssum a -> Proof.make_assum (fun x -> x) p a
let apply_model sh = function
  | Copy (f, t) ->
     let src = get sh f and dst = goal_of (get sh t) in
     let g0 = goal_of src in
     let g' = { g0 with c = dst.c; a = dst.a } in
     let moved = match src with
       | Leaf _ -> if t = [] then Leaf g' else Leaf dst
       | Node (_, _, id, _, cs) -> Node (g', false, id, true, cs) in
     set sh t moved
  | Squash a -> set sh a (squash (get sh a))
  | Clean _ -> sh
  | MakeAssum a -> let n = List.length (goal_of sh).a and x = (goal_of (get sh a)).c in map_goals (fun g -> { g with a = insert_nth n x g.a }) sh

let () =
  let n = 400 and good = ref 0 and checks = ref 0 in
  let ops = Hashtbl.create 4 in
  for k = 1 to n do
    let p, sh = build () in
    let all = addrs sh [] in
    let any () = List.nth all (pick (List.length all)) in
    let op = match pick 4 with 0 -> Copy (any (), any ()) | 1 -> Squash (any ()) | 2 -> Clean (any ()) | _ -> MakeAssum (any ()) in
    let name = match op with Copy _ -> "copy" | Squash _ -> "squash" | Clean _ -> "clean" | MakeAssum _ -> "make_assum" in
    Hashtbl.replace ops name (1 + try Hashtbl.find ops name with Not_found -> 0);
    let p' = apply_real p op and sh' = apply_model sh op in
    let bad = ref [] in
    let chk what b = incr checks; if not b then bad := what :: !bad in
    let cnt (r, n) = Printf.sprintf "%d/%d" r n in
    chk ("node_count " ^ cnt (Proof.node_count p') ^ " model " ^ cnt (count sh')) (Proof.node_count p' = count sh');
    List.iter (fun a ->
        let t = get sh' a in
        chk ("is_leaf " ^ ps a) (Proof.is_leaf p' a = (match t with Leaf _ -> true | Node _ -> false));
        chk ("goal " ^ ps a ^ " " ^ gshow (gof (Proof.goal p' a)) ^ " model " ^ gshow (goal_of t)) (gof (Proof.goal p' a) = goal_of t);
        chk ("status " ^ ps a ^ " " ^ st (Proof.status p' a) ^ " model " ^ status t) (st (Proof.status p' a) = status t))
      (addrs sh' []);
    if !bad = [] then incr good
    else Printf.printf "proof %d, %s: FAILED %s\n" k (oshow op) (String.concat ", " (List.rev !bad))
  done;
  Printf.printf "random: %d/%d edits agree with the model (%d checks; %s)\n" !good n !checks
    (String.concat ", " (List.map (fun k -> Printf.sprintf "%s %d" k (try Hashtbl.find ops k with Not_found -> 0)) [ "copy"; "squash"; "clean"; "make_assum" ]));
  (* The fixed case: make_assum at 1.1 of C, cut B, then cut C at 1. *)
  let p = Proof.create (TacticInternal.debug_arg Mp_resource.empty_bookmark (at "C")) in
  let p = Proof.refine (fun x -> x) p [] "cutT B" (ex "c") (cutT (at "B")) in
  let p = Proof.refine (fun x -> x) p [ 1 ] "cutT C" (ex "c") (cutT (at "C")) in
  let q = Proof.make_assum (fun x -> x) p [ 1; 2 ] in
  Printf.printf "make_assum at 1.2 (goal %s): " (gshow (gof (Proof.goal p [ 1; 2 ])));
  print_endline (String.concat "  " (List.map (fun a -> ps a ^ " " ^ gshow (gof (Proof.goal p a)) ^ " -> " ^ gshow (gof (Proof.goal q a))) [ []; [ 1 ]; [ 1; 1 ]; [ 1; 2 ]; [ 2 ] ]))
