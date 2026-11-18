(* Proof_boot.Proof.squash: below the squashed address every rule box
   keeps its subgoals but its extract becomes Unjustified (squash_kill_ext;
   a wrapped extract is first walked by squash_check_ext), so its status is
   incomplete, and incomplete wins over partial and complete on the way up
   (compute_status_subgoals).  An unwrapped idT step is the exception: its
   extract is an Identity, which squash_kill_ext keeps, so it stays complete
   (in these proofs an unwrapped step with one subgoal is always idT).  Random proofs as in test_proof_boot; each is
   squashed at a random address (a leaf too, where nothing changes), and
   the proof is compared at every address with a model: is_leaf and the
   goal unchanged; status = incomplete for a refined node that is squashed
   or has a squashed refined node below it, else as before (a leaf is
   partial; a node is complete when all its subgoals are); node_count
   with a squashed wrapped refinement counted as unwrapped (2, not 3);
   child 0.0 of a squashed wrapped refinement is refused. *)
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


let pre a b = let rec go = function [], _ -> true | x :: r, y :: s -> x = y && go (r, s) | _ -> false in go (a, b)
let rec mstatus sq p = function
  | Leaf _ -> "partial"
  | Node (_, w, cs) ->
     let ks = List.mapi (fun i c -> mstatus sq (p @ [ i + 1 ]) c) cs in
     let identity = not w && List.length cs = 1 in
     if (sq p && not identity) || List.mem "incomplete" ks then "incomplete" else if List.for_all (( = ) "complete") ks then "complete" else "partial"
let rec mcount sq p = function
  | Leaf _ -> (0, 1)
  | Node (_, w, cs) -> List.fold_left (fun (r, n) (i, c) -> let r', n' = mcount sq (p @ [ i ]) c in r + r', n + n') (1, if w && not (sq p) then 3 else 2) (List.mapi (fun i c -> (i + 1, c)) cs)

let () =
  let n = 300 and good = ref 0 and checks = ref 0 and inc = ref 0 and wsq = ref 0 and leafsq = ref 0 in
  for k = 1 to n do
    let p, sh = build () in
    let all = addrs sh [] in
    let a = List.nth all (pick (List.length all)) in
    (match get sh a with Leaf _ -> incr leafsq | Node _ -> ());
    let sq b = pre a b in
    let p = Proof.squash (fun x -> x) p a in
    let bad = ref [] in
    let chk what b = incr checks; if not b then bad := what :: !bad in
    let ps a = String.concat "." (List.map string_of_int a) in
    let refused f = match f () with _ -> false | exception RefineError.RefineError _ -> true in
    chk "node_count" (Proof.node_count p = mcount sq [] sh);
    List.iter (fun b ->
        let t = get sh b in
        let ms = mstatus sq b t in
        if ms = "incomplete" then incr inc;
        chk ("is_leaf " ^ ps b) (Proof.is_leaf p b = (match t with Leaf _ -> true | Node _ -> false));
        chk ("goal " ^ ps b) (gkey (Proof.goal p b) = key t);
        chk ("status " ^ ps b) (st (Proof.status p b) = ms);
        (match t with
         | Node (_, true, _) when sq b -> incr wsq; chk ("refused 0.0 of " ^ ps b) (refused (fun () -> Proof.is_leaf p (b @ [ 0; 0 ])))
         | _ -> ()))
      all;
    if !bad = [] then incr good else Printf.printf "proof %d (squashed at %s): FAILED %s\n" k (ps a) (String.concat ", " (List.rev !bad))
  done;
  Printf.printf "squashed: %d/%d proofs agree with the model (%d checks)\n" !good n !checks;
  Printf.printf "%d addresses incomplete after the squash; %d squashed wrapped refinements; %d squashes at a leaf\n" !inc !wsq !leafsq
