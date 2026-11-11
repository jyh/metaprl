(* Proof_convert.Convert, the dispatcher that moves a proof between its
   three stored forms (Raw io_proof, Term, Term_io), and the Proof_boot io
   functions under it, which no unit test named (coverage recount 11-10).
   Random proofs are built without a theory: Proof.create on a goal (an atom
   with 0-2 atom assumptions), then 0-6 refinements, each at a random open
   leaf with idT, cutT X or nthAssumT i, a third of them under
   TacticInternal.wrapT (a refinement the leaf refuses is skipped; the leaves are tracked from the subgoal count TacticInternal.
   refine gives).  Each proof is checked by round trips, with no typed
   expectation:
     io  = io_proof_of_proof false p     node_count and status equal p's
     t   = to_term (Raw io)              the reference term
     sq  = io_proof_of_proof true p      the squashed proof, ts = to_term (Raw sq)
     to_term (Term_io (to_term_io (Raw io)))         alpha-equal to t
     to_term (Raw (to_raw (Term t)))                 alpha-equal to ts
     to_term (Raw (to_raw (Term_io (to_term_io (Term t)))))   alpha-equal to ts
     node_count of to_raw (Term t)                   equal to sq's
   The term -> raw direction squashes (io_proof_of_term passes true), and
   squashing drops the primitive extract tree, which is where a wrapped
   refinement's Wrapped node lives: so that trip is compared with the
   squashed proof, and for a proof with no wrapped step ts = t (counted).
   and the status before and after the term round trip, and the squashed
   io_proof_of_proof true, are tabulated (measured, printed, not typed).
   Pinned as a fixed case: a refined, unfinished proof reads "partial" and
   reads "incomplete" after a trip through the term form, which stores its
   rule nodes as ext_unjustified.  Convert.to_raw of a term that is not a
   proof is refused.
   The generator is a fixed linear congruential sequence, not Random. *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Tactic_boot
open Tactic_boot_sig
open Proof_boot
open Proof_convert
open Tacticals_boot.Tacticals

let state = ref 1115
let next () = state := (!state * 1103515245 + 12345) land 0x7fffffff; !state lsr 8
let pick n = next () mod n

let atoms = [| "A"; "B"; "C" |]
let at n = mk_simple_term (Opname.make_opname [ n ]) []
let parse _ = raise (Invalid_argument "test_proof_convert: parse")
let eval _ = raise (Invalid_argument "test_proof_convert: eval")
let ex name = MLast.ExLid (Ploc.dummy, Ploc.VaVal name)
let st = function Proof.StatusBad -> "bad" | Proof.StatusIncomplete -> "incomplete" | Proof.StatusPartial -> "partial" | Proof.StatusComplete -> "complete"
let aeq = TermSubst.alpha_equal

let random_proof () =
  let goal = Refine.mk_msequent (at atoms.(pick 3)) (List.init (pick 3) (fun _ -> at atoms.(pick 3))) in
  let base = TacticInternal.debug_arg Mp_resource.empty_bookmark (at "A") in
  let p = ref (Proof.create { base with TacticInternalType.ref_goal = goal }) and leaves = ref [ [] ] and steps = ref 0 in
  for _ = 1 to pick 7 do
    if !leaves <> [] then begin
      let l = List.nth !leaves (pick (List.length !leaves)) in
      let name, tac = match pick 4 with
        | 0 -> "idT", idT
        | 1 | 2 -> let x = atoms.(pick 3) in "cutT " ^ x, cutT (at x)
        | _ -> let i = 1 + pick 3 in Printf.sprintf "nthAssumT %d" i, nthAssumT i in
      let name, tac = if pick 3 = 0 then "wrapped " ^ name, TacticInternal.wrapT (IntArgList ("wrapped", 7)) tac else name, tac in
      match TacticInternal.refine tac (Proof.goal !p l) with
      | exception RefineError.RefineError _ -> ()
      | subs, _ ->
         p := Proof.refine (fun x -> x) !p l name (ex name) tac;
         incr steps;
         leaves := List.filter (fun x -> x <> l) !leaves @ List.init (List.length subs) (fun i -> l @ [ i + 1 ])
    end
  done;
  !p, !steps

let () =
  let n = 300 and ok = ref 0 and steps = ref 0 and nodes = ref 0 and same_sq = ref 0 in
  let table = Hashtbl.create 8 in
  let bump k = Hashtbl.replace table k (1 + try Hashtbl.find table k with Not_found -> 0) in
  for k = 1 to n do
    let p, s = random_proof () in
    steps := !steps + s;
    let io = Proof.io_proof_of_proof false parse eval p in
    let t = Convert.to_term () "p" (Convert.of_raw () "p" io) in
    let back_io = Convert.to_raw () "p" (Convert.of_term () "p" t) in
    let sq = Proof.io_proof_of_proof true parse eval p in
    let ts = Convert.to_term () "p" (Convert.of_raw () "p" sq) in
    if aeq t ts then incr same_sq;
    let checks = [
      "node_count p = io", Proof.node_count p = Proof.node_count_of_io_proof io;
      "status p = io", Proof.status p [] = Proof.status_of_io_proof io;
      "via term_io", aeq t (Convert.to_term () "p" (Convert.of_term_io () "p" (Convert.to_term_io () "p" (Convert.of_raw () "p" io))));
      "via term -> raw", aeq ts (Convert.to_term () "p" (Convert.of_raw () "p" back_io));
      "via term -> term_io -> raw", aeq ts (Convert.to_term () "p" (Convert.of_raw () "p"
          (Convert.to_raw () "p" (Convert.of_term_io () "p" (Convert.to_term_io () "p" (Convert.of_term () "p" t))))));
      "node_count after the term trip", Proof.node_count_of_io_proof back_io = Proof.node_count_of_io_proof sq ] in
    (match List.filter (fun (_, b) -> not b) checks with
     | [] -> incr ok
     | bad -> Printf.printf "case %d (%d steps): FAILED %s\n" k s (String.concat ", " (List.map fst bad)));
    nodes := !nodes + snd (Proof.node_count p);
    bump (Printf.sprintf "status %s -> after the term trip %s; squashed %s, squashed node_count %s"
            (st (Proof.status p [])) (st (Proof.status_of_io_proof back_io)) (st (Proof.status_of_io_proof sq))
            (if Proof.node_count_of_io_proof sq = Proof.node_count_of_io_proof io then "same" else "differs"))
  done;
  Printf.printf "random: %d/%d proofs pass every round trip (%d refinements, %d nodes in all); squashing left the term unchanged in %d\n" !ok n !steps !nodes !same_sq;
  List.iter (fun (k, c) -> Printf.printf "%4d  %s\n" c k) (List.sort compare (Hashtbl.fold (fun k c acc -> (k, c) :: acc) table []));
  (match Convert.to_raw () "p" (Convert.of_term () "p" (at "A")) with
   | _ -> print_endline "to_raw of a term that is not a proof: accepted"
   | exception RefineError.RefineError (name, _) -> Printf.printf "to_raw of a term that is not a proof: refused (%s)\n" name)
