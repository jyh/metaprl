(* Proof_term_boot.mk_status_term, the rule status a proof term records
   (tactics/proof/proof_term_boot.ml).  test_proof_term_kinds writes each
   proof's term before asking its status, and every term it writes says
   status_incomplete, the complete proof's too (2026-11-15 profile: the
   bad, partial and complete arms unvisited).  Here each proof's term is
   written before and after Proof.status is asked, and the line prints
   the status and the status operators the term holds, in preorder.
   Pinned as it reads today: the term says status_incomplete in every
   case, even after the status is known to be complete.  The term is
   written from the raw form (Proof.term_of_io_proof), whose
   proof_of_io_proof rebuilds each rule box with LazyStatusDelayed
   (proof_boot.ml), and mk_status_term writes Delayed as incomplete; the
   reader (test_proof_term_kinds) does not read the status back either.
   So the bad, partial and complete arms have no caller that reaches
   them: every path to the encoder goes through proof_of_io_proof. *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Tactic_boot
open Proof_boot
open Proof_convert
open Tacticals_boot.Tacticals

let at n = mk_simple_term (Opname.make_opname [ n ]) []
let parse _ = raise (Invalid_argument "test_proof_status_term: parse")
let eval _ = raise (Invalid_argument "test_proof_status_term: eval")
let ex name = MLast.ExLid (Ploc.dummy, Ploc.VaVal name)
let st = function Proof.StatusBad -> "bad" | Proof.StatusIncomplete -> "incomplete" | Proof.StatusPartial -> "partial" | Proof.StatusComplete -> "complete"

(* The status_* operators of a term, in preorder. *)
let statuses t =
  let acc = ref [] in
  let rec go t =
    if not (is_var_term t) then begin
      (match Opname.dest_opname (opname_of_term t) with
       | n :: _ when String.length n > 7 && String.sub n 0 7 = "status_" -> acc := n :: !acc
       | _ -> ());
      List.iter (fun bt -> go (dest_bterm bt).bterm) (dest_term t).term_terms
    end
  in
  go t; String.concat " " (List.rev !acc)

let goal_arg () =
  let base = TacticInternal.debug_arg Mp_resource.empty_bookmark (at "A") in
  { base with TacticInternalType.ref_goal = Refine.mk_msequent (at "A") [ at "A" ] }

let term_of p = Convert.to_term () "p" (Convert.of_raw () "p" (Proof.io_proof_of_proof false parse eval p))

let case name tac =
  match Proof.refine (fun x -> x) (Proof.create (goal_arg ())) [] name (ex name) tac with
  | exception e -> Printf.printf "%-36s refine raised %s\n" name (Printexc.to_string e)
  | p ->
      let before = statuses (term_of p) in
      let s = st (Proof.status p []) in
      let after = statuses (term_of p) in
      Printf.printf "%-36s status %s\n   term before: %s\n   term after:  %s\n" name s before after

let () =
  let b = at "B" in
  List.iter (fun (n, tac) -> case n tac) [
    "nthAssumT 1", nthAssumT 1;
    "idT", idT;
    "cutT B", cutT b;
    "cutT B thenLT [idT; nthAssumT 1]", prefix_thenLT (cutT b) [ idT; nthAssumT 1 ];
  ]
