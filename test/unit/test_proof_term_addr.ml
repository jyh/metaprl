(* Proof_term_boot.mk_addr_term and dest_addr: an address attribute in a
   proof's term form (tactics/proof/proof_term_boot.ml).  No unit test
   wrote one (2026-11-15 profile: mk_addr_term unvisited): an address is
   written only from a wrapped node's argument list, and the tests wrap
   with an int.  Here a proof is refined by
   wrapT (GeneralArgList [| AddrArg a |]) idT  for addresses of each kind
   (subterm, argument, clause) and a mixed one; the line prints the term's
   node, argument and address operators in preorder, before and after the
   term -> raw -> term trip (test_proof_term_kinds' harness).
   Pinned as found: that trip squashes the completed node to
   ext_unjustified, so the wrapped address is not read back
   (dest_addr is reached by test_proof_term_kinds' hand-edited terms).
   The expected file is the output of the code as written, never typed. *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Tactic_boot
open Proof_boot
open Proof_convert
open Tacticals_boot.Tacticals

let at n = mk_simple_term (Opname.make_opname [ n ]) []
let parse _ = raise (Invalid_argument "test_proof_term_addr: parse")
let eval _ = raise (Invalid_argument "test_proof_term_addr: eval")
let ex name = MLast.ExLid (Ploc.dummy, Ploc.VaVal name)
let aeq = TermSubst.alpha_equal
let st = function Proof.StatusBad -> "bad" | Proof.StatusIncomplete -> "incomplete" | Proof.StatusPartial -> "partial" | Proof.StatusComplete -> "complete"
let mk_int_term o i = mk_term (mk_op o [ make_param (Term_sig.Number (Lm_num.num_of_int i)) ]) []
let mk_str_term o v = mk_term (mk_op o [ make_param (Term_sig.String v) ]) []
let nc (a, b) = Printf.sprintf "%d/%d" a b

(* The Summary node and argument operators of a proof term, in preorder. *)
let kinds t =
  let acc = ref [] in
  let rec go t =
    if not (is_var_term t) then begin
      let o = opname_of_term t in
      (match Opname.dest_opname o with
       | n :: _ when String.length n > 4 && (String.sub n 0 4 = "ext_" || String.sub n 0 4 = "arg_" || (String.length n > 7 && String.sub n 0 7 = "status_") || String.sub n 0 5 = "addr_") ->
           acc := n :: !acc
       | _ -> ());
      List.iter (fun bt -> go (dest_bterm bt).bterm) (dest_term t).term_terms
    end
  in
  go t; String.concat " " (List.rev !acc)

let goal_arg () =
  let base = TacticInternal.debug_arg Mp_resource.empty_bookmark (at "A") in
  { base with TacticInternalType.ref_goal = Refine.mk_msequent (at "A") [ at "A" ] }

let to_t io = Convert.to_term () "p" (Convert.of_raw () "p" io)
let back t = Convert.to_raw () "p" (Convert.of_term () "p" t)

let wrapped name a =
  match Proof.refine (fun x -> x) (Proof.create (goal_arg ())) [] name (ex name)
          (TacticInternal.wrapT (GeneralArgList [| AddrArg a |]) idT) with
  | exception e -> Printf.printf "%-28s refine raised %s\n" name (Printexc.to_string e)
  | p ->
      let t = to_t (Proof.io_proof_of_proof false parse eval p) in
      let after = (try kinds (to_t (back t)) with e -> "raised " ^ Printexc.to_string e) in
      Printf.printf "%-28s %s\n  after the term trip:         %s\n" name (kinds t) after

let () =
  let a l = TermAddr.make_address l in
  wrapped "subterm 2" (a [ Term_addr_sig.Subterm 2 ]);
  wrapped "the argument" (a [ Term_addr_sig.ArgAddr ]);
  wrapped "clause 1" (a [ Term_addr_sig.ClauseAddr 1 ]);
  wrapped "clause 1, subterm 1, arg" (a [ Term_addr_sig.ClauseAddr 1; Term_addr_sig.Subterm 1; Term_addr_sig.ArgAddr ]);
  wrapped "the empty address" (a [])
