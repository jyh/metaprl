(* metaprl has two term implementations, term_std and term_ds (the one the
   refiner uses, TERMS = ds). With TERMS = both, the refiner runs both and
   stops on their first disagreement; on 2026-10-29 that build stopped on
   TermAddr.term_subterm at a context hypothesis with arguments, and the
   proof census under TERMS = std lost 90 proofs, all in theories built on
   such contexts. This test builds one sequent in both implementations,
     sequent { <H>; x: A; <K['t1; it]> >- C },
   takes term_subterm at [ClauseAddr i; Subterm j] for every hypothesis i
   (from the left and from the right) and j in -3..3 (j <> 0), and prints
   each implementation's answer and whether they agree; then the two
   implementations' subterm_addresses of the sequent, in order. *)
open Lm_symbol
open Term_sig
open Term_addr_sig

module Show (R : Refiner_sig.RefinerSig) = struct
  open R.Term
  open R.TermMan
  let rec show d t =
    if d > 3 then "…"
    else if is_sequent_term t then
      let (s : R.TermType.esequent) = explode_sequent t in
      let sequent_hyps = s.sequent_hyps and sequent_concl = s.sequent_concl in
      "sequent{ " ^ String.concat "; " (List.map (function
          | Hypothesis (v, a) -> string_of_symbol v ^ ": " ^ show (d + 1) a
          | Context (v, _, args) ->
              "<" ^ string_of_symbol v ^ "[" ^ String.concat "; " (List.map (show (d + 1)) args) ^ "]>")
          (R.Term.SeqHyp.to_list sequent_hyps)) ^ " >- " ^ show (d + 1) sequent_concl ^ " }"
    else if is_var_term t then "'" ^ string_of_symbol (dest_var t)
    else if is_so_var_term t then
      let v, _, args = dest_so_var t in
      string_of_symbol v ^ "[" ^ String.concat "; " (List.map (show (d + 1)) args) ^ "]"
    else if is_context_term t then
      let v, body, _, args = dest_context t in
      "<" ^ string_of_symbol v ^ "[" ^ String.concat "; " (List.map (show (d + 1)) args) ^ "]> "
      ^ show (d + 1) body
    else
      let { term_op; term_terms } = dest_term t in
      let name = String.concat "!" (Opname.dest_opname (dest_op term_op).op_name) in
      if term_terms = [] then name
      else name ^ "{" ^ String.concat "; " (List.map (fun b -> show (d + 1) (dest_bterm b).bterm) term_terms) ^ "}"

  let opname s = Opname.make_opname [ s ]
  let sequent =
    let v = add in
    let h = Context (v "H", [], []) in
    let x = Hypothesis (v "x", mk_simple_term (opname "A") []) in
    let k = Context (v "K", [], [ mk_var_term (v "t1"); mk_simple_term (opname "it") [] ]) in
    mk_sequent_term
      { sequent_args = mk_simple_term (opname "sequent_arg") [];
        sequent_hyps = R.Term.SeqHyp.of_list [ h; x; k ];
        sequent_concl = mk_simple_term (opname "C") [] }

  let addresses =
    String.concat " " (List.map R.TermAddr.string_of_address (R.TermAddr.subterm_addresses sequent))

  let at addr =
    try show 0 (R.TermAddr.term_subterm sequent (R.TermAddr.make_address addr))
    with _ -> "(raises)"
end

module Std = Show (Refiner_std.Refiner)
module Ds = Show (Refiner_ds.Refiner)

let () =
  Printf.printf "std sequent: %s\nds sequent:  %s\n" (Std.show 0 Std.sequent) (Ds.show 0 Ds.sequent);
  let differ = ref 0 and total = ref 0 in
  List.iter (fun i ->
      List.iter (fun j ->
          let addr = [ ClauseAddr i; Subterm j ] in
          let s = Std.at addr and d = Ds.at addr in
          incr total; if s <> d then incr differ;
          Printf.printf "[Clause %d; Subterm %d]  std %s  ds %s%s\n" i j s d (if s = d then "" else "  DIFFER"))
        [ -3; -2; -1; 1; 2; 3 ])
    [ 1; 2; 3; -1; -2; -3 ];
  Printf.printf "%d of %d addresses differ\n" !differ !total;
  (* subterm_addresses lists the addresses of the immediate subterms; tactics
     take them in this order. *)
  let s = Std.addresses and d = Ds.addresses in
  Printf.printf "subterm_addresses\n  std %s\n  ds  %s\n  %s\n" s d (if s = d then "agree" else "DIFFER")
