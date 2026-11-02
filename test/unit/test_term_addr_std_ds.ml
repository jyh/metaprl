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

(* subterm_exists and strip_address (no unit test reached either,
   2026-11-02 profile): subterm_exists t a holds exactly when
   term_subterm t a answers; for every prefix p of an address a,
   strip_address p a composed after p is a again, and stripping an item
   that does not start a fails. *)
module Exists (R : Refiner_sig.RefinerSig) = struct
  module S = Show (R)
  open R.Term
  open R.TermMan
  let op = S.opname
  let c = mk_simple_term (op "c") []
  let terms = [
    S.sequent;
    mk_simple_term (op "f") [ c; mk_simple_term (op "g") [ c ] ];
    mk_term (mk_op (op "lam") []) [ mk_bterm [ add "x" ] (mk_simple_term (op "g") [ mk_var_term (add "x") ]) ];
    mk_so_var_term (add "A") [ add "H" ] [ c; mk_simple_term (op "g") [ c ] ] ]
  let items = [ Subterm 1; Subterm 2; Subterm 3; Subterm (-1); Subterm (-2); ArgAddr; ClauseAddr 0; ClauseAddr 1; ClauseAddr 2; ClauseAddr 3; ClauseAddr (-1); ClauseAddr 4 ]
  let addrs = [] :: List.concat_map (fun a -> [ a ] :: List.map (fun b -> [ a; b ]) items) items
  let check () =
    let tried = ref 0 and ok = ref 0 and exists = ref 0 and first = ref None in
    List.iteri (fun ti t ->
        List.iter (fun a ->
            let addr = R.TermAddr.make_address a in
            let answers = (try ignore (R.TermAddr.term_subterm t addr); true with _ -> false) in
            let says = (try R.TermAddr.subterm_exists t addr with _ -> not answers) in
            incr tried; if says then incr exists;
            if says = answers then incr ok
            else if !first = None then first := Some (Printf.sprintf "term %d at %s: subterm_exists %b, term_subterm %s" ti (R.TermAddr.string_of_address addr) says (if answers then "answers" else "raises")))
          addrs)
      terms;
    let st = ref 0 and sok = ref 0 and sfirst = ref None in
    List.iter (fun a ->
        let addr = R.TermAddr.make_address a in
        List.iteri (fun k _ ->
            let p = List.filteri (fun i _ -> i < k) a in
            incr st;
            let good = (try R.TermAddr.dest_address (R.TermAddr.compose_address (R.TermAddr.make_address p) (R.TermAddr.strip_address p addr)) = a with _ -> false) in
            if good then incr sok else if !sfirst = None then sfirst := Some (R.TermAddr.string_of_address addr))
          (a @ [ ArgAddr ]);
        match a with
        | x :: _ ->
            let other = if x = Subterm 1 then Subterm 2 else Subterm 1 in
            incr st;
            if (try ignore (R.TermAddr.strip_address [ other ] addr); false with _ -> true) then incr sok
            else if !sfirst = None then sfirst := Some ("strip a non-prefix of " ^ R.TermAddr.string_of_address addr)
        | [] -> ())
      addrs;
    !tried, !ok, !exists, !first, !st, !sok, !sfirst
end

module Std = Show (Refiner_std.Refiner)
module Ds = Show (Refiner_ds.Refiner)
module Estd = Exists (Refiner_std.Refiner)
module Eds = Exists (Refiner_ds.Refiner)

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
;;
let () =
  List.iter (fun (name, (tried, ok, exists, first, st, sok, sfirst)) ->
      Printf.printf "%s: subterm_exists iff term_subterm answers: %d of %d (%d exist)\n" name ok tried exists;
      (match first with None -> () | Some w -> Printf.printf "  first difference: %s\n" w);
      Printf.printf "%s: strip_address inverts compose_address: %d of %d\n" name sok st;
      match sfirst with None -> () | Some w -> Printf.printf "  first difference: %s\n" w)
    [ "std", Estd.check (); "ds", Eds.check () ]
;;
(* Recorded, not endorsed: on a sequent, term_std answers plain Subterm
   addresses by walking its own encoding of the sequent (hyp!Perv{...}
   terms), where term_ds refuses them; on the other terms they agree. *)
let () =
  let differ = ref 0 and total = ref 0 and first = ref None in
  List.iteri (fun ti (ts, td) ->
      List.iter (fun a ->
          let e1 = (try Refiner_std.Refiner.TermAddr.subterm_exists ts (Refiner_std.Refiner.TermAddr.make_address a) with _ -> false)
          and e2 = (try Refiner_ds.Refiner.TermAddr.subterm_exists td (Refiner_ds.Refiner.TermAddr.make_address a) with _ -> false) in
          incr total;
          if e1 <> e2 then begin
            incr differ;
            if !first = None then first := Some (Printf.sprintf "term %d at %s: std %b, ds %b" ti (Refiner_std.Refiner.TermAddr.string_of_address (Refiner_std.Refiner.TermAddr.make_address a)) e1 e2)
          end)
        Estd.addrs)
    (List.combine Estd.terms Eds.terms);
  Printf.printf "std and ds disagree on whether a subterm exists at %d of %d (term, address) pairs\n" !differ !total;
  match !first with None -> () | Some w -> Printf.printf "  first: %s\n" w
