(* TermOp's small destructors, asked of std (refiner/term_std/term_op_std.ml)
   and ds (refiner/term_ds/term_op_ds.ml): is_quoted_term, is_two_subterm,
   five_subterms and six_subterms, which no unit test, theory build or
   proof census reached on these inputs (2026-11-15 rank).  Each case
   prints both answers (a refusal as its RefineError name) and DIFFER
   where they disagree.  The expected file is the output of the code as
   written (2026-11-15).
   Pinned as found: on a subterm that binds a variable, five_subterms
   and six_subterms refuse from different places (std under its own
   name, ds in dest_simple_bterm), as dest_simple_term_opname does. *)
module Check (R : Refiner_sig.RefinerSig) = struct
  open R.Term
  let op s = Opname.make_opname [ s ]
  let c = mk_simple_term (op "c") []
  let d = mk_simple_term (op "d") []
  let n k = make_param (Term_sig.Number (Lm_num.num_of_int k))
  let simple o ts = mk_simple_term (op o) ts
  let bound o vss = mk_term (mk_op (op o) []) (List.map (fun vs -> mk_bterm (List.map Lm_symbol.add vs) c) vss)
  let params o ps = mk_term (mk_op (op o) ps) []
  let show t = String.concat "!" (Opname.dest_opname (R.Term.dest_op (R.Term.dest_term t).Term_sig.term_op).Term_sig.op_name)
  let ans f = try f () with R.RefineError.RefineError (s, _) -> "refused " ^ s | Invalid_argument s -> "Invalid_argument " ^ s
  let b x = string_of_bool x
  let cases = [
    "is_quoted_term c[q]", (fun () -> b (R.TermOp.is_quoted_term (params "c" [ make_param Term_sig.Quote ])));
    "is_quoted_term c[q; 1:n]", (fun () -> b (R.TermOp.is_quoted_term (params "c" [ make_param Term_sig.Quote; n 1 ])));
    "is_quoted_term c[1:n; q]", (fun () -> b (R.TermOp.is_quoted_term (params "c" [ n 1; make_param Term_sig.Quote ])));
    "is_quoted_term c", (fun () -> b (R.TermOp.is_quoted_term c));
    "is_two_subterm f f{c; d}", (fun () -> b (R.TermOp.is_two_subterm (op "f") (simple "f" [ c; d ])));
    "is_two_subterm f f{c}", (fun () -> b (R.TermOp.is_two_subterm (op "f") (simple "f" [ c ])));
    "is_two_subterm f f{c; d; c}", (fun () -> b (R.TermOp.is_two_subterm (op "f") (simple "f" [ c; d; c ])));
    "is_two_subterm f g{c; d}", (fun () -> b (R.TermOp.is_two_subterm (op "f") (simple "g" [ c; d ])));
    "is_two_subterm f f{x. c; c}", (fun () -> b (R.TermOp.is_two_subterm (op "f") (bound "f" [ [ "x" ]; [] ])));
    "five_subterms f{c; d; c; d; c}", (fun () -> let (a, b2, c2, d2, e) = R.TermOp.five_subterms (simple "f" [ c; d; c; d; c ]) in
                                         String.concat " " (List.map show [ a; b2; c2; d2; e ]));
    "five_subterms f{c; c; c; c}", (fun () -> ignore (R.TermOp.five_subterms (simple "f" [ c; c; c; c ])); "accepted");
    "five_subterms f{c; c; x. c; c; c}", (fun () -> ignore (R.TermOp.five_subterms (bound "f" [ []; []; [ "x" ]; []; [] ])); "accepted");
    "six_subterms f{c; d; c; d; c; d}", (fun () -> let (a, b2, c2, d2, e, f) = R.TermOp.six_subterms (simple "f" [ c; d; c; d; c; d ]) in
                                           String.concat " " (List.map show [ a; b2; c2; d2; e; f ]));
    "six_subterms f{c; c; c; c; c}", (fun () -> ignore (R.TermOp.six_subterms (simple "f" [ c; c; c; c; c ])); "accepted");
    "six_subterms f{c; c; c; c; c; x. c}", (fun () -> ignore (R.TermOp.six_subterms (bound "f" [ []; []; []; []; []; [ "x" ] ])); "accepted") ]
  let answers () = List.map (fun (name, f) -> name, ans f) cases
end

module S = Check (Refiner_std.Refiner)
module D = Check (Refiner_ds.Refiner)

let () =
  List.iter2 (fun (name, s) (_, d) ->
      Printf.printf "%-38s std %s | ds %s%s\n" name s d (if s = d then "" else "  DIFFER"))
    (S.answers ()) (D.answers ())
