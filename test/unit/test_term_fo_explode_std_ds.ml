(* TermMan.is_fo_term and explode_term on every kind of term, in term_std
   and term_ds, side by side: an operator with and without a binder, a
   variable, a second-order variable with an argument, a context term and
   a sequent.  term_ds keeps the last four as their own nodes, and bisect
   at a45cd0437 left Term_man_ds.is_fo_term's arms for them, and
   explode_term's for a context, unreached.  explode_term is printed as
   its constructor, the operator's name, and the numbers of parameters and
   subterms (of hypotheses for a sequent).
   Pinned as found: the two disagree on a second-order variable with an
   argument, 'A['b]: term_std's is_fo_term says true (it holds the
   variable as a var operator whose subterms bind nothing) and term_ds's
   says false.  Today's callers (term_ty_infer) also test is_so_var_term
   in the same condition, so their decisions agree; refiner_debug's
   TERMS=both merge would flag a call on such a variable.  The expected
   file is the output of the code. *)
open Term_sig
let v = Lm_symbol.add
module S (R : Refiner_sig.RefinerSig) = struct
  open R.Term
  open R.TermMan
  let op s = Opname.make_opname [ s ]
  let c s = mk_simple_term (op s) []
  let inputs = [
    "f{a}", mk_simple_term (op "f") [ c "a" ];
    "f{x. a}", mk_term (mk_op (op "f") []) [ mk_bterm [ v "x" ] (c "a") ];
    "'x", mk_var_term (v "x");
    "'A['b]", mk_so_var_term (v "A") [] [ c "b" ];
    "'C<|J|>[a]{f{c}}", mk_context_term (v "C") (mk_simple_term (op "f") [ c "c" ]) [ v "J" ] [ c "a" ];
    "s{x: a >- b}", mk_sequent_term { sequent_args = c "sa"; sequent_hyps = R.Term.SeqHyp.of_list [ Hypothesis (v "x", c "a") ]; sequent_concl = c "b" } ]
  let explode t = match explode_term t with
    | MatchTerm (n, ps, bts) -> Printf.sprintf "MatchTerm %s %d param(s) %d subterm(s)" (String.concat "!" n) (List.length ps) (List.length bts)
    | MatchSequent (n, _, hyps, _) -> Printf.sprintf "MatchSequent %s %d hyp(s)" (String.concat "!" n) (List.length hyps)
  let lines () = List.map (fun (n, t) -> n, [ "is_fo_term " ^ string_of_bool (is_fo_term t); (try explode t with e -> Printexc.to_string e) ]) inputs
end
module Std = S (Refiner_std.Refiner)
module Ds = S (Refiner_ds.Refiner)
let () =
  List.iter2 (fun (n, ls) (_, ld) ->
      Printf.printf "%s:\n" n;
      List.iter2 (fun a b -> Printf.printf "  std %s%s\n" a (if a = b then "" else "\n   ds " ^ b)) ls ld)
    (Std.lines ()) (Ds.lines ())
