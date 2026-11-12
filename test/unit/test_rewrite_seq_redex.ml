(* The rewriter's redex paths for sequent contexts WITH ARGUMENTS and for
   second-order variables that occur twice (refiner/rewrite
   rewrite_match_redex.ml match_context_instance, rewrite_compile_redex.ml
   SOVarInstance), which only the proof census reached (2026-11-11 reach
   census: 65 lines of the two files reached by the census and by no unit
   test, the open PRs' tests included).  test_rewrite_shapes swaps the
   conclusions of two sequents sharing a context with no arguments; here
   the context carries one, <J['x]>, H is the rule's int argument (as in
   test_rewrite_args: the position of x, 2 when one hypothesis precedes
   it, else 1), and the rule is applied in term_std
   and term_ds (Refiner_std, Refiner_ds) to fixed terms.  Each case prints
   the result (printed as test_rewrite_shapes prints) or that the rewrite
   is refused; every outcome is the code's
   own (measured 2026-11-11), and the two representations must agree.
     swapJ  pair{ s{<H>; x: 'A; <J['x]> >- 'C['x]} ;
                  s{<H>; x: 'A; <J['x]> >- 'D['x]} }
        --> pair{ s{<H>; x: 'A; <J['x]> >- 'D['x]} ;
                  s{<H>; x: 'A; <J['x]> >- 'C['x]} }
     same   pair{ lam{x. 'b['x]} ; lam{y. 'b['y]} } --> 'b[c]
            ('b occurs twice: the second is an instance of the first)
   swapJ is also applied to sequent SCHEMAS (terms that contain contexts
   themselves, as rule statements do), where the second sequent's
   contexts are matched against the first's: name, context list and
   arguments must agree.
   Not covered (measured, still census-only): contexts restricted by a
   rule argument (Rewrite_compile_redex.map_restricts, the
   StackContextRestrict paths of hyp_clashes), operator parameters
   (RWOperator, RWMOperator), and the compile path of a second-order
   instance with subterms (SOVarInstance). *)
open Term_sig

let v = Lm_symbol.add

module Make (R : Refiner_sig.RefinerSig) = struct
  open R.Term
  open R.TermMan
  let op s = Opname.make_opname [ s ]
  let mk s ts = mk_simple_term (op s) ts
  let c = mk "c" [] and a = mk "a" [] and b = mk "b" []
  let g x = mk "g" [ x ]
  let pair x y = mk "pair" [ x; y ]
  let lam x t = mk_term (mk_op (op "lam") []) [ mk_bterm [ v x ] t ]
  let var x = mk_var_term (v x)
  let sov ?(conts = []) x args = mk_so_var_term (v x) (List.map v conts) args
  let seq hyps concl = mk_sequent_term { sequent_args = mk "s" []; sequent_hyps = R.Term.SeqHyp.of_list hyps; sequent_concl = concl }
  let rec show_term t =
    if is_var_term t then "'" ^ Lm_symbol.string_of_symbol (dest_var t)
    else if is_sequent_term t then
      let s = explode_sequent t in
      "sequent{ " ^ String.concat "; " (List.map (function Hypothesis (x, a) -> Lm_symbol.string_of_symbol x ^ ": " ^ show_term a | Context (x, _, _) -> "<" ^ Lm_symbol.string_of_symbol x ^ ">")
                                           (R.Term.SeqHyp.to_list s.sequent_hyps)) ^ " >- " ^ show_term s.sequent_concl ^ " }"
    else
      let { term_op; term_terms } = dest_term t in
      let name = String.concat "!" (Opname.dest_opname (dest_op term_op).op_name) in
      if term_terms = [] then name
      else name ^ "{" ^ String.concat "; " (List.map (fun b -> let { bvars; bterm } = dest_bterm b in
                                                 (if bvars = [] then "" else String.concat "," (List.map Lm_symbol.string_of_symbol bvars) ^ ". ") ^ show_term bterm) term_terms) ^ "}"
  let show = show_term

  (* the rules *)
  let hctx = Context (v "H", [], [])
  let jctx = Context (v "J", [ v "H" ], [ var "x" ])
  let side concl = seq [ hctx; Hypothesis (v "x", sov ~conts:[ "H" ] "A" []); jctx ] (sov ~conts:[ "H"; "J" ] concl [ var "x" ])
  let swapJ = R.Rewrite.term_rewrite Rewrite_sig.Strict { Rewrite_sig.spec_ints = [| v "H" |]; spec_addrs = [||] } [ pair (side "C") (side "D") ] [ pair (side "D") (side "C") ]
  let same = R.Rewrite.term_rewrite Rewrite_sig.Strict R.Rewrite.empty_args_spec [ pair (lam "x" (sov "b" [ var "x" ])) (lam "y" (sov "b" [ var "y" ])) ] [ sov "b" [ c ] ]
  let apply_k k rw t = try String.concat " | " (List.map show (R.Rewrite.apply_rewrite rw ({ Rewrite_sig.arg_ints = [| k |]; arg_addrs = [||] }, Lm_symbol.SymbolSet.empty) t [])) with R.RefineError.RefineError _ -> "refused"
  let apply rw t = try String.concat " | " (List.map show (R.Rewrite.apply_rewrite rw R.Rewrite.empty_args t [])) with R.RefineError.RefineError _ -> "refused"

  (* concrete sequents: z: a; y: g{z} (J's part, which may mention x) *)
  let s hyps concl = seq (List.map (fun (x, t) -> Hypothesis (v x, t)) hyps) concl
  let cases =
    [ "swapJ, the same hypotheses",
        apply_k 2 swapJ (pair (s [ "u", b; "x", a; "y", g (var "x") ] (g (var "x"))) (s [ "u", b; "x", a; "y", g (var "x") ] c));
      "swapJ, J's part differs (g{x} vs g{u})",
        apply_k 2 swapJ (pair (s [ "u", b; "x", a; "y", g (var "x") ] c) (s [ "u", b; "x", a; "y", g (var "u") ] c));
      "swapJ, J's part has one hypothesis more",
        apply_k 2 swapJ (pair (s [ "u", b; "x", a; "y", c ] c) (s [ "u", b; "x", a; "y", c; "w", c ] c));
      "swapJ, H differs",
        apply_k 2 swapJ (pair (s [ "u", b; "x", a ] c) (s [ "u", a; "x", a ] c));
      "swapJ, x's hypothesis differs",
        apply_k 1 swapJ (pair (s [ "x", a ] c) (s [ "x", b ] c));
      "swapJ, the variable named differently in each",
        apply_k 1 swapJ (pair (s [ "x", a; "y", g (var "x") ] (var "x")) (s [ "z", a; "y", g (var "z") ] (var "z")));
      "swapJ on schemas <K>; x: a; <L<|K|>['x]>, equal",
        apply_k 2 swapJ (pair (seq [ Context (v "K", [], []); Hypothesis (v "x", a); Context (v "L", [ v "K" ], [ var "x" ]) ] c)
                              (seq [ Context (v "K", [], []); Hypothesis (v "x", a); Context (v "L", [ v "K" ], [ var "x" ]) ] b));
      "swapJ on schemas, L vs M",
        apply_k 2 swapJ (pair (seq [ Context (v "K", [], []); Hypothesis (v "x", a); Context (v "L", [ v "K" ], [ var "x" ]) ] c)
                              (seq [ Context (v "K", [], []); Hypothesis (v "x", a); Context (v "M", [ v "K" ], [ var "x" ]) ] b));
      "swapJ on schemas, L['x] vs L[c]",
        apply_k 2 swapJ (pair (seq [ Context (v "K", [], []); Hypothesis (v "x", a); Context (v "L", [ v "K" ], [ var "x" ]) ] c)
                              (seq [ Context (v "K", [], []); Hypothesis (v "x", a); Context (v "L", [ v "K" ], [ c ]) ] b));
      "swapJ on schemas, L<|K|> vs L<||>",
        apply_k 2 swapJ (pair (seq [ Context (v "K", [], []); Hypothesis (v "x", a); Context (v "L", [ v "K" ], [ var "x" ]) ] c)
                              (seq [ Context (v "K", [], []); Hypothesis (v "x", a); Context (v "L", [], [ var "x" ]) ] b));
      "same, lam{x. g{x}} and lam{y. g{y}}", apply same (pair (lam "x" (g (var "x"))) (lam "y" (g (var "y"))));
      "same, lam{x. g{x}} and lam{y. c}", apply same (pair (lam "x" (g (var "x"))) (lam "y" c));
      "same, lam{x. c} and lam{y. c}", apply same (pair (lam "x" c) (lam "y" c)) ]
end

module S = Make (Refiner_std.Refiner)
module D = Make (Refiner_ds.Refiner)

let () =
  List.iter2 (fun (name, rs) (_, rd) ->
      Printf.printf "%-46s %s\n" name (if rs = rd then rs else "std: " ^ rs ^ "  DIFFERS FROM ds: " ^ rd))
    S.cases D.cases
