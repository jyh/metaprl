(* Operator parameters in the rewriter (refiner/rewrite: RWOperator and
   RWMOperator in rewrite_compile_redex.ml and rewrite_match_redex.ml, and
   the instance check of a meta operator that occurs twice), which only the
   proof census reached (2026-11-11 reach census).  An operator parameter
   names an operator (an opname, its parameters, its arities), as
   h[op:op] does in the theories.  Four rules, compiled and applied in
   term_std and term_ds (Refiner_std, Refiner_ds), which must agree:
     lit    h[f/0]                 --> c     (a literal operator f, arity [0])
     meta   h[@o:op]               --> k[@o:op]
     twice  pair{h[@o:op]; h[@o:op]} --> c   (the same operator twice)
     ttwice pair{t[@o:t]; t[@o:t]}   --> c   (the same token twice)
   Each case prints the result or that the rewrite is refused; every
   outcome is the code's own (measured 2026-11-11).  The operator is
   compared by name, parameters and arities; a meta operator in the term
   (a schema) is matched by a meta operator in the redex.
   ttwice is the instance check for a token (opname) parameter that occurs
   twice (StackOpname). *)
open Term_sig

let v = Lm_symbol.add

module Make (R : Refiner_sig.RefinerSig) = struct
  open R.Term
  let op s = Opname.make_opname [ s ]
  let mk s ts = mk_simple_term (op s) ts
  let c = mk "c" []
  let opp ?(arities = [ 0 ]) name = make_param (Operator { opparam_name = op name; opparam_params = []; opparam_arities = arities })
  let mop x = make_param (MOperator (v x))
  let h p = mk_term (mk_op (op "h") [ p ]) []
  let k p = mk_term (mk_op (op "k") [ p ]) []
  let pair a b = mk "pair" [ a; b ]
  let rule redex contractum = R.Rewrite.term_rewrite Rewrite_sig.Strict R.Rewrite.empty_args_spec [ redex ] [ contractum ]
  let show t =
    let { term_op; _ } = dest_term t in
    let { op_name; op_params } = dest_op term_op in
    let ps = List.map (fun p -> match dest_param p with
        | Operator o -> String.concat "!" (Opname.dest_opname o.opparam_name) ^ "/" ^ String.concat "," (List.map string_of_int o.opparam_arities)
        | MOperator x -> "@" ^ Lm_symbol.string_of_symbol x
        | _ -> "?") op_params in
    String.concat "!" (Opname.dest_opname op_name) ^ (if ps = [] then "" else "[" ^ String.concat "; " ps ^ "]")
  let apply rw t = try String.concat " | " (List.map show (R.Rewrite.apply_rewrite rw R.Rewrite.empty_args t [])) with R.RefineError.RefineError _ -> "refused"
  let lit = rule (h (opp "f")) c
  let meta = rule (h (mop "o")) (k (mop "o"))
  let twice = rule (pair (h (mop "o")) (h (mop "o"))) c
  let tok p = mk_term (mk_op (op "t") [ p ]) []
  let ttok s = make_param (Token (Opname.make_opname [ s ]))
  let mtok x = make_param (MToken (v x))
  let ttwice = rule (pair (tok (mtok "o")) (tok (mtok "o"))) c
  let cases =
    [ "lit on h[f/0]", apply lit (h (opp "f"));
      "lit on h[g/0]", apply lit (h (opp "g"));
      "lit on h[f/1]", apply lit (h (opp ~arities:[ 1 ] "f"));
      "lit on h[f/0,0]", apply lit (h (opp ~arities:[ 0; 0 ] "f"));
      "meta on h[f/2]", apply meta (h (opp ~arities:[ 2 ] "f"));
      "meta on h[@p] (a schema)", apply meta (h (mop "p"));
      "twice on pair{h[f/0]; h[f/0]}", apply twice (pair (h (opp "f")) (h (opp "f")));
      "twice on pair{h[f/0]; h[g/0]}", apply twice (pair (h (opp "f")) (h (opp "g")));
      "twice on pair{h[f/0]; h[f/1]}", apply twice (pair (h (opp "f")) (h (opp ~arities:[ 1 ] "f")));
      "twice on pair{h[@p]; h[@p]} (a schema)", apply twice (pair (h (mop "p")) (h (mop "p")));
      "twice on pair{h[@p]; h[@q]}", apply twice (pair (h (mop "p")) (h (mop "q")));
      "lit on h[@p] (a schema)", apply lit (h (mop "p"));
      "ttwice on pair{t[Foo]; t[Foo]}", apply ttwice (pair (tok (ttok "Foo")) (tok (ttok "Foo")));
      "ttwice on pair{t[Foo]; t[Bar]}", apply ttwice (pair (tok (ttok "Foo")) (tok (ttok "Bar"))) ]
end

module S = Make (Refiner_std.Refiner)
module D = Make (Refiner_ds.Refiner)

let () =
  List.iter2 (fun (name, rs) (_, rd) ->
      Printf.printf "%-40s %s\n" name (if rs = rd then rs else "std: " ^ rs ^ "  DIFFERS FROM ds: " ^ rd))
    S.cases D.cases
