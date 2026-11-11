(* TermSubst.alpha_equal_fun f t1 vs t2 os: t2 is t1 with, for each free
   occurrence of v_i, some term t such that f t o_i.  The rewriter passes a
   predicate that records each match on its stack (Rewrite_match_redex,
   match_redex_term_pred), so it must run once per occurrence.  The debug
   refiner (TERMS = both) passed it to both implementations, so it ran
   twice, and the rewriter's second run found its stack already filled:
   "match_redex_sequent_hyps : internal error", which made a proof in
   itt_vec_sequent_term incomplete under TERMS = both only.

   This test runs alpha_equal_fun in std alone, ds alone and the debug
   refiner, and prints the answer and how many times the predicate ran,
   for a match, a mismatch of the predicate, a structural mismatch, and a
   predicate that raises.  The expected output is as the code printed it
   when the test was written. *)
module Run (R : Refiner_sig.RefinerSig) = struct
  open R
  let op s = Opname.make_opname [ s ]
  let v = Lm_symbol.add
  let var s = Term.mk_var_term (v s)
  let c s = Term.mk_simple_term (op s) []
  let f a b = Term.mk_simple_term (op "f") [ a; b ]
  let g a = Term.mk_simple_term (op "g") [ a ]

  let case name pred t1 vs t2 os =
    let calls = ref 0 in
    let p t o = incr calls; pred t o in
    let r =
      match TermSubst.alpha_equal_fun p t1 (List.map v vs) t2 os with
      | b -> string_of_bool b
      | exception RefineError.RefineError _ -> "RefineError"
      | exception e -> Printexc.to_string e
    in
    Printf.sprintf "%-34s %-11s predicate ran %d" name r !calls

  let is_c name t _ = TermSubst.alpha_equal t (c name)

  let all () =
    [ case "two occurrences, both match" (fun t o -> is_c o t ()) (f (var "x") (var "x")) [ "x" ] (f (c "a") (c "a")) [ "a" ];
      case "the predicate refuses" (fun t o -> is_c o t ()) (f (var "x") (var "y")) [ "x"; "y" ] (f (c "a") (c "b")) [ "a"; "a" ];
      case "structure differs" (fun _ _ -> true) (f (var "x") (var "x")) [ "x" ] (g (c "a")) [ "a" ];
      case "the predicate raises" (fun _ _ -> raise (RefineError.RefineError ("test", RefineError.StringError "no"))) (g (var "x")) [ "x" ] (g (c "a")) [ "a" ] ]
end

module Std = Run (Refiner_std.Refiner)
module Ds = Run (Refiner_ds.Refiner)
module Dbg = Run (Refiner_debug.MakeRefinerDebug (Refiner_std.Refiner) (Refiner_ds.Refiner))

let () =
  List.iter (fun (name, l) -> List.iter (fun s -> Printf.printf "%-6s %s\n" name s) l)
    [ ("std", Std.all ()); ("ds", Ds.all ()); ("debug", Dbg.all ()) ]
