(* Rewrite_util.check_arity (refiner/rewrite/rewrite_util.ml): when a
   redex names a second-order variable again, its arity and bound
   contexts must agree with the first occurrence.  Its refusals were
   reached by no unit test, theory build or proof census (2026-11-15
   rank).  Each redex below is compiled (term_rewrite, Strict and
   Relaxed) and prints "compiled" or the RefineError's name and error.
   The expected file is the output of the code as written (2026-11-15).
   Pinned as found: a free variable x and a second-order 'x['y] in one
   redex compile (no check compares their kinds), and a third occurrence
   is then refused, because rstack_check_arity takes the first stack
   entry of that name, the free variable.  A context and a second-order
   variable of one name are refused before check_arity
   (compile_so_redex_term).  Not reachable: rstack_check_arity's []
   arm, since every call follows a membership test that found the name. *)
open Term_sig
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open RefineError

let op s = Opname.make_opname [ s; "Rsa" ]
let v = Lm_symbol.add
let app o ts = mk_term (mk_op (op o) []) (List.map (fun t -> mk_bterm [] t) ts)
let c0 o = app o []
let var x = mk_var_term (v x)
let so ?(conts = []) x args = mk_so_var_term (v x) (List.map v conts) args
let lam x t = mk_term (mk_op (op "lam") []) [ mk_bterm [ v x ] t ]
let err = function
  | RewriteSOVarArity x -> "RewriteSOVarArity " ^ Lm_symbol.string_of_symbol x
  | StringVarError (s, x) -> "StringVarError (" ^ s ^ ", " ^ Lm_symbol.string_of_symbol x ^ ")"
  | StringError s -> "StringError " ^ s
  | _ -> "another error"

let case name redex =
  List.iter (fun (mode, strict) ->
      let r =
        try ignore (Rewrite.term_rewrite strict Rewrite.empty_args_spec [ redex ] [ c0 "k" ]); "compiled"
        with RefineError (s, e) -> "refused " ^ s ^ ": " ^ err e
      in
      Printf.printf "%-44s %-7s %s\n" name mode r) [ "Strict", Rewrite_sig.Strict; "Relaxed", Rewrite_sig.Relaxed ]

let () =
  case "f{'a; 'a} (agree)" (app "f" [ so "a" []; so "a" [] ]);
  case "f{lam x. 'a['x]; lam y. 'a['y]} (agree)" (app "f" [ lam "x" (so "a" [ var "x" ]); lam "y" (so "a" [ var "y" ]) ]);
  case "f{'a; lam x. 'a['x]} (arity 0, then 1)" (app "f" [ so "a" []; lam "x" (so "a" [ var "x" ]) ]);
  case "f{lam x. 'a['x]; 'a} (arity 1, then 0)" (app "f" [ lam "x" (so "a" [ var "x" ]); so "a" [] ]);
  case "f{'a; 'a[c]} (an instance at arity 1)" (app "f" [ so "a" []; so "a" [ c0 "c" ] ]);
  case "f{'a<|H|>; 'a} (bound contexts differ)" (app "f" [ so ~conts:[ "H" ] "a" []; so "a" [] ]);
  case "f{x; lam y. 'x['y]} (a free variable, then SO)" (app "f" [ var "x"; lam "y" (so "x" [ var "y" ]) ]);
  case "f{x; lam y. 'x['y]; lam z. 'x['z]} (a third)" (app "f" [ var "x"; lam "y" (so "x" [ var "y" ]); lam "z" (so "x" [ var "z" ]) ]);
  case "f{C['a]; lam y. 'C['y]} (a context, then SO)" (app "f" [ mk_context_term (v "C") (so "a" []) [] []; lam "y" (so "C" [ var "y" ]) ])
