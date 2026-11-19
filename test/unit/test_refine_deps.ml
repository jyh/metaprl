(* Refine.compute_dependencies over a refiner that joined another (through
   its label) and holds ML rules, an ML rewrite and a justified rewrite:
   what each name depends on, or the refusal.  compute_deps_set's ML and
   label arms are unreachable, stated: find_refiner, which it calls first,
   refuses an ML rule or rewrite ("ML rules/rewrites can't be justified")
   and never returns a label (a label's name is Not_found).  The harness
   is test_refine_build's.
   The expected file is the output of the code as written (2026-11-16),
   never typed. *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.Refine
open Refiner.Refiner.RefineError

let op s = Opname.make_opname [ s ]
let v = Lm_symbol.add
let mk s ts = mk_simple_term (op s) ts
let c = mk "c" []
let g x = mk "g" [ x ]
let f x y = mk "f" [ x; y ]
let sov ?(conts = []) x args = mk_so_var_term (v x) (List.map v conts) args
let var x = mk_var_term (v x)
let bind name bvars t = mk_term (mk_op (op name) []) [ mk_bterm (List.map v bvars) t ]
let show t = String.concat " " (List.filter (( <> ) "") (List.map String.trim (String.split_on_char '\n' (Simple_print.SimplePrint.string_of_term t))))

let rec msg = function
  | StringError s -> s
  | StringTermError (s, t) -> s ^ ": " ^ show t
  | StringStringError (s, t) -> s ^ ": " ^ t
  | RewriteFreeSOVar x -> "RewriteFreeSOVar " ^ Lm_symbol.to_string x
  | StringErrorError (s, e) -> s ^ ": " ^ msg e
  | StringVarError (s, x) -> s ^ ": " ^ Lm_symbol.to_string x
  | RewriteFreeContextVar (x, y) -> "RewriteFreeContextVar " ^ Lm_symbol.to_string x ^ " " ^ Lm_symbol.to_string y
  | RewriteMissingContextArg x -> "RewriteMissingContextArg " ^ Lm_symbol.to_string x
  | RewriteSOVarArity x -> "RewriteSOVarArity " ^ Lm_symbol.to_string x
  | RewriteStringError s -> s
  | VarError x -> "VarError " ^ Lm_symbol.to_string x
  | StringWrapError (s, e) -> s ^ ": " ^ msg e
  | VarErrorError (x, e) -> Lm_symbol.to_string x ^ ": " ^ msg e
  | _ -> "(another refine_error)"
let attempt label fn =
  Printf.printf "%-60s %s\n%!" label
    (try fn () with
     | RefineError (n, e) -> "refused (" ^ n ^ ": " ^ msg e ^ ")"
     | Invalid_argument s -> "Invalid_argument " ^ s
     | Not_found -> "Not_found"
     | Failure s -> "Failure " ^ s)

(* the result of rewriting [t] with [rw] under [sent], or the refusal *)
let rewrite sent rw t =
  match refine sent (rwtactic 0 rw) (mk_msequent t []) with
  | [ m ], _ -> "rewrites to " ^ show (msequent_goal m)
  | _, _ -> "several subgoals"
let prim = function PrimRW r -> r | CondRW _ -> failwith "cond"
let sentinel b = sentinal_of_refiner (refiner_of_build b)

(* a rule  c --> name{c}  with a primitive extract, and how it applies *)
let rule b name =
  let mt = Term_sig.MetaImplies (Term_sig.MetaTheorem c, Term_sig.MetaTheorem (mk name [ c ])) in
  let tac = create_rule b name Rewrite.empty_args_spec [] mt in
  prim_rule b name Rewrite.empty_args_spec [] mt [ sov "e" [] ] (sov "e" []);
  tac
let applies sent tac name =
  match refine sent (tac Rewrite.empty_rw_args []) (mk_msequent (mk name [ c ]) []) with
  | _ -> "accepted"
  | exception RefineError _ -> "refused"

let deps r name =
  String.concat ", " (List.map (fun (d, o) ->
      (match d with Refine_sig.DepDefinition -> "definition" | Refine_sig.DepRule -> "rule" | Refine_sig.DepRewrite -> "rewrite" | Refine_sig.DepCondRewrite -> "cond_rewrite") ^ " " ^ Opname.string_of_opname o)
    (compute_dependencies r name))
let opn s n = Opname.make_opname [ n; s ]
let () =
  let a = null_refiner "test_refine_deps_a" in
  ignore (rule a "ra");
  let la = label_refiner a "A" in
  let m = null_refiner "test_refine_deps_ml" in
  join_refiner m la;
  let mlr _ mseq _ = [ mseq ], (fun _ _ _ _ _ fs -> match fs with [ h ] -> h [] | _ -> c) in
  ignore (create_ml_rule m "mlr" mlr);
  ignore (create_ml_rewrite m "mlrw" (fun t -> t));
  ignore (create_rewrite m "pw" (g (sov "a" [])) (sov "a" []));
  prim_rewrite m "pw" (g (sov "a" [])) (sov "a" []);
  let r = refiner_of_build m in
  List.iter (fun (label, o) -> attempt ("compute_dependencies " ^ label) (fun () -> "[" ^ deps r o ^ "]"))
    [ "ML rule mlr", opn "test_refine_deps_ml" "mlr";
      "ML rewrite mlrw", opn "test_refine_deps_ml" "mlrw";
      "rewrite pw", opn "test_refine_deps_ml" "pw";
      "rule ra (through the join)", opn "test_refine_deps_a" "ra";
      "label A", opn "test_refine_deps_a" "A";
      "a name it does not have", opn "test_refine_deps_ml" "zz" ]
