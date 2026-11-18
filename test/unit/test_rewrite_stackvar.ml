(* Rewrite_build_contractum.build_bname, which no rewrite test reached on
   its StackString and fallback arms (2026-11-15 re-rank, deadsplit680):
   a contractum binder named by a meta parameter of the redex takes its
   name from the stack.  Each rewrite h[@x:k] --> lam{x. g{'x}} is
   compiled Relaxed (and the first Strict) and applied once; it prints
   the result or the error.  The expected file is the output of the code
   as written (2026-11-15).
   Pinned as found: only a string parameter names the binder
   (lam{'abc. g{'abc}}); a number or a token falls to the fallback arm and
   the binder keeps its own name (lam{'n. g{'n}}).  The bound occurrence
   is built as a bound variable, not through RWStackVar, so
   build_contractum_term's RWStackVar arms for a string or a number entry,
   and its refusal of an unusual entry, are still not reached; nor is a
   contractum context with arguments (it raises "Not implemented yet"),
   which needs a redex context with arguments to compile. *)
open Term_sig
open Refiner.Refiner
open TermType
open Term
open TermMan
open RefineError
open Rewrite_sig

let op s = Opname.make_opname [ s; "Rsv" ]
let v = Lm_symbol.add
let app o ts = mk_term (mk_op (op o) []) (List.map (fun t -> mk_bterm [] t) ts)
let p1 o prm = mk_term (mk_op (op o) [ make_param prm ]) []
let c0 o = app o []
let so name args = mk_so_var_term (v name) [] args
let var x = mk_var_term (v x)
let sp = Simple_print.SimplePrint.string_of_term

let rw ?(strict = Relaxed) ?(addrs = [||]) ?(arg_addrs = [||]) name redex contractum target =
  let r =
    try
      let rw = Rewrite.term_rewrite strict { spec_ints = [||]; spec_addrs = addrs } [ redex ] [ contractum ] in
      match Rewrite.apply_rewrite rw ({ arg_ints = [||]; arg_addrs }, Lm_symbol.SymbolSet.empty) target [] with
      | [ r ] -> sp r
      | l -> Printf.sprintf "%d results" (List.length l)
    with
    | RefineError (s, e) ->
        "REFUSED: " ^ s
        ^ (match e with
           | StringVarError (m, x) -> " (" ^ m ^ ": " ^ Lm_symbol.to_string x ^ ")"
           | StringError m -> " (" ^ m ^ ")"
           | RewriteFreeSOVar x -> " (RewriteFreeSOVar " ^ Lm_symbol.to_string x ^ ")"
           | RewriteSOVarArity x -> " (RewriteSOVarArity " ^ Lm_symbol.to_string x ^ ")"
           | RewriteBadMatch _ -> " (RewriteBadMatch)"
           | _ -> " (another error)")
    | Invalid_argument s -> "INVALID_ARGUMENT: " ^ s
  in
  Printf.printf "%-44s %s\n%!" name r

let () =
  let lam x t = mk_term (mk_op (op "lam") []) [ mk_bterm [ v x ] t ] in
  print_endline "== a contractum binder named by a meta parameter, and its bound occurrence";
  rw "h[@s:s] --> lam{s. g{'s}} on h[\"abc\":s]" (p1 "h" (MString (v "s"))) (lam "s" (app "g" [ var "s" ])) (p1 "h" (String "abc"));
  rw "h[@n:n] --> lam{n. g{'n}} on h[7:n]" (p1 "h" (MNumber (v "n"))) (lam "n" (app "g" [ var "n" ])) (p1 "h" (Number (Lm_num.num_of_int 7)));
  rw "h[@t:t] --> lam{t. g{'t}} on h[k:t]" (p1 "h" (MToken (v "t"))) (lam "t" (app "g" [ var "t" ])) (p1 "h" (Token (op "k")));
  rw "the first, Strict" ~strict:Strict (p1 "h" (MString (v "s"))) (lam "s" (app "g" [ var "s" ])) (p1 "h" (String "abc"))
