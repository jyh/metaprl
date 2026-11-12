(* Rewrite_compile_contractum (refiner/rewrite): the branches the proof
   census runs and no unit test does after test_rewrite_contractum and
   test_rewrite_compile_args (2026-11-11 reach census, 13 lines): in a
   Relaxed contractum, a meta parameter that names a variable the redex
   bound with another kind (a number reused as a string or a variable);
   meta and literal operator parameters, and a literal token beside a
   meta parameter (an operator whose parameters are all literal is copied
   as is, so a lone token never reaches that branch); a contractum second-order variable that names one of the
   redex's binders; and a context term in a Strict contractum.  Each case
   is a term_rewrite applied to a target, and prints the result or the
   error.  The expected file is the output of the code as written
   (2026-11-11), never typed.  Pinned as found: in Relaxed mode a number
   variable reused as a string gives "7", but reused as a variable or an
   operator the rewrite compiles and then raises Invalid_argument ("stack
   entry is not valid") when applied; Strict refuses it when compiled.
   And a redex binder named in the contractum outside any binder escapes
   as a free variable (f{'z}). *)
open Term_sig
open Term_addr_sig
open Refiner.Refiner
open TermType
open Term
open TermMan
open RefineError
open Rewrite_sig

let op s = Opname.make_opname [ s; "Rcc" ]
let v = Lm_symbol.add
let app o ts = mk_term (mk_op (op o) []) (List.map (fun t -> mk_bterm [] t) ts)
let p1 o prm = mk_term (mk_op (op o) [ make_param prm ]) []
let c0 o = app o []
let so name args = mk_so_var_term (v name) [] args
let var x = mk_var_term (v x)
let lam x t = mk_term (mk_op (op "lam") []) [ mk_bterm [ v x ] t ]
let opp name = { opparam_name = op name; opparam_params = []; opparam_arities = [ 0; 1 ] }
let sp = Simple_print.SimplePrint.string_of_term

let rw ?(strict = Relaxed) ?(addrs = [||]) ?(arg_addrs = [||]) name redex contractum target =
  let r =
    try
      let rw = Rewrite.term_rewrite strict { spec_ints = [||]; spec_addrs = addrs } [ redex ] [ contractum ] in
      match Rewrite.apply_rewrite rw ({ arg_ints = [||]; arg_addrs }, Lm_symbol.SymbolSet.empty) target [] with
      | [ r ] -> sp r
      | l -> Printf.sprintf "%d results" (List.length l)
    with
    | RefineError (s, _) -> "REFUSED: " ^ s
    | Invalid_argument s -> "INVALID_ARGUMENT: " ^ s
    | Failure s -> "FAILURE: " ^ s
  in
  Printf.printf "%-48s %s\n" name r

let () =
  print_endline "== a meta parameter of another kind (Relaxed)";
  let num7 = p1 "h" (Number (Lm_num.num_of_int 7)) in
  rw "h[@n:n] --> k[@n:s] on h[7:n]" (p1 "h" (MNumber (v "n"))) (p1 "k" (MString (v "n"))) num7;
  rw "h[@n:n] --> k[@n:v] on h[7:n]" (p1 "h" (MNumber (v "n"))) (p1 "k" (Var (v "n"))) num7;
  rw "h[@n:n] --> k[@n:op] on h[7:n]" (p1 "h" (MNumber (v "n"))) (p1 "k" (MOperator (v "n"))) num7;
  rw "the first, Strict" ~strict:Strict (p1 "h" (MNumber (v "n"))) (p1 "k" (MString (v "n"))) num7;
  print_endline "== operator and token parameters";
  rw "h[@o:op] --> k[@o:op] on h[f:op]" (p1 "h" (MOperator (v "o"))) (p1 "k" (MOperator (v "o"))) (p1 "h" (Operator (opp "f")));
  rw "c --> k[g:op] (a literal operator)" (c0 "c") (p1 "k" (Operator (opp "g"))) (c0 "c");
  rw "c --> k[a:t] (a literal token, copied as is)" (c0 "c") (p1 "k" (Token (op "a"))) (c0 "c");
  rw "h[@n:n] --> k[a:t; @n:n] (a token beside a meta)" (p1 "h" (MNumber (v "n")))
    (mk_term (mk_op (op "k") [ make_param (Token (op "a")); make_param (MNumber (v "n")) ]) []) num7;
  print_endline "== a contractum variable naming a redex binder";
  rw "lam x. 'b['x] --> f{'x} on lam z. g{z}" (lam "x" (so "b" [ var "x" ])) (app "f" [ so "x" [] ]) (lam "z" (app "g" [ var "z" ]));
  rw "lam x. 'b['x] --> lam x. f{'x}" (lam "x" (so "b" [ var "x" ])) (lam "x" (app "f" [ so "x" [] ])) (lam "z" (app "g" [ var "z" ]));
  print_endline "== a context in a Strict contractum";
  let ctx t = app "f" [ mk_context_term (v "C") t [] [] ] in
  let at path = [| TermAddr.make_address (List.map (fun i -> Subterm i) path) |] in
  let target = app "f" [ app "h" [ app "k" [ c0 "d"; app "g" [ c0 "c" ] ] ] ] in
  rw "f{C[g{'x}]} --> f{C[m{'x}]}, Strict" ~strict:Strict (ctx (app "g" [ so "x" [] ])) (ctx (app "m" [ so "x" [] ]))
    target ~addrs:[| v "C" |] ~arg_addrs:(at [ 1; 2 ]);
  rw "the same, Relaxed" (ctx (app "g" [ so "x" [] ])) (ctx (app "m" [ so "x" [] ]))
    target ~addrs:[| v "C" |] ~arg_addrs:(at [ 1; 2 ])
