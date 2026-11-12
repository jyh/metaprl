(* Rewrite (refiner/rewrite), the items a matched redex binds for its
   parameter variables, and Rewrite_util's stack for a second-order
   variable that is first met where patterns are off: the branches the
   proof census runs and no unit test did (2026-11-11 reach census:
   rewrite.ml 5 lines, rewrite_util.ml 4).  Each case compiles a redex
   with Rewrite.compile_redices, prints the compiled program
   (Rewrite.print_rewrite_redex) where the stack is the point, and applies
   it with apply_redex to a target, printing the items bound or the
   RefineError raised.  The parameter kinds: a shape variable, an
   operator variable, a level variable and a variable parameter, each matched against a literal
   and against a variable of its kind.  The stack cases: f{lam x. 'b['x]; 'b['a]; 'a}, whose 'a is first met
   inside the argument list of the instance 'b['a] (so it is only a
   "maybe pattern") and then as a pattern, once, twice, and at another
   arity.  The expected
   file is the output of the code as written (2026-11-11). *)
open Term_sig
open Refiner.Refiner
open TermType
open Term
open TermMan
open RefineError
open Rewrite_sig

let op s = Opname.make_opname [ s; "Ri" ]
let v = Lm_symbol.add
let app o ts = mk_term (mk_op (op o) []) (List.map (fun t -> mk_bterm [] t) ts)
let c0 o = app o []
let so name args = mk_so_var_term (v name) [] args
let pt o params = mk_term (mk_op (op o) params) []
let sp = Simple_print.SimplePrint.string_of_term
let show_rx rx = let b = Buffer.create 256 in let out = Lm_printf.formatter_of_buffer b in
  Lm_printf.pp_set_margin out 100; Rewrite.print_rewrite_redex out rx; Lm_printf.pp_print_flush out (); Buffer.contents b
let show_item = function
  | RewriteTerm t -> "term " ^ sp t
  | RewriteString (RewriteParam s) -> "string " ^ s
  | RewriteString (RewriteMetaParam x) -> "string-var " ^ Lm_symbol.to_string x
  | RewriteToken (RewriteParam o) -> "token " ^ Opname.string_of_opname o
  | RewriteToken (RewriteMetaParam x) -> "token-var " ^ Lm_symbol.to_string x
  | RewriteNum (RewriteParam n) -> "num " ^ Lm_num.string_of_num n
  | RewriteNum (RewriteMetaParam x) -> "num-var " ^ Lm_symbol.to_string x
  | RewriteShape (RewriteParam s) -> "shape " ^ TermShape.string_of_shape s
  | RewriteShape (RewriteMetaParam x) -> "shape-var " ^ Lm_symbol.to_string x
  | RewriteOperator (RewriteParam o) -> "operator " ^ Opname.string_of_opname o.opparam_name
  | RewriteOperator (RewriteMetaParam x) -> "operator-var " ^ Lm_symbol.to_string x
  | RewriteLevel l -> "level " ^ sp (pt "lv" [ make_param (MLevel l) ])
  | RewriteUnsupported -> "unsupported"

let case ?(print = false) name redex target =
  Printf.printf "== %s\n%!" name;
  let r =
    try
      let rx = Rewrite.compile_redices Strict { spec_ints = [||]; spec_addrs = [||] } [ redex ] in
      (if print then print_string (show_rx rx));
      let items = Rewrite.apply_redex rx { arg_ints = [||]; arg_addrs = [||] } target [] in
      "MATCH [" ^ String.concat "; " (List.map show_item items) ^ "]"
    with RefineError (s, _) -> "REFUSED: " ^ s
  in
  print_endline r

let shape_of t = TermShape.shape_of_term t
let opparam name = { opparam_name = Opname.make_opname [ name; "Ri" ]; opparam_params = []; opparam_arities = [] }

let () =
  let pat_shape = pt "s" [ make_param (MShape (v "S")) ] in
  case "s[shape S] on s[shape of g{_}]" pat_shape (pt "s" [ make_param (Shape (shape_of (app "g" [ c0 "c" ]))) ]);
  case "s[shape S] on s[shape var T]" pat_shape (pt "s" [ make_param (MShape (v "T")) ]);
  let pat_op = pt "o" [ make_param (MOperator (v "O")) ] in
  case "o[operator O] on o[operator h]" pat_op (pt "o" [ make_param (Operator (opparam "h")) ]);
  case "o[operator O] on o[operator var P]" pat_op (pt "o" [ make_param (MOperator (v "P")) ]);
  let pat_lvl = pt "l" [ make_param (MLevel (mk_var_level_exp (v "L"))) ] in
  case "l[level L] on l[level 2]" pat_lvl (pt "l" [ make_param (MLevel (mk_const_level_exp 2)) ]);
  case "l[level L] on l[level i]" pat_lvl (pt "l" [ make_param (MLevel (mk_var_level_exp (v "i"))) ]);
  case "l[level L] on l[level i+1 | 3]" pat_lvl (pt "l" [ make_param (MLevel (mk_level 3 [ mk_level_var (v "i") 1 ])) ]);
  let pat_var = pt "w" [ make_param (Var (v "X")) ] in
  case "w[var X] on w[var y]" pat_var (pt "w" [ make_param (Var (v "y")) ]);
  case "s[shape S] on o[operator h] (no match)" pat_shape (pt "o" [ make_param (Operator (opparam "h")) ]);
  let lam x t = mk_term (mk_op (op "lam") []) [ mk_bterm [ v x ] t ] in
  let x = mk_var_term (v "x") in
  let fb = app "f" [ lam "x" (so "b" [ x ]); so "b" [ so "a" [] ]; so "a" [] ] in
  case ~print:true "f{lam x. 'b['x]; 'b['a]; 'a}" fb (app "f" [ lam "x" (app "g" [ x ]); app "g" [ c0 "c" ]; c0 "c" ]);
  case "  same, on f{lam x. g{x}; g{d}; c}" fb (app "f" [ lam "x" (app "g" [ x ]); app "g" [ c0 "d" ]; c0 "c" ]);
  case ~print:true "f{lam x. 'b['x]; 'b['a]; 'a; 'a}" (app "f" [ lam "x" (so "b" [ x ]); so "b" [ so "a" [] ]; so "a" []; so "a" [] ])
    (app "f" [ lam "x" (app "g" [ x ]); app "g" [ c0 "c" ]; c0 "c"; c0 "c" ]);
  case "f{lam x. 'b['x]; 'b['a]; lam y. 'a['y]} (arities)" (app "f" [ lam "x" (so "b" [ x ]); so "b" [ so "a" [] ]; lam "y" (so "a" [ mk_var_term (v "y") ]) ])
    (app "f" [ lam "x" (app "g" [ x ]); app "g" [ c0 "c" ]; lam "y" (c0 "c") ])
