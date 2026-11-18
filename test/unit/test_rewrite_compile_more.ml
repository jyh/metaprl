(* Rewrite_compile_redex.compile_so_redex_term's refusals and repeated
   instances (refiner/rewrite), which no unit test reached (2026-11-15
   profile), and Term_op_ds.mk_var_param_term's refusal of the special
   opnames.  The redex harness is test_rewrite_freefo_upgrade's: each redex
   is compiled with Rewrite.compile_redex (Relaxed) and applied with
   apply_redex; the output is the items bound or the first string of the
   RefineError.  Cases: a name used as a free first-order variable and as a
   second-order variable; a free first-order variable met twice inside
   instances' arguments; a second-order instance inside another instance's
   argument; a non-sequent context met twice (refused: "not supported
   yet").  The expected file is the output of the code as written, never
   typed. *)
open Term_sig
open Refiner.Refiner
open TermType
open Term
open TermMan
open RefineError
open Rewrite_sig

let op s = Opname.make_opname [ s; "Rcr" ]
let v = Lm_symbol.add
let app o ts = mk_term (mk_op (op o) []) (List.map (fun t -> mk_bterm [] t) ts)
let c0 o = app o []
let so name args = mk_so_var_term (v name) [] args
let var s = mk_var_term (v s)
let sp = Simple_print.SimplePrint.string_of_term

let show_item = function
  | RewriteTerm t -> "term " ^ sp t
  | RewriteString (RewriteParam s) -> "string " ^ s
  | RewriteString (RewriteMetaParam m) -> "meta-string " ^ Lm_symbol.to_string m
  | RewriteToken _ -> "token" | RewriteNum _ -> "num" | RewriteLevel _ -> "level"
  | RewriteShape _ -> "shape" | RewriteOperator _ -> "operator"
  | RewriteUnsupported -> "unsupported"

let case name strict redex target =
  let r =
    try
      let rx = Rewrite.compile_redex strict Rewrite.empty_args_spec redex in
      let items = Rewrite.apply_redex rx Rewrite.empty_rw_args target [] in
      "MATCH [" ^ String.concat "; " (List.map show_item items) ^ "]"
    with
    | RefineError (s, e) ->
        "REFUSED: " ^ s
        ^ (match e with
           | StringVarError (m, x) -> " (" ^ m ^ ": " ^ Lm_symbol.to_string x ^ ")"
           | StringError m -> " (" ^ m ^ ")"
           | _ -> "")
    | Invalid_argument s -> "INVALID_ARGUMENT: " ^ s
  in
  Printf.printf "%-44s %s\n" name r

let lam x t = mk_term (mk_op (op "lam") []) [ mk_bterm [ v x ] t ]

let ctx name t = mk_context_term (v name) t [] []

let () =
  let fy = app "f" [ var "y" ] and k = c0 "k" in
  let pat = lam "w" (so "a" [ var "w" ]) and fw = lam "w" (app "f" [ var "w" ]) in
  print_endline "== a free variable x and a second-order variable 'x[]";
  case "  pair{x; 'x} on pair{y; k}" Relaxed (app "pair" [ var "x"; so "x" [] ]) (app "pair" [ var "y"; k ]);
  case "  pair{'x; x} on pair{k; y}" Relaxed (app "pair" [ so "x" []; var "x" ]) (app "pair" [ k; var "y" ]);
  print_endline "== x twice inside instances: quad{'a['x]; 'a['x]; x; lam{w.'a['w]}}";
  let r = app "quad" [ so "a" [ var "x" ]; so "a" [ var "x" ]; var "x"; pat ] in
  case "  on quad{f{y}; f{y}; y; lam{w.f{w}}}" Relaxed r (app "quad" [ fy; fy; var "y"; fw ]);
  print_endline "== an instance inside an instance: tri{'a['b]; 'b; lam{w.'a['w]}}";
  let r = app "tri" [ so "a" [ so "b" [] ]; so "b" []; pat ] in
  case "  on tri{f{k}; k; lam{w.f{w}}}" Relaxed r (app "tri" [ app "f" [ k ]; k; fw ]);
  print_endline "== a non-sequent context met twice: pair{<H> c; <H> c}";
  case "  on pair{<J> c; <J> c}" Relaxed (app "pair" [ ctx "H" (c0 "c"); ctx "H" (c0 "c") ]) (app "pair" [ ctx "J" (c0 "c"); ctx "J" (c0 "c") ]);
  print_endline "== Term_op_ds.mk_var_param_term (term_ds)";
  List.iter (fun (name, o) ->
      Printf.printf "  %-42s %s\n" name
        (match Refiner_ds.Refiner.TermOp.mk_var_param_term o (v "x") with
         | _ -> "built"
         | exception Invalid_argument s -> "INVALID_ARGUMENT: " ^ s))
    [ "an ordinary opname", op "g"; "Opname.var_opname", Opname.var_opname; "Opname.context_opname", Opname.context_opname ]
