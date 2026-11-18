(* Rewrite_util.rstack_upgrade's free first-order arm (refiner/rewrite),
   which no unit test reached (2026-11-15 profile: the FreeFOVarInstance
   arm unvisited, the second-order arms reached).  A free first-order
   variable x met first inside the argument of a second-order instance
   ('a['x], where x is not bound, so it is compiled as an instance), and
   then on its own (x, a pattern), has its stack entry upgraded from an
   instance to a pattern.  Each redex is compiled with Rewrite.compile_redex
   and applied with apply_redex; the output is the items bound or the first
   string of the RefineError, as in test_rewrite_match_order.  The expected
   file is the output of the code as written (2026-11-15), never typed.
   Measured: met first as an instance, x is upgraded and the redex matches
   as it does with the pattern met first (the instance is checked once x
   is known); with x only in the argument it stays an instance and
   check_stack refuses the redex.  An entry pushed after x's ('b in
   quad{'a['x]; 'b; x; ...}) is kept by the upgrade.
   Not reached, and why: rstack_upgrade's [] arm ("internal error"); both
   callers (rewrite_compile_redex.ml) upgrade only a variable the stack
   already holds (rstack_freefo_mem, rstack_so_mem). *)
open Term_sig
open Refiner.Refiner
open TermType
open Term
open TermMan
open RefineError
open Rewrite_sig

let op s = Opname.make_opname [ s; "Rfu" ]
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

(* 'a also needs its pattern, lam{w.'a['w]}: a redex whose second-order
   variable is only ever an instance is refused (check_stack). *)
let () =
  let fy = app "f" [ var "y" ] and fz = app "f" [ var "z" ] and k = c0 "k" in
  let pat = lam "w" (so "a" [ var "w" ]) and fw = lam "w" (app "f" [ var "w" ]) in
  List.iter (fun (title, strict) ->
    print_endline ("== " ^ title);
    print_endline "-- the instance first: tri{'a['x]; x; lam{w.'a['w]}} (upgraded)";
    let r = app "tri" [ so "a" [ var "x" ]; var "x"; pat ] in
    case "  on tri{f{y}; y; lam{w.f{w}}}" strict r (app "tri" [ fy; var "y"; fw ]);
    case "  on tri{f{z}; y; lam{w.f{w}}}" strict r (app "tri" [ fz; var "y"; fw ]);
    case "  on tri{k; y; lam{w.f{w}}}" strict r (app "tri" [ k; var "y"; fw ]);
    case "  on tri{f{y}; k; lam{w.f{w}}}" strict r (app "tri" [ fy; k; fw ]);
    print_endline "-- an entry after x's: quad{'a['x]; 'b; x; lam{w.'a['w]}} (upgraded, 'b kept)";
    let r = app "quad" [ so "a" [ var "x" ]; so "b" []; var "x"; pat ] in
    case "  on quad{f{y}; k; y; lam{w.f{w}}}" strict r (app "quad" [ fy; k; var "y"; fw ]);
    case "  on quad{f{y}; k; z; lam{w.f{w}}}" strict r (app "quad" [ fy; k; var "z"; fw ]);
    print_endline "-- the pattern first: tri{x; 'a['x]; lam{w.'a['w]}}";
    let r = app "tri" [ var "x"; so "a" [ var "x" ]; pat ] in
    case "  on tri{y; f{y}; lam{w.f{w}}}" strict r (app "tri" [ var "y"; fy; fw ]);
    case "  on tri{y; f{z}; lam{w.f{w}}}" strict r (app "tri" [ var "y"; fz; fw ]);
    case "  on tri{y; k; lam{w.f{w}}}" strict r (app "tri" [ var "y"; k; fw ]);
    print_endline "-- only in the argument: pair{'a['x]; lam{w.'a['w]}}";
    let r = app "pair" [ so "a" [ var "x" ]; pat ] in
    case "  on pair{f{y}; lam{w.f{w}}}" strict r (app "pair" [ fy; fw ]);
    case "  on pair{k; lam{w.f{w}}}" strict r (app "pair" [ k; fw ]))
    [ "Relaxed", Relaxed; "Strict", Strict ]
