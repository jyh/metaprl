(* Rewrite_compile_redex (refiner/rewrite): the branches the proof census
   runs and no unit test did (2026-11-11 reach census, 46 lines): a
   second-order variable that occurs twice (an instance of the first), a
   context passed as an address argument, and argument redices under
   Strict compilation, whose second-order variables restrict which goal
   contexts they may see (map_restricts).  Each case compiles with
   Rewrite.compile_redices and applies with apply_redex, and prints the
   items it binds or the RefineError it raises; the expected file is the
   output of the code as written (2026-11-11), never typed.  Pinned as
   found: an argument whose variable is restricted to H is not refused
   when it mentions a variable bound in J; the argument is matched first,
   so the restriction is recorded before J is, and J's clashing
   hypotheses are renamed (the identity rewrite shows the renamed goal). *)
open Term_sig
open Term_addr_sig
open Refiner.Refiner
open TermType
open Term
open TermMan
open RefineError
open Rewrite_sig

let op s = Opname.make_opname [ s; "Rca" ]
let v = Lm_symbol.add
let app o ts = mk_term (mk_op (op o) []) (List.map (fun t -> mk_bterm [] t) ts)
let c0 o = app o []
let so name conts args = mk_so_var_term (v name) (List.map v conts) args
let var x = mk_var_term (v x)
let lam x t = mk_term (mk_op (op "lam") []) [ mk_bterm [ v x ] t ]
let sp = Simple_print.SimplePrint.string_of_term

let seq hyps concl =
  mk_sequent_term { sequent_args = c0 "arg"; sequent_hyps = SeqHyp.of_list hyps; sequent_concl = concl }

let show_item = function
  | RewriteTerm t -> sp t
  | RewriteString _ | RewriteToken _ | RewriteNum _ -> "param"
  | RewriteLevel _ -> "level" | RewriteShape _ -> "shape" | RewriteOperator _ -> "operator"
  | RewriteUnsupported -> "-"

let case ?(ints = [||]) ?(addrs = [||]) ?(arg_ints = [||]) ?(arg_addrs = [||]) ?(args = []) ?(targs = [])
    name strict redex target =
  let r =
    try
      let rx = Rewrite.compile_redices strict { spec_ints = ints; spec_addrs = addrs } (redex :: args) in
      let items = Rewrite.apply_redex rx { arg_ints; arg_addrs } target targs in
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
  Printf.printf "%-50s %s\n" name r

let () =
  print_endline "== a second-order variable twice";
  let fa = app "f" [ so "a" [] []; so "a" [] [] ] in
  case "f{'a; 'a} on f{c; c}" Relaxed fa (app "f" [ c0 "c"; c0 "c" ]);
  case "f{'a; 'a} on f{c; d}" Relaxed fa (app "f" [ c0 "c"; c0 "d" ]);
  case "f{'a; g{'a}} on f{c; g{c}}" Relaxed (app "f" [ so "a" [] []; app "g" [ so "a" [] [] ] ]) (app "f" [ c0 "c"; app "g" [ c0 "c" ] ]);
  let twice = app "f" [ lam "x" (so "b" [] [ var "x" ]); lam "y" (so "b" [] [ var "y" ]) ] in
  case "f{lam x. 'b['x]; lam y. 'b['y]} on equal bodies" Relaxed twice
    (app "f" [ lam "x" (app "g" [ var "x" ]); lam "z" (app "g" [ var "z" ]) ]);
  case "f{lam x. 'b['x]; lam y. 'b['y]} on different" Relaxed twice
    (app "f" [ lam "x" (app "g" [ var "x" ]); lam "z" (app "h" [ var "z" ]) ]);
  print_endline "== a context passed as an address argument";
  (* f{ C[g{'x}] }: the hole of context C, at the address given, holds g{'x} *)
  let redex = app "f" [ mk_context_term (v "C") (app "g" [ so "x" [] [] ]) [] [] ] in
  let target = app "f" [ app "h" [ app "k" [ c0 "d"; app "g" [ c0 "c" ] ] ] ] in
  let at path = [| TermAddr.make_address (List.map (fun i -> Subterm i) path) |] in
  case "f{C[g{'x}]}, hole at h.1.2" Relaxed redex target ~addrs:[| v "C" |] ~arg_addrs:(at [ 1; 2 ]);
  case "f{C[g{'x}]}, hole at h.1.1 (d, no g)" Relaxed redex target ~addrs:[| v "C" |] ~arg_addrs:(at [ 1; 1 ]);
  case "f{C[g{'x}]}, hole at h.1.3 (no subterm)" Relaxed redex target ~addrs:[| v "C" |] ~arg_addrs:(at [ 1; 3 ]);
  case "f{C[g{'x}]}, hole at the top (empty address)" Relaxed redex (app "f" [ app "g" [ c0 "c" ] ]) ~addrs:[| v "C" |] ~arg_addrs:(at []);
  case "f{C[g{'x}]}, no address argument" Relaxed redex target;
  print_endline "== argument redices, Strict";
  (* the goal <H>; x: 'A; <J['x]> >- 'C['x] with H as the rule argument,
     and one argument 'T that sees H only, or H and J *)
  let goal =
    seq [ Context (v "H", [], []); Hypothesis (v "x", so "A" [ "H" ] []); Context (v "J", [ v "H" ], [ var "x" ]) ]
      (so "C" [ "H"; "J" ] [ var "x" ])
  in
  let target = seq [ Hypothesis (v "y", c0 "T"); Hypothesis (v "x", c0 "T"); Hypothesis (v "z", c0 "T") ] (app "f" [ var "x" ]) in
  (* and the identity rewrite of the goal under the same argument, whose
     result shows the goal after matching: a restriction recorded by the
     argument before J is matched renames J's clashing hypotheses *)
  let go name strict conts t =
    case name strict goal target ~ints:[| v "H" |] ~arg_ints:[| 2 |] ~args:[ so "T" conts [] ] ~targs:[ t ];
    let r =
      try
        let rw = Rewrite.term_rewrite strict { spec_ints = [| v "H" |]; spec_addrs = [||] } [ goal; so "T" conts [] ] [ goal ] in
        match Rewrite.apply_rewrite rw ({ arg_ints = [| 2 |]; arg_addrs = [||] }, Lm_symbol.SymbolSet.empty) target [ t ] with
        | [ r ] -> sp r
        | l -> Printf.sprintf "%d results" (List.length l)
      with
      | RefineError (s, _) -> "REFUSED: " ^ s
      | Invalid_argument s -> "INVALID_ARGUMENT: " ^ s
    in
    Printf.printf "%-50s %s\n" "   identity rewrite gives" r
  in
  go "'T sees H: argument g{y}" Strict [ "H" ] (app "g" [ var "y" ]);
  go "'T sees H: argument g{z} (z bound in J)" Strict [ "H" ] (app "g" [ var "z" ]);
  go "'T sees H and J: argument g{z}" Strict [ "H"; "J" ] (app "g" [ var "z" ]);
  go "'T sees H: argument g{z}, Relaxed" Relaxed [ "H" ] (app "g" [ var "z" ]);
  go "'T sees nothing: argument g{y}" Strict [] (app "g" [ var "y" ]);
  go "'T sees nothing: argument c" Strict [] (c0 "c")
