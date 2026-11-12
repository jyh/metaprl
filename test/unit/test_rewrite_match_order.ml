(* Rewrite_match_redex (refiner/rewrite): branches the proof census runs
   and no unit test did (2026-11-12 census, 21 lines), each compiled with
   Rewrite.compile_redex or compile_redices and applied with apply_redex;
   the output is the items bound or the first string of the RefineError.
   The expected file is the output of the code as written (2026-11-12),
   never typed.
   - a free first-order variable used twice must match one variable;
   - a second-order variable met as an instance ('a[k]) before or after its
     pattern (x.'a['x]), and as two instances before it: every instance is
     checked against the pattern once it is known;
   - bound-variable and parameter counts that differ;
   - a free variable passed as a rule argument and restricted from <H>:
     the restriction is recorded before <H> is matched, so a hypothesis of
     <H> that binds the argument's variable is renamed (in the conclusion
     too), and a context of that name is refused.
     Two such arguments record the restriction twice (the union).
   Not reached here, and declared: a non-sequent context with a restriction
   recorded before it (RWSOContext under StackContextRestrict). *)
open Lm_symbol
open Term_sig
open Refiner.Refiner
open TermType
open Term
open TermMan
open RefineError
open Rewrite_sig

let op s = Opname.make_opname [ s; "Rmp" ]
let v = Lm_symbol.add
let p1 o prm = mk_term (mk_op (op o) [ make_param prm ]) []
let app o ts = mk_term (mk_op (op o) []) (List.map (fun t -> mk_bterm [] t) ts)
let c0 o = app o []
let so name conts args = mk_so_var_term (v name) (List.map v conts) args
let sp = Simple_print.SimplePrint.string_of_term

let seq hyps concl =
  mk_sequent_term
    { sequent_args = c0 "arg"; sequent_hyps = SeqHyp.of_list hyps; sequent_concl = concl }

let show_item = function
  | RewriteTerm t -> "term " ^ sp t
  | RewriteString (RewriteParam s) -> "string " ^ s
  | RewriteString (RewriteMetaParam m) -> "meta-string " ^ Lm_symbol.to_string m
  | RewriteToken (RewriteParam o) -> "token " ^ Opname.string_of_opname o
  | RewriteToken (RewriteMetaParam m) -> "meta-token " ^ Lm_symbol.to_string m
  | RewriteNum (RewriteParam n) -> "num " ^ Lm_num.string_of_num n
  | RewriteNum (RewriteMetaParam m) -> "meta-num " ^ Lm_symbol.to_string m
  | RewriteLevel _ -> "level"
  | RewriteShape _ -> "shape"
  | RewriteOperator _ -> "operator"
  | RewriteUnsupported -> "unsupported"

(* ?h: H is passed as the rule argument with that many hypotheses *)
let case ?h name strict redex target =
  let spec, args =
    match h with
    | None -> Rewrite.empty_args_spec, Rewrite.empty_rw_args
    | Some n -> { spec_ints = [| v "H" |]; spec_addrs = [||] }, { Rewrite.empty_rw_args with arg_ints = [| n + 1 |] }
  in
  let r =
    try
      let rx = Rewrite.compile_redex strict spec redex in
      let items = Rewrite.apply_redex rx args target [] in
      "MATCH [" ^ String.concat "; " (List.map show_item items) ^ "]"
    with
    | RefineError (s, e) ->
        "REFUSED: " ^ s
        ^ (match e with
           | StringVarError (m, x) -> " (" ^ m ^ ": " ^ Lm_symbol.to_string x ^ ")"
           | StringError m -> " (" ^ m ^ ")"
           | RewriteMissingContextArg x -> " (missing context argument " ^ Lm_symbol.to_string x ^ ")"
           | _ -> "")
    | Invalid_argument s -> "INVALID_ARGUMENT: " ^ s
  in
  Printf.printf "%-52s %s\n" name r

let var s = mk_var_term (v s)
let lam x t = mk_term (mk_op (op "lam") []) [ mk_bterm [ v x ] t ]
let bnd xs o t = mk_term (mk_op (op o) []) [ mk_bterm (List.map v xs) t ]
let p2 o a b = mk_term (mk_op (op o) [ make_param a; make_param b ]) []

let () =
  print_endline "== free first-order variables (RWMatchFreeFOVar)";
  let r = app "pair" [ var "x"; var "x" ] in
  case "pair{x; x} on pair{y; y}" Relaxed r (app "pair" [ var "y"; var "y" ]);
  case "pair{x; x} on pair{y; z}" Relaxed r (app "pair" [ var "y"; var "z" ]);
  case "pair{x; x} on pair{y; k}" Relaxed r (app "pair" [ var "y"; c0 "k" ]);
  print_endline "== second-order variable instance before / after its pattern";
  let k = c0 "k" and j = c0 "j" in
  let ap = so "a" [] [ var "x" ] in
  (* 'a[k] then lam{x.'a['x]} *)
  let r1 = app "pair" [ so "a" [] [ k ]; lam "x" ap ] in
  case "pair{'a[k]; lam{x.'a['x]}} on pair{f{k}; lam{x.f{x}}}" Relaxed r1
    (app "pair" [ app "f" [ k ]; lam "x" (app "f" [ var "x" ]) ]);
  case "pair{'a[k]; lam{x.'a['x]}} on pair{f{j}; lam{x.f{x}}}" Relaxed r1
    (app "pair" [ app "f" [ j ]; lam "x" (app "f" [ var "x" ]) ]);
  (* lam{x.'a['x]} then 'a[k] *)
  let r2 = app "pair" [ lam "x" ap; so "a" [] [ k ] ] in
  case "pair{lam{x.'a['x]}; 'a[k]} on pair{lam{x.f{x}}; f{k}}" Relaxed r2
    (app "pair" [ lam "x" (app "f" [ var "x" ]); app "f" [ k ] ]);
  case "pair{lam{x.'a['x]}; 'a[k]} on pair{lam{x.f{x}}; f{j}}" Relaxed r2
    (app "pair" [ lam "x" (app "f" [ var "x" ]); app "f" [ j ] ]);
  (* two instances, then the pattern *)
  let r3 = app "tri" [ so "a" [] [ k ]; so "a" [] [ j ]; lam "x" ap ] in
  case "tri{'a[k]; 'a[j]; lam{x.'a['x]}} on tri{f{k}; f{j}; lam{x.f{x}}}" Relaxed r3
    (app "tri" [ app "f" [ k ]; app "f" [ j ]; lam "x" (app "f" [ var "x" ]) ]);
  case "tri{'a[k]; 'a[j]; lam{x.'a['x]}} on tri{f{k}; f{k}; lam{x.f{x}}}" Relaxed r3
    (app "tri" [ app "f" [ k ]; app "f" [ k ]; lam "x" (app "f" [ var "x" ]) ]);
  print_endline "== bound-variable counts";
  case "f{'a} on f{x.x}" Relaxed (app "f" [ so "a" [] [] ]) (lam "x" (var "x") |> fun t -> mk_term (mk_op (op "f") []) [ mk_bterm [ v "x" ] (var "x") ]);
  case "lam{x.'a['x]} on lam2{x,y.x}" Relaxed (bnd [ "x" ] "g" ap) (bnd [ "x"; "y" ] "g" (var "x"));
  print_endline "== parameter counts";
  case "p[a;b] on p[a]" Relaxed (p2 "p" (String "a") (String "b")) (p1 "p" (String "a"));
  print_endline "== context hypotheses in the target";
  let redex =
    seq [ Context (v "H", [], []); Hypothesis (v "x", so "A" [ "H" ] []); Context (v "J", [ v "H" ], [ var "x" ]) ]
      (so "C" [ "H"; "J" ] [ var "x" ])
  in
  let tgt hyps = seq hyps (app "f" [ var "x" ]) in
  case ~h:1 "H = <K>: <K>; x: T" Strict redex (tgt [ Context (v "K", [], []); Hypothesis (v "x", c0 "T") ]);
  case ~h:1 "J = <L>: y: T; x: T; <L>" Strict redex (tgt [ Hypothesis (v "y", c0 "T"); Hypothesis (v "x", c0 "T"); Context (v "L", [], []) ]);
  case ~h:1 "J = <x>: y: T; x: T; <x> (context named x)" Strict redex (tgt [ Hypothesis (v "y", c0 "T"); Hypothesis (v "x", c0 "T"); Context (v "x", [], []) ]);
  case ~h:0 "H empty, J = <L>: x: T; <L>" Relaxed redex (tgt [ Hypothesis (v "x", c0 "T"); Context (v "L", [], []) ])

(* A rule argument: the redex is goal :: args, compiled args first, so a
   restriction an argument records on a goal context is on the stack before
   that context is matched (StackContextRestrict). *)
let case_arg name strict goal args tgoal targs =
  let r =
    try
      let rx = Rewrite.compile_redices strict Rewrite.empty_args_spec (goal :: args) in
      let items = Rewrite.apply_redex rx Rewrite.empty_rw_args tgoal targs in
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
  Printf.printf "%-52s %s\n" name r

let () =
  print_endline "== a free variable as a rule argument, restricted from <H>";
  let goal = seq [ Context (v "H", [], []) ] (so "C" [ "H" ] []) in
  let fy = app "f" [ var "y" ] in
  case_arg "arg y; y: T >- f{y} (H's y renamed)" Strict goal [ var "x" ]
    (seq [ Hypothesis (v "y", c0 "T") ] fy) [ var "y" ];
  case_arg "arg y; <K>; y: T >- f{y}" Strict goal [ var "x" ]
    (seq [ Context (v "K", [], []); Hypothesis (v "y", c0 "T") ] fy) [ var "y" ];
  case_arg "arg y; z: T >- f{y} (no clash)" Strict goal [ var "x" ]
    (seq [ Hypothesis (v "z", c0 "T") ] fy) [ var "y" ];
  case_arg "arg y; <y> >- f{y} (a context named y)" Strict goal [ var "x" ]
    (seq [ Context (v "y", [], []) ] fy) [ var "y" ];
  case_arg "the same, Relaxed" Relaxed goal [ var "x" ]
    (seq [ Context (v "y", [], []) ] fy) [ var "y" ];
  case_arg "args y, z; y: T; z: T >- g{y; z} (both renamed)" Strict goal [ var "x"; var "w" ]
    (seq [ Hypothesis (v "y", c0 "T"); Hypothesis (v "z", c0 "T") ] (app "g" [ var "y"; var "z" ])) [ var "y"; var "z" ];
  print_endline "== a free variable in the goal, restricted from <H> (already matched)";
  let goal2 = seq [ Context (v "H", [], []) ] (app "f" [ var "x" ]) in
  case_arg "<H> >- f{x} on y: T >- f{w}" Strict goal2 [] (seq [ Hypothesis (v "y", c0 "T") ] (app "f" [ var "w" ])) [];
  case_arg "<H> >- f{x} on y: T >- f{y}" Strict goal2 [] (seq [ Hypothesis (v "y", c0 "T") ] fy) [];
  case_arg "<H> >- f{x} on <y> >- f{y}" Strict goal2 [] (seq [ Context (v "y", [], []) ] fy) []
