(* Rewrite_match_redex (refiner/rewrite): the branches the proof census
   runs and no unit test did (2026-11-11 reach census, 88 lines):
   parameter matching against string, token and meta parameters, and
   sequent contexts under Strict compilation, where a context left out of
   a second-order variable's context list may not bind that variable's
   free variables (H, not the last context, is passed as a rule argument
   with its number of hypotheses, the way a rule names 'H).  Each case compiles a redex with Rewrite.compile_redex
   and applies it to a target with apply_redex, and prints the items it
   binds or the first string of the RefineError it raises; the expected
   file is the output of the code as written (2026-11-11), never typed.
   Not reached here, and declared: the branch of match_redex_sequent_hyps
   that renames a context's clashing hypotheses (a restriction recorded
   before the context is matched, StackContextRestrict); every restriction
   in these cases is met after its context, and is refused by
   check_cont_bvars_hyps instead. *)
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

let () =
  print_endline "== parameters";
  case "s[\"a\"] on s[\"a\"]" Relaxed (p1 "s" (String "a")) (p1 "s" (String "a"));
  case "s[\"a\"] on s[\"b\"]" Relaxed (p1 "s" (String "a")) (p1 "s" (String "b"));
  case "t[a:t] on t[a:t]" Relaxed (p1 "t" (Token (op "a"))) (p1 "t" (Token (op "a")));
  case "t[a:t] on t[b:t]" Relaxed (p1 "t" (Token (op "a"))) (p1 "t" (Token (op "b")));
  case "n[3:n] on n[3:n]" Relaxed (p1 "n" (Number (Lm_num.num_of_int 3))) (p1 "n" (Number (Lm_num.num_of_int 3)));
  case "n[3:n] on n[4:n]" Relaxed (p1 "n" (Number (Lm_num.num_of_int 3))) (p1 "n" (Number (Lm_num.num_of_int 4)));
  print_endline "== meta parameters in the target";
  case "n[@i:n] on n[@k:n] (a meta number)" Relaxed (p1 "n" (MNumber (v "i"))) (p1 "n" (MNumber (v "k")));
  case "s[@i:s] on s[@k:s] (a meta string)" Relaxed (p1 "s" (MString (v "i"))) (p1 "s" (MString (v "k")));
  case "t[@i:t] on t[@k:t] (a meta token)" Relaxed (p1 "t" (MToken (v "i"))) (p1 "t" (MToken (v "k")));
  case "n[@i:n] on n[5:n]" Relaxed (p1 "n" (MNumber (v "i"))) (p1 "n" (Number (Lm_num.num_of_int 5)));
  case "n[3:n] on n[@k:n] (constant against a meta)" Relaxed (p1 "n" (Number (Lm_num.num_of_int 3))) (p1 "n" (MNumber (v "k")));
  case "pair{n[@i]; n[@i]} on pair{n[@k]; n[@k]}" Relaxed
    (app "pair" [ p1 "n" (MNumber (v "i")); p1 "n" (MNumber (v "i")) ])
    (app "pair" [ p1 "n" (MNumber (v "k")); p1 "n" (MNumber (v "k")) ]);
  case "pair{n[@i]; n[@i]} on pair{n[@k]; n[@m]}" Relaxed
    (app "pair" [ p1 "n" (MNumber (v "i")); p1 "n" (MNumber (v "i")) ])
    (app "pair" [ p1 "n" (MNumber (v "k")); p1 "n" (MNumber (v "m")) ]);
  case "pair{n[@i]; n[@i]} on pair{n[@k]; n[5]}" Relaxed
    (app "pair" [ p1 "n" (MNumber (v "i")); p1 "n" (MNumber (v "i")) ])
    (app "pair" [ p1 "n" (MNumber (v "k")); p1 "n" (Number (Lm_num.num_of_int 5)) ]);
  print_endline "== sequent contexts, Strict";
  (* <H>; x: 'A; <J['x]> >- 'C['x], with 'C allowed to see H only, or H and J *)
  let redex cconts =
    seq [ Context (v "H", [], []); Hypothesis (v "x", so "A" [ "H" ] []); Context (v "J", [ v "H" ], [ mk_var_term (v "x") ]) ]
      (so "C" cconts [ mk_var_term (v "x") ])
  in
  let target concl =
    seq [ Hypothesis (v "y", c0 "T"); Hypothesis (v "x", c0 "T"); Hypothesis (v "z", c0 "T") ] concl
  in
  let fz = app "f" [ mk_var_term (v "z") ] and fx = app "f" [ mk_var_term (v "x") ] and fy = app "f" [ mk_var_term (v "y") ] in
  case ~h:1 "C sees H, J: concl f{z}" Strict (redex [ "H"; "J" ]) (target fz);
  case ~h:1 "C sees H only: concl f{x}" Strict (redex [ "H" ]) (target fx);
  case ~h:1 "C sees H only: concl f{y}" Strict (redex [ "H" ]) (target fy);
  case ~h:1 "C sees H only: concl f{z} (z bound in J)" Strict (redex [ "H" ]) (target fz);
  case ~h:1 "the same, Relaxed" Relaxed (redex [ "H" ]) (target fz);
  case ~h:1 "C sees H only: J empty, concl f{x}" Strict (redex [ "H" ])
    (seq [ Hypothesis (v "y", c0 "T"); Hypothesis (v "x", c0 "T") ] fx);
  (* 'A sees no context: a hypothesis type mentioning an H-bound variable *)
  let redex2 =
    seq [ Context (v "H", [], []); Hypothesis (v "x", so "A" [] []); Context (v "J", [ v "H" ], [ mk_var_term (v "x") ]) ]
      (so "C" [ "H"; "J" ] [ mk_var_term (v "x") ])
  in
  case ~h:1 "A sees nothing: x: g{y} after y: T" Strict redex2
    (seq [ Hypothesis (v "y", c0 "T"); Hypothesis (v "x", app "g" [ mk_var_term (v "y") ]) ] fx);
  case ~h:1 "A sees nothing: x: T after y: T" Strict redex2
    (seq [ Hypothesis (v "y", c0 "T"); Hypothesis (v "x", c0 "T") ] fx);
  (* J sees nothing: a J hypothesis mentioning an H-bound variable *)
  let redex3 =
    seq [ Context (v "H", [], []); Hypothesis (v "x", so "A" [ "H" ] []); Context (v "J", [], [ mk_var_term (v "x") ]) ]
      (so "C" [ "H"; "J" ] [ mk_var_term (v "x") ])
  in
  case ~h:1 "J sees nothing: z: g{y}" Strict redex3
    (seq [ Hypothesis (v "y", c0 "T"); Hypothesis (v "x", c0 "T"); Hypothesis (v "z", app "g" [ mk_var_term (v "y") ]) ] fx);
  case ~h:1 "J sees nothing: z: g{x}" Strict redex3
    (seq [ Hypothesis (v "y", c0 "T"); Hypothesis (v "x", c0 "T"); Hypothesis (v "z", app "g" [ mk_var_term (v "x") ]) ] fx)
