(* Rewrite_debug's printers (refiner/rewrite/rewrite_debug.ml), which only
   the "rewrite" debug flag reaches: no unit test, theory build or proof
   replay did (2026-11-14 rank: 74 of its 166 points).  With the flag set,
   each rewrite below is compiled (term_rewrite) and applied once
   (apply_rewrite) in term_std, and the trace it writes to stderr is
   captured and printed, followed by the result.  The redexes carry every
   parameter kind (numbers, strings, tokens, levels, variables and the
   meta-parameters), a second-order variable with an argument and a
   binder.  Added later (bisect at a45cd0437 left print_stack_item and
   print_param 9 points each): shape, operator and quote parameters and
   their meta forms, and a sequent with contexts (H the rule's int
   argument), whose trace prints Shape, Operator and SeqContext stack
   items.  Not reached here: the Void, ITerm, Context and ContextRestrict
   stack items (the "RWSoVar: Void" lines are match_redex's own message,
   not a printed stack item) and the ObId and ParamList parameters.  The expected file
   is the output of the code as written (2026-11-14, 2026-11-15). *)
open Term_sig
open Refiner.Refiner
open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan

let op s = Opname.make_opname [ s ]
let v = Lm_symbol.add
let app o ps ts = mk_term (mk_op (op o) ps) (List.map (fun t -> mk_bterm [] t) ts)
let c0 o = app o [] []
let sov x args = mk_so_var_term (v x) [] args
let lam x t = mk_term (mk_op (op "lam") []) [ mk_bterm [ v x ] t ]
let show t = Simple_print.SimplePrint.string_of_term t

let capture_stderr f =
  let file = Filename.temp_file "trd" ".err" in
  flush stderr; Format.pp_print_flush Format.err_formatter ();
  let saved = Unix.dup Unix.stderr in
  let fd = Unix.openfile file [ Unix.O_WRONLY; Unix.O_TRUNC ] 0o600 in
  Unix.dup2 fd Unix.stderr; Unix.close fd;
  let restore () = flush stderr; Format.pp_print_flush Format.err_formatter (); Unix.dup2 saved Unix.stderr; Unix.close saved in
  let r = (try f () with e -> restore (); raise e) in
  restore ();
  let ic = open_in_bin file in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic; Sys.remove file; s, r

let case ?(spec = Rewrite.empty_args_spec) ?(args = Rewrite.empty_args) name redex contractum target =
  let trace, result = capture_stderr (fun () ->
      try
        let rw = Rewrite.term_rewrite Rewrite_sig.Strict spec [ redex ] [ contractum ] in
        String.concat " | " (List.map show (Rewrite.apply_rewrite rw args target []))
      with RefineError.RefineError (s, _) -> "refused (" ^ s ^ ")") in
  Printf.printf "== %s\n%s-> %s\n" name trace result

let () =
  Lm_debug.set_debug "rewrite" true;
  let lvl = make_param (MLevel (mk_level 1 [ mk_level_var (v "i") 0 ])) in
  case "every parameter kind"
    (app "p" [ make_param (MNumber (v "n")); make_param (MString (v "s")); make_param (MToken (v "t")); lvl;
               make_param (Number (Lm_num.num_of_int 3)); make_param (String "x"); make_param (Token (op "tok")) ] [ sov "a" [] ])
    (app "q" [ make_param (MNumber (v "n")); make_param (MString (v "s")) ] [ sov "a" [] ])
    (app "p" [ make_param (Number (Lm_num.num_of_int 7)); make_param (String "str"); make_param (Token (op "k"));
               make_param (MLevel (mk_level 1 [ mk_level_var (v "j") 0 ]));
               make_param (Number (Lm_num.num_of_int 3)); make_param (String "x"); make_param (Token (op "tok")) ] [ c0 "c" ]);
  case "a binder and a second-order variable"
    (app "h" [] [ lam "x" (sov "b" [ mk_var_term (v "x") ]) ]) (sov "b" [ c0 "c" ])
    (app "h" [] [ lam "y" (app "f" [] [ mk_var_term (v "y") ]) ]);
  case "no match" (app "h" [] [ sov "a" [] ]) (sov "a" []) (c0 "c");
  let sh = TermShape.shape_of_term (c0 "s") and opp = TermShape.opparam_of_term (c0 "o") in
  case "shape, operator and quote parameters"
    (app "r" [ make_param (MShape (v "sh")); make_param (MOperator (v "op")); make_param (Shape sh);
               make_param (Operator opp); make_param Quote ] [])
    (app "q" [ make_param (MShape (v "sh")); make_param (MOperator (v "op")) ] [])
    (app "r" [ make_param (Shape (TermShape.shape_of_term (c0 "t"))); make_param (Operator (TermShape.opparam_of_term (c0 "u")));
               make_param (Shape sh); make_param (Operator opp); make_param Quote ] []);
  let seq hyps concl =
    mk_sequent_term { sequent_args = c0 "sa"; sequent_hyps = SeqHyp.of_list hyps; sequent_concl = concl } in
  (* H is the rule's int argument: x is hypothesis 2 *)
  case "a sequent with contexts" ~spec:{ Rewrite_sig.spec_ints = [| v "H" |]; spec_addrs = [||] }
    ~args:({ Rewrite_sig.arg_ints = [| 2 |]; arg_addrs = [||] }, Lm_symbol.SymbolSet.empty)
    (seq [ Context (v "H", [], []); Hypothesis (v "x", mk_so_var_term (v "A") [ v "H" ] []);
           Context (v "J", [ v "H" ], [ mk_var_term (v "x") ]) ]
       (mk_so_var_term (v "B") [ v "H"; v "J" ] [ mk_var_term (v "x") ]))
    (seq [ Context (v "H", [], []); Context (v "J", [ v "H" ], [ c0 "d" ]) ] (mk_so_var_term (v "B") [ v "H"; v "J" ] [ c0 "d" ]))
    (seq [ Hypothesis (v "y", c0 "e"); Hypothesis (v "x", c0 "d"); Hypothesis (v "w", c0 "g") ] (c0 "b"));
  Lm_debug.set_debug "rewrite" false;
  case "flag off" (app "h" [] [ sov "a" [] ]) (sov "a" []) (app "h" [] [ c0 "c" ])
