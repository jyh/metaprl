(* Rewrite_debug's printers, the kinds test_rewrite_debug does not feed
   (2026-11-15 rank: print_stack_item, rstack_item_str, print_param,
   print_sparam and four print_prog arms, unreached by the unit tests, the
   theory build and the proof census; and Rewrite_util.rstack_downgrade).
   With the "rewrite" debug flag set, each rewrite is compiled
   (term_rewrite) and applied once (apply_rewrite); the trace it writes to
   stderr is printed, then the result.  The redexes carry shape, operator,
   quote, variable, object-id, list and level parameters, a second-order
   variable used twice, a free first-order variable used twice, binders,
   a context and a sequent.  Then three compiled redex stacks are printed
   (print_rewrite_redex): meta-parameters, a variable first seen inside an
   instance's argument, and that variable then used as an instance and
   then as a pattern, which takes rstack_downgrade's first arm.  The
   expected file is the output of the code as written (2026-11-15).
   Not reached, and why:
   - print_sparam's Shape, Operator and Var arms: a contractum operator
     is printed by print_sop only when is_sparam admits every parameter
     (Number, String, Token, Quote, ParamList), so those arms take no input.
   - rstack_item_str's SOVarInstance and FreeFOVarInstance arms:
     check_stack refuses a redex whose stack still holds either, so no
     compiled redex prints one; their other caller is an error message
     in Rewrite_compile_contractum.
   - The ContextRestrict stack item and RWAvoidBindings: ContextRestrict
     needs a rule argument (compile_redices with goal and args;
     test_rewrite_match_order declares the same hole), and RWAvoidBindings
     a sequent context instance (wrap_context_instances); neither is
     built here.  The Void and ITerm stack items are not produced by
     these cases; why was not measured.
   Found and not changed: the RWSOFreeVarsContext arm prints the label
   "RWSOContext"; rstack_downgrade's failure message names
   rstack_upgrade; and its FreeFOVarInstance arm turns the entry into a
   pattern, as rstack_upgrade's does. *)
open Term_sig
open Refiner.Refiner
open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan

let op s = Opname.make_opname [ s; "Rdk" ]
let v = Lm_symbol.add
let app o ps ts = mk_term (mk_op (op o) ps) (List.map (fun t -> mk_bterm [] t) ts)
let c0 o = app o [] []
let sov x args = mk_so_var_term (v x) [] args
let var x = mk_var_term (v x)
let lam x t = mk_term (mk_op (op "lam") []) [ mk_bterm [ v x ] t ]
let show t = Simple_print.SimplePrint.string_of_term t
let p = make_param
let opp name = { opparam_name = op name; opparam_params = []; opparam_arities = [ 0; 1 ] }
let shape = Shape (TermShape.shape_of_term (app "s" [] [ c0 "c" ]))

let capture_stderr f =
  let file = Filename.temp_file "trdk" ".err" in
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

let case ?(strict = Rewrite_sig.Relaxed) ?(ints = [||]) ?(arg_ints = [||]) ?(addrs = [||]) ?(arg_addrs = [||]) name redex contractum target =
  let trace, result = capture_stderr (fun () ->
      try
        let rw = Rewrite.term_rewrite strict { Rewrite_sig.spec_ints = ints; spec_addrs = addrs } [ redex ] [ contractum ] in
        let args = ({ Rewrite_sig.arg_ints; arg_addrs }, Lm_symbol.SymbolSet.empty) in
        String.concat " | " (List.map show (Rewrite.apply_rewrite rw args target []))
      with
      | RefineError.RefineError (s, _) -> "refused (" ^ s ^ ")"
      | Invalid_argument s -> "Invalid_argument (" ^ s ^ ")") in
  Printf.printf "== %s\n%s-> %s\n" name trace result

let () =
  Lm_debug.set_debug "rewrite" true;
  case "meta shape, operator and variable parameters"
    (app "h" [ p (MShape (v "sh")); p (MOperator (v "o")); p (Var (v "w")) ] [])
    (app "k" [ p (MShape (v "sh")); p (MOperator (v "o")); p (Var (v "w")) ] [ c0 "c" ])
    (app "h" [ p shape; p (Operator (opp "f")); p (Var (v "z")) ] []);
  let lits = [ p shape; p (Operator (opp "f")); p Quote ] in
  let num n = p (Number (Lm_num.num_of_int n)) in
  case "literal shape, operator and quote parameters, and object-id and list parameters beside a meta"
    (app "h" (p (MNumber (v "n")) :: lits) [])
    (app "k" (p (MNumber (v "n")) :: p (ObId [ num 1 ]) :: p (ParamList [ num 2; p (String "a") ]) :: lits) [])
    (app "h" (num 7 :: lits) []);
  case "a contractum whose parameters are all simple (number, string, token, quote, list)"
    (c0 "c")
    (app "k" [ num 3; p (String "s"); p (Token (op "t")); p Quote;
               p (ParamList [ num 2; p (String "a") ]) ] [ c0 "d" ])
    (c0 "c");
  case "a level meta-parameter with one variable"
    (app "h" [ p (MLevel (mk_level 0 [ mk_level_var (v "i") 0 ])) ] [])
    (app "k" [ p (MLevel (mk_level 0 [ mk_level_var (v "i") 0 ])) ] [])
    (app "h" [ p (MLevel (mk_level 0 [ mk_level_var (v "j") 0 ])) ] []);
  case "a second-order variable used twice"
    (app "f" [] [ sov "a" []; sov "a" [] ]) (sov "a" []) (app "f" [] [ c0 "c"; c0 "c" ]);
  case "a free first-order variable used twice"
    (app "f" [] [ var "x"; var "x" ]) (app "g" [] [ var "x" ]) (app "f" [] [ var "y"; var "y" ]);
  case "a binder the body ignores"
    (lam "x" (sov "b" [])) (app "g" [] [ sov "b" [] ]) (lam "z" (c0 "c"));
  case "a bound variable used in the body"
    (lam "x" (app "g" [] [ var "x" ])) (c0 "c") (lam "z" (app "g" [] [ var "z" ]));
  case "a binder in the contractum"
    (lam "x" (sov "b" [])) (lam "y" (sov "b" [])) (lam "z" (c0 "c"));
  let ctx t = app "f" [] [ mk_context_term (v "C") t [] [] ] in
  let at path = [| TermAddr.make_address (List.map (fun i -> Term_addr_sig.Subterm i) path) |] in
  case "a context" (ctx (app "g" [] [ sov "x" [] ])) (ctx (app "m" [] [ sov "x" [] ]))
    (app "f" [] [ app "h" [] [ app "g" [] [ c0 "c" ] ] ]) ~addrs:[| v "C" |] ~arg_addrs:(at [ 1 ]);
  case "a second-order variable with an argument, used twice"
    (app "pair" [] [ lam "x" (sov "b" [ var "x" ]); lam "y" (sov "b" [ var "y" ]) ]) (sov "b" [ c0 "c" ])
    (app "pair" [] [ lam "u" (app "g" [] [ var "u" ]); lam "w" (app "g" [] [ var "w" ]) ]);
  let seq hyps concl = mk_sequent_term { sequent_args = c0 "arg"; sequent_hyps = SeqHyp.of_list hyps; sequent_concl = concl } in
  let sovc x conts args = mk_so_var_term (v x) (List.map v conts) args in
  let side concl = seq [ Context (v "H", [], []); Hypothesis (v "x", sovc "A" [ "H" ] []); Context (v "J", [ v "H" ], [ var "x" ]) ]
                       (sovc concl [ "H"; "J" ] [ var "x" ]) in
  case "a sequent" ~strict:Rewrite_sig.Strict ~ints:[| v "H" |] ~arg_ints:[| 2 |]
    (side "C") (side "C")
    (seq [ Hypothesis (v "u", c0 "U"); Hypothesis (v "x", c0 "X"); Hypothesis (v "y", app "g" [] [ var "x" ]) ] (app "g" [] [ var "x" ]));
  Lm_debug.set_debug "rewrite" false;
  (* A compiled redex's stack, printed by print_rewrite_redex (rstack_item_str). *)
  let redex name terms =
    Printf.printf "== redex: %s\n" name;
    (try
       let rx = Rewrite.compile_redices Rewrite_sig.Relaxed Rewrite.empty_args_spec terms in
       let b = Buffer.create 256 in
       let out = Lm_printf.formatter_of_buffer b in
       Lm_printf.pp_set_margin out 100; Rewrite.print_rewrite_redex out rx; Lm_printf.pp_print_flush out ();
       print_string (Buffer.contents b)
     with
     | RefineError.RefineError (s, _) -> print_string ("refused (" ^ s ^ ")")
     | Invalid_argument s -> print_string ("Invalid_argument (" ^ s ^ ")"));
    print_newline () in
  redex "meta-parameters" [ app "h" [ p (MNumber (v "n")); p (MString (v "s")) ] [] ];
  redex "a variable first seen inside an instance's argument"
    [ app "f" [] [ sov "c" [ sov "b" [] ]; lam "y" (sov "c" [ var "y" ]) ] ];
  redex "that variable then used as an instance, then as a pattern (rstack_downgrade)"
    [ app "f" [] [ lam "x" (sov "c" [ sov "b" [ var "x" ] ]); lam "y" (sov "c" [ var "y" ]);
                   sov "b" [ c0 "d" ]; lam "z" (sov "b" [ var "z" ]) ] ]
