(* Term_meta_gen's parser-side conversions (refiner/term_gen), which the
   filter runs on every term it reads and no unit test did (2026-11-11 reach
   census, 77 lines): term_of_parsed_term over sequents (hypotheses with an
   empty or a repeated name are renamed; a sequent whose meta-type allows
   no bindings refuses a named hypothesis), the context markers ("!!" for
   the default contexts, "#" for "not the enclosing ones"), an encoded free
   variable (a second-order variable with the "!" context and no
   arguments), context_subst_of_terms, a labelled meta term, and the
   memo that rewrite_of_parsed_rewrite shares between redex and contractum.
   Each case prints the converted term (or the error).  The expected file
   is the output of the code as written (2026-11-11), never typed.
   Pinned as found, and a defect: rewrite_of_parsed_rewrite is
   "f redex, f contractum", and OCaml evaluates a tuple right to left, so
   the CONTRACTUM is parsed first and the shared memo fixes the default
   contexts of 'C from the contractum (none) instead of the redex (J):
   'C<||> on both sides, where mrewrite_of_parsed_mrewrite, which orders
   its calls, gives 'C<|J|>.  The fix is a separate change. *)
open Term_sig
open Refiner.Refiner
open TermType
open Term
open TermMan
open RefineError

let op s = Opname.make_opname [ s; "Tmp" ]
let v = Lm_symbol.add
let app o ts = mk_term (mk_op (op o) []) (List.map (fun t -> mk_bterm [] t) ts)
let c0 o = app o []
let var x = mk_var_term (v x)
let so name conts args = mk_so_var_term (v name) conts args
let empty = Lm_symbol.make "" 0
let dflt = [ Term_meta_sig.default_contexts ]
let bang = [ Lm_symbol.make "!" 0 ]
let sp = Simple_print.SimplePrint.string_of_term
let flat s = String.concat " " (List.filter (( <> ) "") (String.split_on_char '\n' s))
let seq hyps concl =
  mk_sequent_term { sequent_args = c0 "arg"; sequent_hyps = SeqHyp.of_list hyps; sequent_concl = concl }

let run name f =
  let r =
    try f () with
    | RefineError (s, StringVarError (m, x)) -> Printf.sprintf "REFUSED: %s (%s: %s)" s m (Lm_symbol.to_string x)
    | RefineError (s, _) -> "REFUSED: " ^ s
    | Invalid_argument s -> "INVALID_ARGUMENT: " ^ s
    | Failure s -> "FAILURE: " ^ s
  in
  Printf.printf "%-44s %s\n" name r

let parse ?(binds = true) name t = run name (fun () -> flat (sp (TermMeta.term_of_parsed_term (fun _ -> binds) t)))

let () =
  print_endline "== term_of_parsed_term";
  parse "x: A; y: B >- f{x; y}" (seq [ Hypothesis (v "x", c0 "A"); Hypothesis (v "y", c0 "B") ] (app "f" [ var "x"; var "y" ]));
  parse "two unnamed hypotheses" (seq [ Hypothesis (empty, c0 "A"); Hypothesis (empty, c0 "B") ] (c0 "C"));
  parse "x: A; x: B >- f{x} (x repeated)" (seq [ Hypothesis (v "x", c0 "A"); Hypothesis (v "x", c0 "B") ] (app "f" [ var "x" ]));
  parse "x: A >- C, bindings not allowed" ~binds:false (seq [ Hypothesis (v "x", c0 "A") ] (c0 "C"));
  parse "unnamed: A >- C, bindings not allowed" ~binds:false (seq [ Hypothesis (empty, c0 "A") ] (c0 "C"));
  parse "<J>; x: A >- 'C<|!!|> (default contexts)" (seq [ Context (v "J", dflt, []); Hypothesis (v "x", c0 "A") ] (so "C" dflt []));
  parse "<J>; <K> >- 'C<|#;K|> (# drops J... )"
    (seq [ Context (v "J", dflt, []); Context (v "K", dflt, []) ] (so "C" [ Term_meta_sig.hash_sym; v "K" ] []));
  parse "<J> >- 'C<|#|> (a so-var), no bindings" ~binds:false (seq [ Context (v "J", dflt, []) ] (so "C" [ Term_meta_sig.hash_sym ] []));
  parse "<J>; <K<|#|>> >- C (a context), no bindings" ~binds:false
    (seq [ Context (v "J", dflt, []); Context (v "K", [ Term_meta_sig.hash_sym ], []) ] (c0 "C"));
  parse "<J>; <K<|#|>> >- C (a context)" (seq [ Context (v "J", dflt, []); Context (v "K", [ Term_meta_sig.hash_sym ], []) ] (c0 "C"));
  parse "an encoded free variable z" (app "f" [ so "z" bang [] ]);
  parse "<J>; x: A >- 'z<|!|> (encoded, x free in it?)" (seq [ Context (v "J", dflt, []); Hypothesis (v "x", c0 "A") ] (so "x" bang []));
  parse "a context term D<|!!|>[g{x}] in a sequent"
    (seq [ Context (v "J", dflt, []); Hypothesis (v "x", c0 "A") ] (mk_context_term (v "D") (app "g" [ var "x" ]) dflt []));
  print_endline "== context_subst_of_terms";
  let terms = [ seq [ Context (v "J", [ v "H" ], [ c0 "a" ]) ] (so "C" [ v "J" ] [ c0 "b"; c0 "c" ]); so "D" [] [] ] in
  let lookup name i =
    run (Printf.sprintf "lookup %s/%d" name i) (fun () ->
        match TermMeta.context_subst_of_terms terms (v name) i with
        | Some l -> "Some [" ^ String.concat "; " (List.map Lm_symbol.to_string l) ^ "]"
        | None -> "None")
  in
  lookup "J" 1; lookup "C" 2; lookup "D" 0; lookup "E" 0; lookup "C" 3;
  run "two arities for one variable" (fun () ->
      ignore (TermMeta.context_subst_of_terms [ app "f" [ so "C" [] [ c0 "a" ]; so "C" [] [] ] ]); "built");
  print_endline "== meta terms and rewrites";
  run "mterms_of_parsed_mterms on a labelled term" (fun () ->
      let mt, _, _ = TermMeta.mterms_of_parsed_mterms (fun _ -> true)
          (MetaLabeled ("lbl", MetaTheorem (seq [ Hypothesis (empty, c0 "A") ] (c0 "C")))) [] in
      match mt with MetaLabeled (l, MetaTheorem t) -> l ^ ": " ^ flat (sp t) | _ -> "another shape");
  run "mterms: <J> >- 'C<|!!|> (the memoising parser)" (fun () ->
      let mt, _, _ = TermMeta.mterms_of_parsed_mterms (fun _ -> true) (MetaTheorem (seq [ Context (v "J", dflt, []) ] (so "C" dflt []))) [] in
      match mt with MetaTheorem t -> flat (sp t) | _ -> "another shape");
  parse "term_of_parsed_term: <J> >- 'C<|!!|>" (seq [ Context (v "J", dflt, []) ] (so "C" dflt []));
  run "mrewrite: the same redex and contractum" (fun () ->
      let rs, c = TermMeta.mrewrite_of_parsed_mrewrite (fun _ -> true)
          [ seq [ Context (v "J", dflt, []) ] (so "C" dflt []) ] (app "k" [ so "C" dflt [] ]) in
      String.concat "; " (List.map (fun r -> flat (sp r)) rs) ^ "  ==>  " ^ flat (sp c));
  run "rewrite: 'C<|!!|> in the redex, then the contractum" (fun () ->
      let r, c = TermMeta.rewrite_of_parsed_rewrite (fun _ -> true)
          (seq [ Context (v "J", dflt, []) ] (so "C" dflt [])) (app "k" [ so "C" dflt [] ]) in
      flat (sp r) ^ "  ==>  " ^ flat (sp c))
