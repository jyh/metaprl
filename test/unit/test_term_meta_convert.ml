(* Term_meta_gen (refiner/term_gen): the conversions the proof census runs
   and no unit test did (2026-11-12 census, 12 lines).  Each case prints
   the converted term, the lookup, or the error; the expected file is the
   output of the code as written (2026-11-12), never typed.
   - unzip_mfunction keeps a hypothesis's labels in order (two labels on
     one), and refuses a label on an iff;
   - term_of_parsed_term: a bound variable written as a second-order
     variable with no arguments becomes the variable; a second-order
     variable's arguments are converted; a hypothesis is rebuilt only when
     its type changes (one kept, the next converted); a free variable
     becomes a second-order variable with the enclosing contexts;
   - term_of_parsed_term_with_vars leaves a free variable as it is;
   - display_term_of_term writes the enclosing contexts as the default
     marker and others as they are;
   - context_subst_of_terms reads a hypothesis's type and a context term
     inside a sequent. *)
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

let bnd x t = mk_term (mk_op (op "lam") []) [ mk_bterm [ v x ] t ]
let show t = flat (sp t)
let labels l = "[" ^ String.concat "; " l ^ "]"

let () =
  print_endline "== unzip_mfunction, labels";
  let a = c0 "A" and b = c0 "B" and g = c0 "G" in
  run "u: (l, m: A) -> B -> G" (fun () ->
      let hs, goal = TermMeta.unzip_mfunction
          (MetaFunction (var "u", MetaLabeled ("l", MetaLabeled ("m", MetaTheorem a)), MetaImplies (MetaTheorem b, MetaTheorem g))) in
      String.concat " | "
        (List.map (fun (ls, vo, t) -> labels ls ^ " " ^ (match vo with Some v -> show v | None -> "-") ^ " " ^ show t) hs)
      ^ " => " ^ show goal);
  run "a label on an iff" (fun () ->
      ignore (TermMeta.unzip_mfunction (MetaImplies (MetaLabeled ("l", MetaIff (MetaTheorem a, MetaTheorem b)), MetaTheorem g))); "built");
  print_endline "== term_of_parsed_term, second-order variables";
  parse "lam{x. 'x<|H|>} (bound, no arguments)" (bnd "x" (so "x" [ v "H" ] []));
  parse "f{'a<|H|>[c]}" (app "f" [ so "a" [ v "H" ] [ c0 "c" ] ]);
  parse "f{'a<|!!|>[c]}" (app "f" [ so "a" dflt [ c0 "c" ] ]);
  parse "f{'a<|H|>['b<|!!|>]}" (app "f" [ so "a" [ v "H" ] [ so "b" dflt [] ] ]);
  parse "<J>; x: 'A<|!!|> >- C (a hypothesis converted)"
    (seq [ Context (v "J", dflt, []); Hypothesis (v "x", so "A" dflt []) ] (c0 "C"));
  parse "<J>; x: A; y: 'B<|!!|> >- C (x kept, y converted)"
    (seq [ Context (v "J", dflt, []); Hypothesis (v "x", c0 "A"); Hypothesis (v "y", so "B" dflt []) ] (c0 "C"));
  parse "f{z} (a free variable)" (app "f" [ var "z" ]);
  print_endline "== term_of_parsed_term_with_vars";
  let wv name t = run name (fun () -> show (TermMeta.term_of_parsed_term_with_vars (fun _ -> true) t)) in
  wv "f{'a<|!!|>}" (app "f" [ so "a" dflt [] ]);
  wv "f{z} (a free variable)" (app "f" [ var "z" ]);
  wv "<J> >- 'C<|!!|>" (seq [ Context (v "J", dflt, []) ] (so "C" dflt []));
  print_endline "== display_term_of_term";
  let dp name t = run name (fun () -> show (TermMeta.display_term_of_term t)) in
  dp "<J> >- 'C<|J|> (the enclosing contexts)" (seq [ Context (v "J", [], []) ] (so "C" [ v "J" ] []));
  dp "<J> >- 'C<|K|> (others)" (seq [ Context (v "J", [], []) ] (so "C" [ v "K" ] []));
  dp "<J> >- 'C<||>" (seq [ Context (v "J", [], []) ] (so "C" [] []));
  print_endline "== context_subst_of_terms, hypotheses and context terms";
  let terms = [ seq [ Hypothesis (v "x", so "A" [ v "H" ] [ c0 "a" ]) ] (mk_context_term (v "D") (so "E" [ v "K" ] []) [ v "H" ] [ c0 "b" ]) ] in
  let lookup name i =
    run (Printf.sprintf "lookup %s/%d" name i) (fun () ->
        match TermMeta.context_subst_of_terms terms (v name) i with
        | Some l -> "Some [" ^ String.concat "; " (List.map Lm_symbol.to_string l) ^ "]"
        | None -> "None")
  in
  lookup "A" 1; lookup "D" 1; lookup "E" 0; lookup "D" 2
