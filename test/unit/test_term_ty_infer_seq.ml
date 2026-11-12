(* Term_ty_infer on SEQUENTS, contexts and meta-parameters, the half of the
   filter's type checker that only the proof census reached (2026-11-11
   reach census: 108 lines of term_ty_infer.ml reached by the census and by
   no unit test, test_term_ty_infer included).  The environment is
   test_term_ty_infer's, built by hand the way Filter_cache_fun builds its
   root, plus three sequent arguments declared with ty_sequent types:
     sarg   hypotheses  x: Term . Term,   conclusion Term,  a Judgment
     parg   hypotheses  x: Term . Term,   conclusion Prop,  a Judgment
     carg   hypotheses in two cases (x: Term . Term | x: Prop . Prop),
            conclusion Term, a Judgment
     varg   hypotheses  x: Prop . Term (the variable's type is not the
            hypothesis's), conclusion Prop, a Judgment
   and ptag[t:t] : Term, whose token must name a Term (tag's names a Prop).
   A sequent's type is read from its argument; each hypothesis is checked
   against the hypothesis type and binds its variable at the bound type;
   a context <H> is a second-order context variable whose type is
   inferred.  Each case prints the inferred type, or the first string of
   the RefineError raised; every outcome is the code's own (measured
   2026-11-11).
   Pinned as found, not changed: a token meta-variable's type is fixed by
   its FIRST use, so eq{tag[@t]; ptag[@t]} (a Prop name, then a Term
   name) is accepted and eq{ptag[@t]; tag[@t]} is refused, though the two
   state the same constraint.
   Not covered: ty_exists declarations, the debug_infer prints. *)
open Lm_symbol
open Opname
open Term_sig
open Term_ty_sig
open Refiner.Refiner
open TermType
open Term
open TermShape
open RefineError

let perv = mk_opname "Perv" nil_opname
let pop s = mk_opname s perv
let uop s = make_opname [ s; "Test" ]
let const o = mk_term (mk_op o []) []

let term_c = Term_ty_infer.term_type
let type_c = Term_ty_infer.type_type
let prop_o = pop "Prop"
let judgment_o = pop "Judgment"
let dform_o = pop "Dform"
let nonterminal_o = pop "Nonterminal"
let ignore_o = pop "Ignore"
let prop_c = const prop_o
let judgment_c = const judgment_o
let dform_c = const dform_o
let nonterminal_c = const nonterminal_o

let typeclasses =
  List.fold_left (fun tbl (o, supers) -> OpnameTable.add tbl o (OpnameSet.of_list (o :: supers)))
    OpnameTable.empty
    [ Term_ty_infer.term_opname, []; Term_ty_infer.type_opname, []; judgment_o, []; dform_o, [];
      nonterminal_o, []; prop_o, [ Term_ty_infer.term_opname ] ]

(* every typeclass term is itself a type, in its own class *)
let typeenv =
  OpnameTable.fold (fun env o _ -> ShapeTable.add env (shape_of_term (const o)) o) ShapeTable.empty typeclasses

let decl o params bterms ty t =
  { ty_term = t; ty_opname = o; ty_params = params; ty_bterms = bterms; ty_type = ty }

let bt bvars ty = { ty_bvars = bvars; ty_bterm = ty }

let zero = const (uop "zero")
let tt = const (uop "tt")
let nt = const (uop "nt")
let succ t = mk_term (mk_op (uop "succ") []) [ mk_bterm [] t ]
let lam v t = mk_term (mk_op (uop "lam") []) [ mk_bterm [ Lm_symbol.add v ] t ]
let num n = mk_term (mk_op (uop "num") [ make_param (Number (Lm_num.num_of_int n)) ]) []
let sname s = mk_term (mk_op (uop "name") [ make_param (String s) ]) []
let tname s = mk_term (mk_op (uop "name") [ make_param (Token (make_opname [ s ])) ]) []
let tag s = mk_term (mk_op (uop "tag") [ make_param (Token (uop s)) ]) []
let bad v t = mk_term (mk_op (uop "bad") []) [ mk_bterm [ Lm_symbol.add v ] t ]
let odd n = mk_term (mk_op (uop "odd") [ make_param (Number (Lm_num.num_of_int n)) ]) []
let eq a b = mk_term (mk_op (uop "eq") []) [ mk_bterm [] a; mk_bterm [] b ]
let df t = mk_term (mk_op (uop "df") []) [ mk_bterm [] t ]
let var v = mk_var_term (Lm_symbol.add v)
let sarg = const (uop "sarg")
let parg = const (uop "parg")
let carg = const (uop "carg")
let varg = const (uop "varg")
let ptag s = mk_term (mk_op (uop "ptag") [ make_param (Token (uop s)) ]) []

let termenv =
  let classes =
    OpnameTable.fold (fun l o _ -> decl o [] [] type_c (const o) :: l) [] typeclasses
  in
  let x = mk_var_term (Lm_symbol.add "x") in
  List.fold_left (fun env d -> ShapeTable.add env (shape_of_term d.ty_term) d) ShapeTable.empty
    (classes
     @ [ decl (uop "zero") [] [] term_c zero;
         decl (uop "tt") [] [] prop_c tt;
         decl (uop "nt") [] [] nonterminal_c nt;
         decl (uop "succ") [] [ bt [] term_c ] term_c (succ zero);
         decl (uop "lam") [] [ bt [ term_c ] term_c ] term_c (lam "x" x);
         decl (uop "num") [ TyNumber ] [] term_c (num 0);
         decl (uop "name") [ TyString ] [] term_c (sname "a");
         decl (uop "tag") [ TyToken prop_c ] [] term_c (tag "tt");
         decl (uop "bad") [] [ bt [] term_c ] term_c (bad "x" x);
         decl (uop "odd") [ TyString ] [] term_c (odd 0);
         decl (uop "eq") [] [ bt [] term_c; bt [] term_c ] judgment_c (eq zero zero);
         decl (uop "df") [] [ bt [] term_c ] dform_c (df zero);
         (* sequent arguments: sarg's hypotheses bind a Term and are Terms, its
            conclusion is a Term and the sequent a Judgment; parg's
            conclusion is a Prop; carg's hypotheses are two cases *)
         decl (uop "sarg") [] [] (Term_ty_infer.mk_ty_sequent_term (Term_ty_infer.mk_ty_hyp_term term_c term_c) term_c judgment_c) sarg;
         decl (uop "parg") [] [] (Term_ty_infer.mk_ty_sequent_term (Term_ty_infer.mk_ty_hyp_term term_c term_c) prop_c judgment_c) parg;
         decl (uop "varg") [] [] (Term_ty_infer.mk_ty_sequent_term (Term_ty_infer.mk_ty_hyp_term prop_c term_c) prop_c judgment_c) varg;
         decl (uop "ptag") [ TyToken term_c ] [] term_c (ptag "zero");
         decl (uop "carg") [] [] (Term_ty_infer.mk_ty_sequent_term (Term_ty_infer.mk_ty_hyp_cases_term [ term_c, term_c; prop_c, prop_c ]) term_c judgment_c) carg ])

let tenv =
  { Term_ty_infer.tenv_typeclasses = typeclasses;
    tenv_typereduce = Term_match_table.empty_table;
    tenv_typereductions = Term_ty_infer.Shape2Table.empty;
    tenv_typeenv = typeenv;
    tenv_termenv = termenv }

let show t = Simple_print.SimplePrint.string_of_term t

(* A type is printed when it is a closed term; a type left as a variable
   prints as such, since its name is a fresh symbol. *)
let show_ty t = if is_var_term t then "a type variable" else show t

let run name f =
  let r =
    try f () with
    | RefineError (s, _) -> "REFUSED: " ^ s
    | Failure s -> "FAILURE: " ^ s
    | Invalid_argument s -> "INVALID_ARGUMENT: " ^ s
    | Not_found -> "NOT_FOUND"
  in
  Printf.printf "%-48s %s\n" name r

let infer name t = run ("infer " ^ name) (fun () -> show_ty (Term_ty_infer.infer_term tenv t))
let check name f = run name (fun () -> f (); "OK")

let rw redex contractum = MetaIff (MetaTheorem redex, MetaTheorem contractum)
let so v args = TermMan.mk_so_var_term (Lm_symbol.add v) [] args
let constrain t ty = Term_ty_infer.mk_ty_constrain_term t ty

type h = Hyp of string * term | Ctx of string * string list * term list
let seq arg hyps concl =
  TermMan.mk_sequent_term
    { sequent_args = arg;
      sequent_hyps = SeqHyp.of_list (List.map (function
          | Hyp (v, t) -> Hypothesis (Lm_symbol.add v, t)
          | Ctx (v, cs, ts) -> Context (Lm_symbol.add v, List.map Lm_symbol.add cs, ts)) hyps);
      sequent_concl = concl }
let soc v cs args = TermMan.mk_so_var_term (Lm_symbol.add v) (List.map Lm_symbol.add cs) args
let mnum v = mk_term (mk_op (uop "num") [ make_param (MNumber (Lm_symbol.add v)) ]) []
let mname v = mk_term (mk_op (uop "name") [ make_param (MString (Lm_symbol.add v)) ]) []
let rule subs goal = List.fold_right (fun s acc -> MetaImplies (MetaTheorem s, acc)) subs (MetaTheorem goal)

let () =
  print_endline "== sequents";
  infer "sarg: x: zero >- succ{x}" (seq sarg [ Hyp ("x", zero) ] (succ (var "x")));
  infer "sarg: <H>; x: zero >- x" (seq sarg [ Ctx ("H", [], []); Hyp ("x", zero) ] (var "x"));
  infer "sarg: x: tt >- zero (a Prop hypothesis)" (seq sarg [ Hyp ("x", tt) ] zero);
  infer "sarg: x: eq{zero; zero} >- zero" (seq sarg [ Hyp ("x", eq zero zero) ] zero);
  infer "sarg: >- tt (a Prop conclusion)" (seq sarg [] tt);
  infer "parg: >- tt" (seq parg [] tt);
  infer "parg: >- zero (a Term where a Prop is due)" (seq parg [] zero);
  infer "zero as the sequent argument" (seq zero [] zero);
  infer "carg: x: zero >- x" (seq carg [ Hyp ("x", zero) ] (var "x"));
  infer "carg: x: tt >- zero" (seq carg [ Hyp ("x", tt) ] zero);
  infer "carg: x: eq{zero; zero} >- zero" (seq carg [ Hyp ("x", eq zero zero) ] zero);
  infer "varg: x: zero >- x (x is a Prop)" (seq varg [ Hyp ("x", zero) ] (var "x"));
  infer "varg: x: tt >- zero" (seq varg [ Hyp ("x", tt) ] zero);
  infer "sarg: <H>; x: zero >- 'a<|H|>['x]" (seq sarg [ Ctx ("H", [], []); Hyp ("x", zero) ] (soc "a" [ "H" ] [ var "x" ]));
  infer "sarg: <H>; x: zero; <J<|H|>['x]> >- zero" (seq sarg [ Ctx ("H", [], []); Hyp ("x", zero); Ctx ("J", [ "H" ], [ var "x" ]) ] zero);
  infer "sarg: <H> >- C<|H|>[succ{zero}] (a context term)" (seq sarg [ Ctx ("H", [], []) ] (TermMan.mk_context_term (Lm_symbol.add "C") (succ zero) [ Lm_symbol.add "H" ] []));
  infer "sarg: <H> >- C<|H|>[eq{zero; zero}]" (seq sarg [ Ctx ("H", [], []) ] (TermMan.mk_context_term (Lm_symbol.add "C") (eq zero zero) [ Lm_symbol.add "H" ] []));
  infer "sarg: <H>; x: zero; <J<|H|>[eq{x; x}]> >- zero" (seq sarg [ Ctx ("H", [], []); Hyp ("x", zero); Ctx ("J", [ "H" ], [ eq (var "x") (var "x") ]) ] zero);
  print_endline "== meta-parameters";
  infer "num[@n]" (mnum "n");
  infer "name[@s]" (mname "s");
  infer "tag[@t] (a token meta-parameter)" (mk_term (mk_op (uop "tag") [ make_param (MToken (Lm_symbol.add "t")) ]) []);
  infer "eq{tag[@t]; ptag[@t]} (t names a Prop, then a Term)" (eq (mk_term (mk_op (uop "tag") [ make_param (MToken (Lm_symbol.add "t")) ]) []) (mk_term (mk_op (uop "ptag") [ make_param (MToken (Lm_symbol.add "t")) ]) []));
  infer "eq{ptag[@t]; tag[@t]} (t names a Term, then a Prop)" (eq (mk_term (mk_op (uop "ptag") [ make_param (MToken (Lm_symbol.add "t")) ]) []) (mk_term (mk_op (uop "tag") [ make_param (MToken (Lm_symbol.add "t")) ]) []));
  infer "num[@n:s] (a string meta-parameter)" (mk_term (mk_op (uop "num") [ make_param (MString (Lm_symbol.add "n")) ]) []);
  print_endline "== rules over sequents";
  let s1 = seq sarg [ Ctx ("H", [], []); Hyp ("x", zero) ] (succ (var "x")) in
  let s2 = seq sarg [ Ctx ("H", [], []) ] (lam "x" (succ (var "x"))) in
  check "rule <H>; x: zero >- succ{x}  -->  <H> >- lam" (fun () -> Term_ty_infer.check_rule tenv (rule [ s1 ] s2) []);
  check "rule with <H> then <H['x]> (context arity)" (fun () ->
      Term_ty_infer.check_rule tenv (rule [ seq sarg [ Ctx ("H", [], [ zero ]) ] zero ] s2) []);
  check "rule with a parg subgoal under a sarg goal" (fun () -> Term_ty_infer.check_rule tenv (rule [ seq parg [ Ctx ("H", [], []) ] tt ] s2) []);
  check "rule with <H> in a carg subgoal, sarg goal" (fun () -> Term_ty_infer.check_rule tenv (rule [ seq carg [ Ctx ("H", [], []) ] zero ] s2) []);
  check "rule with <J>; <H<|J|>> in a subgoal, <H> in the goal" (fun () ->
      Term_ty_infer.check_rule tenv (rule [ seq sarg [ Ctx ("J", [], []); Ctx ("H", [ "J" ], []) ] zero ] s2) []);
  check "rule whose context is a hypothesis elsewhere" (fun () ->
      Term_ty_infer.check_rule tenv (rule [ seq sarg [ Hyp ("H", zero) ] zero ] s2) [])
