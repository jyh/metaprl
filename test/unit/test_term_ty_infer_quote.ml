(* Term_ty_infer on QUOTED terms, and on a value whose type is not a term
   type (a sequent, hypothesis, hypothesis-cases, existential or context
   type) where a typeclass is expected: tenv_find_type's quoted arm and
   quote_type, the Quote param, and unify_subtype_typeclass_term with
   shape_of_type, which test_term_ty_infer, _seq, _poly and _seq_types
   leave out.
   The environment is test_term_ty_infer_seq_types's, plus the typeclass
   Quote below Term (as support/display/perv.mli declares it) and
     hy : ty_hyp{Term; Term}     hc : ty_hyp_cases{Term, Term | Prop, Prop}
     ex : ty_exists{Ty; v. v}
   Each case prints the inferred type (on one line), or the first string
   of the RefineError raised; the expected file is the output of the code
   as written, never typed.  Pinned as found, not changed:
     - a quoted term's type is Quote whatever it quotes, its subterms must
       be Quote ('succ{zero} is refused, 'succ{'zero} is not) and its bound
       variables are given type Quote; a twice-quoted term is an unknown term;
     - Quote is below Term, so 'zero is accepted where a Term is expected,
       and zero is refused where a Quote is;
     - a value whose type is not a term type is accepted where a Term is
       expected (same{zero; sarg}, succ{hy}, succ{ex}) and refused where
       any other typeclass is (same{tt; sarg}): its shape is in no type
       environment, so tenv_find_typeclasses gives it Term's classes;
     - a name used as a variable and as a context is accepted as a Term.
   Not reached by any input here: shape_of_type's TypeVar and TypeTerm
   arms (unify_subtype_types handles both before it calls
   unify_subtype_typeclass_term), its TypeSoVar and TypeSCVar arms, and a
   typeclass term on the right that reduces (no type reductions here). *)
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
let quote_o = pop "Quote"
let prop_c = const prop_o
let judgment_c = const judgment_o
let dform_c = const dform_o
let nonterminal_c = const nonterminal_o

let typeclasses =
  List.fold_left (fun tbl (o, supers) -> OpnameTable.add tbl o (OpnameSet.of_list (o :: supers)))
    OpnameTable.empty
    [ Term_ty_infer.term_opname, []; Term_ty_infer.type_opname, []; judgment_o, []; dform_o, [];
      nonterminal_o, []; prop_o, [ Term_ty_infer.term_opname ];
      (* as support/display/perv.mli declares it: typeclass Quote -> Term *)
      quote_o, [ Term_ty_infer.term_opname ] ]

(* every typeclass term is itself a type, in its own class *)
let typeenv =
  let env = OpnameTable.fold (fun env o _ -> ShapeTable.add env (shape_of_term (const o)) o) ShapeTable.empty typeclasses in
    ShapeTable.add env (shape_of_term (mk_term (mk_op (uop "List") []) [ mk_bterm [] (const prop_o) ])) Term_ty_infer.term_opname

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
let app o ts = mk_term (mk_op (uop o) []) (List.map (fun t -> mk_bterm [] t) ts)
let list_ty a = app "List" [ a ]
let nil = const (uop "nil")
let cons a l = app "cons" [ a; l ]
let same a b = app "same" [ a; b ]
let earg = const (uop "earg")
let harg = const (uop "harg")
let qarg = const (uop "qarg")
let ctx c t = TermMan.mk_context_term (Lm_symbol.add c) t [] []
(* a context with one argument and zero in its hole *)
let ctxa c a = TermMan.mk_context_term (Lm_symbol.add c) zero [] [ a ]
let carg2 = const (uop "carg2")
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
         decl (uop "carg") [] [] (Term_ty_infer.mk_ty_sequent_term (Term_ty_infer.mk_ty_hyp_cases_term [ term_c, term_c; prop_c, prop_c ]) term_c judgment_c) carg;
         (* polymorphic List, nil, cons, same *)
         decl (uop "List") [] [ bt [] type_c ] type_c (list_ty x);
         decl (uop "nil") [] [] (list_ty (var "a")) nil;
         decl (uop "cons") [] [ bt [] (var "a"); bt [] (list_ty (var "a")) ] (list_ty (var "a")) (cons zero nil);
         decl (uop "same") [] [ bt [] (var "a"); bt [] (var "a") ] term_c (same zero zero);
         (* earg: a hypothesis's type is an existential  exists v: Ty. v : v *)
         decl (uop "earg") [] [] (Term_ty_infer.mk_ty_sequent_term
            (Term_ty_infer.mk_ty_exists_term (Lm_symbol.add "v") type_c (Term_ty_infer.mk_ty_hyp_term (var "v") (var "v"))) term_c judgment_c) earg;
         (* harg: the hypothesis type is a type variable *)
         decl (uop "qarg") [] [] (Term_ty_infer.mk_ty_sequent_term (Term_ty_infer.mk_ty_hyp_term prop_c term_c) term_c judgment_c) qarg;
         decl (uop "carg2") [] [] (Term_ty_infer.mk_ty_sequent_term (Term_ty_infer.mk_ty_hyp_cases_term [ prop_c, term_c; prop_c, prop_c ]) term_c judgment_c) carg2;
         decl (uop "harg") [] [] (Term_ty_infer.mk_ty_sequent_term (var "h") term_c judgment_c) harg;
         (* constants whose types are a hypothesis type, hypothesis cases and an existential *)
         decl (uop "hy") [] [] (Term_ty_infer.mk_ty_hyp_term term_c term_c) (const (uop "hy"));
         decl (uop "hc") [] [] (Term_ty_infer.mk_ty_hyp_cases_term [ term_c, term_c; prop_c, prop_c ]) (const (uop "hc"));
         decl (uop "ex") [] [] (Term_ty_infer.mk_ty_exists_term (Lm_symbol.add "v") type_c (var "v")) (const (uop "ex")) ])

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
  let r = String.concat " " (List.filter (fun w -> w <> "") (String.split_on_char ' ' (String.map (fun c -> if c = '\n' then ' ' else c) r))) in
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

let q t = TermOp.quote_term t
let () =
  infer "zero" zero;
  infer "'zero" (q zero);
  infer "'tt" (q tt);
  infer "'succ{zero}" (q (succ zero));
  infer "'succ{'zero}" (q (succ (q zero)));
  infer "succ{'zero}" (succ (q zero));
  infer "'num[3]" (q (num 3));
  infer "'name[\"a\"]" (q (sname "a"));
  infer "'tag[tt]" (q (tag "tt"));
  infer "'lam{x. x}" (q (lam "x" (var "x")));
  infer "'lam{x. 'zero}" (q (lam "x" (q zero)));
  infer "'nil" (q nil);
  infer "'cons{'zero; 'nil}" (q (cons (q zero) (q nil)));
  infer "cons{'zero; nil}" (cons (q zero) nil);
  infer "cons{'zero; cons{zero; nil}}" (cons (q zero) (cons zero nil));
  infer "cons{zero; cons{'zero; nil}}" (cons zero (cons (q zero) nil));
  infer "same{'zero; zero}" (same (q zero) zero);
  infer "same{zero; 'zero}" (same zero (q zero));
  infer "same{'zero; 'tt}" (same (q zero) (q tt));
  infer "eq{'zero; zero}" (eq (q zero) zero);
  infer "''zero" (q (q zero));
  infer "'unknown" (q (const (uop "unknown")));
  infer "'sarg" (q sarg);
  infer "'List{tt}" (q (list_ty tt));
  infer "same{'zero; 'zero}" (same (q zero) (q zero));
  infer "cons{'zero; cons{'tt; nil}}" (cons (q zero) (cons (q tt) nil));
  (* a non-term type on the left of a subtype, a term type on the right *)
  infer "same{zero; sarg}" (same zero sarg);
  infer "same{tt; sarg}" (same tt sarg);
  infer "same{'zero; sarg}" (same (q zero) sarg);
  infer "same{nil; sarg}" (same nil sarg);
  infer "succ{sarg}" (succ sarg);
  infer "succ{carg}" (succ carg);
  infer "cons{zero; cons{sarg; nil}}" (cons zero (cons sarg nil));
  infer "same{zero; earg: x: zero >- x}" (same zero (seq earg [ Hyp ("x", zero) ] (var "x")));
  infer "same{zero; lam{x. x}}" (same zero (lam "x" (var "x")));
  let hy = const (uop "hy") and hc = const (uop "hc") and ex = const (uop "ex") in
  infer "hy" hy;
  infer "hc" hc;
  infer "ex" ex;
  infer "same{zero; hy}" (same zero hy);
  infer "same{tt; hy}" (same tt hy);
  infer "same{zero; hc}" (same zero hc);
  infer "same{zero; ex}" (same zero ex);
  infer "same{tt; ex}" (same tt ex);
  infer "succ{hy}" (succ hy);
  infer "succ{hc}" (succ hc);
  infer "succ{ex}" (succ ex);
  infer "same{nil; hy}" (same nil hy);
  infer "same{hy; zero}" (same hy zero);
  (* a name used as a variable on the right of a Term and as a context, a
     second-order variable or a sequent context elsewhere *)
  infer "eq{same{zero; C}; succ{C[zero]}}" (eq (same zero (var "C")) (succ (ctx "C" zero)));
  infer "eq{succ{C[zero]}; same{zero; C}}" (eq (succ (ctx "C" zero)) (same zero (var "C")));
  infer "eq{succ{C[zero]}; succ{C}}" (eq (succ (ctx "C" zero)) (succ (var "C")));
  infer "eq{succ{'a[zero]}; same{zero; a}}" (eq (succ (so "a" [ zero ])) (same zero (var "a")));
  infer "eq{succ{'a[zero]}; succ{a}}" (eq (succ (so "a" [ zero ])) (succ (var "a")));
  infer "eq{same{<H> >- zero; sarg}; same{zero; H}}" (eq (same (seq sarg [ Ctx ("H", [], []) ] zero) sarg) (same zero (var "H")));
  infer "eq{succ{<H> >- zero}; succ{H}}" (eq (succ (seq sarg [ Ctx ("H", [], []) ] zero)) (succ (var "H")))
