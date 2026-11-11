(* Term_ty_infer on SEQUENT TYPES used as values and on hypothesis types
   that are existentials or type variables: the unification of ty_sequent,
   ty_hyp and ty_hyp_cases types (equal and subtype), expand_hyp_type's
   existential arms and standardize_ty_hyp, which test_term_ty_infer_seq
   (sequents checked against their argument's type) and
   test_term_ty_infer_poly leave out.
   The environment is test_term_ty_infer_seq's, plus
     List{Ty} : Ty     nil : List{'a}     cons{'a; List{'a}} : List{'a}
     same{'a; 'a} : Term
     qarg   hypotheses  x: Prop . Term, conclusion Term, a Judgment
     carg2  hypotheses in two cases (x: Prop . Term | x: Prop . Prop),
            conclusion Term, a Judgment
     earg   hypotheses  exists v: Ty. (x: 'v . 'v), conclusion Term
     harg   hypotheses  a type variable, conclusion Term
   Each case prints the inferred type (on one line), or the first string
   of the RefineError raised; the expected file is the output of the code
   as written, never typed.  Pinned as found, not changed:
     - a sequent argument is a value of its sequent type: same{sarg; parg}
       is a Term (a Prop conclusion is below a Term one) and
       same{parg; sarg} is refused; in a List the types must be equal;
     - a hypothesis's variable type is contravariant: same{qarg; sarg} is a
       Term and same{sarg; qarg} is refused;
     - an existential hypothesis type accepts a hypothesis of any type,
       a Judgment included;
     - in check_rule the GOAL is inferred first, so a second-order
       variable's argument type is fixed there: 'a[zero] in a subgoal under
       'a[tt] in the goal is refused, 'a[tt] under 'a[x: Term] is not.
   Not reached by any input here: the unification arms for two
   second-order-variable or two context types (TypeSoVar, TypeCVar,
   TypeSCVar). *)
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
         decl (uop "harg") [] [] (Term_ty_infer.mk_ty_sequent_term (var "h") term_c judgment_c) harg ])

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

let () =
  infer "same{sarg; sarg}" (same sarg sarg);
  infer "same{sarg; parg}" (same sarg parg);
  infer "same{parg; sarg}" (same parg sarg);
  infer "same{carg; carg}" (same carg carg);
  infer "same{carg; sarg}" (same carg sarg);
  infer "same{sarg; carg}" (same sarg carg);
  infer "same{qarg; sarg}" (same qarg sarg);
  infer "same{sarg; qarg}" (same sarg qarg);
  infer "cons{sarg; cons{sarg; nil}}" (cons sarg (cons sarg nil));
  infer "cons{sarg; cons{parg; nil}}" (cons sarg (cons parg nil));
  infer "cons{carg; cons{carg; nil}}" (cons carg (cons carg nil));
  infer "cons{carg; cons{sarg; nil}}" (cons carg (cons sarg nil));
  infer "cons{qarg; cons{sarg; nil}} (x: Prop vs x: Term)" (cons qarg (cons sarg nil));
  infer "cons{carg; cons{carg2; nil}} (a case's x differs)" (cons carg (cons carg2 nil));
  infer "same{earg: x: zero >- x; earg: x: eq >- zero}"
    (same (seq earg [ Hyp ("x", zero) ] (var "x")) (seq earg [ Hyp ("x", eq zero zero) ] zero));
  infer "earg: x: zero >- x" (seq earg [ Hyp ("x", zero) ] (var "x"));
  infer "earg: x: zero; y: tt >- x" (seq earg [ Hyp ("x", zero); Hyp ("y", tt) ] (var "x"));
  infer "earg: <H>; x: zero >- x" (seq earg [ Ctx ("H", [], []); Hyp ("x", zero) ] (var "x"));
  infer "earg: x: eq{zero; zero} >- zero" (seq earg [ Hyp ("x", eq zero zero) ] zero);
  infer "harg: x: zero >- x" (seq harg [ Hyp ("x", zero) ] (var "x"));
  infer "harg: <H>; x: zero >- zero" (seq harg [ Ctx ("H", [], []); Hyp ("x", zero) ] zero);
  let sJ c = seq sarg [ Ctx ("H", [], []); Hyp ("x", zero); Ctx ("J", [ "H" ], [ var "x" ]) ] c in
  check "rule <H>; x; <J<|H|>[x]> >- zero --> same, succ{zero}" (fun () -> Term_ty_infer.check_rule tenv (rule [ sJ zero ] (sJ (succ zero))) []);
  check "rule <J<|H|>[x]> then <J<|H|>[tt]>" (fun () ->
      Term_ty_infer.check_rule tenv (rule [ sJ zero ] (seq sarg [ Ctx ("H", [], []); Hyp ("x", zero); Ctx ("J", [ "H" ], [ tt ]) ] zero)) []);
  check "rule 'a<|H|>[x] then 'a<|H|>[tt]" (fun () ->
      Term_ty_infer.check_rule tenv (rule [ seq sarg [ Ctx ("H", [], []); Hyp ("x", zero) ] (soc "a" [ "H" ] [ var "x" ]) ]
        (seq sarg [ Ctx ("H", [], []) ] (soc "a" [ "H" ] [ tt ]))) []);
  check "rule 'a<|H|>[x] then 'a<|H|>[eq]" (fun () ->
      Term_ty_infer.check_rule tenv (rule [ seq sarg [ Ctx ("H", [], []); Hyp ("x", zero) ] (soc "a" [ "H" ] [ var "x" ]) ]
        (seq sarg [ Ctx ("H", [], []) ] (soc "a" [ "H" ] [ eq zero zero ]))) []);
  check "rule 'a<|H|>[tt] then 'a<|H|>[x] (goal)" (fun () ->
      Term_ty_infer.check_rule tenv (rule [ seq sarg [ Ctx ("H", [], []) ] (soc "a" [ "H" ] [ tt ]) ]
        (seq sarg [ Ctx ("H", [], []); Hyp ("x", zero) ] (soc "a" [ "H" ] [ var "x" ]))) []);
  check "rule 'a<|H|>[zero] then 'a<|H|>[tt] (goal)" (fun () ->
      Term_ty_infer.check_rule tenv (rule [ seq sarg [ Ctx ("H", [], []) ] (soc "a" [ "H" ] [ zero ]) ]
        (seq sarg [ Ctx ("H", [], []) ] (soc "a" [ "H" ] [ tt ]))) []);
  check "rewrite same{'a; 'b} <--> same{'b; 'a}" (fun () -> Term_ty_infer.check_rewrite tenv (rw (same (so "a" []) (so "b" [])) (same (so "b" []) (so "a" []))) []);
  check "rewrite C[zero] <--> C[tt] (a context)" (fun () ->
      Term_ty_infer.check_rewrite tenv (rw (TermMan.mk_context_term (Lm_symbol.add "C") zero [] []) (TermMan.mk_context_term (Lm_symbol.add "C") tt [] [])) [])
