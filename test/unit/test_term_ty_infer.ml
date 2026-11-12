(* Term_ty_infer (refiner/reflib), the filter's type checker for terms,
   rules, rewrites, display forms, iforms and grammar productions, which no
   unit test reached (2026-11-11 reach census: the proof census runs 480 of
   its 1,310 points, the unit tests 0).
   The environment is built by hand, the way Filter_cache_fun builds its
   root: a typeclass maps to the set of itself and its superclasses, the
   typeenv sends a type's shape to its typeclass (Term when absent), and
   the termenv gives each declared term its ty_term.  Here:
     classes  Term, Ty, Judgment, Dform, Nonterminal (each alone) and
              Prop (Prop and Term: a Prop is also a Term);
     terms    zero : Term          succ{Term} : Term
              tt : Prop            lam{x: Term. Term} : Term
              num[n:n] : Term      name[s:s] : Term
              tag[t:t] : Term, whose token must name a term of type Prop
              and two declarations that disagree with their own term (the
              filter never builds one; they reach the defensive checks):
              bad{x. Term} declared with no binder, odd[n:n] declared with
              a string parameter
              eq{Term; Term} : Judgment
              df{Term} : Dform     nt : Nonterminal
   Each case prints the inferred type, or the first string of the
   RefineError it raises; the expected file is the output of the code as
   written (2026-11-11), never typed.  Pinned as found, not changed:
   check_rewrite checks the redex's type against the contractum's in BOTH
   directions (its "verify the rewrite in the reverse direction" step),
   so zero <--> tt is refused although a Prop is a Term; and infer_term
   runs in Strict mode, where a type constraint is not read, so
   zero-constrained-to-Term is an unknown term there.  Also: erase_term removes type
   constraints at every depth and erase_arg_term only at the top, and
   is_seq_ignore_bindings_tp recognises a sequent type whose hypotheses
   bind Ignore. *)
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
         decl (uop "df") [] [ bt [] term_c ] dform_c (df zero) ])

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

let () =
  print_endline "== infer_term";
  infer "zero" zero;
  infer "succ{zero}" (succ zero);
  infer "succ{tt} (Prop below Term)" (succ tt);
  infer "eq{zero; tt}" (eq zero (succ tt));
  infer "succ{eq{zero; zero}} (Judgment is no Term)" (succ (eq zero zero));
  infer "lam{x. succ{x}}" (lam "x" (succ (var "x")));
  infer "lam{x. eq{x; x}} (body must be a Term)" (lam "x" (eq (var "x") (var "x")));
  infer "num[3]" (num 3);
  infer "name[\"a\"] (string parameter)" (sname "a");
  infer "name[a] (token where a string is declared)" (tname "a");
  infer "tag[tt] (tt : Prop)" (tag "tt");
  infer "tag[zero] (zero : Term, no Prop)" (tag "zero");
  infer "tag[undeclared]" (tag "undeclared");
  infer "bad{x. zero} (declared without its binder)" (bad "x" zero);
  infer "odd[1] (declared with a string parameter)" (odd 1);
  infer "a free variable x" (var "x");
  infer "succ{x} (free x)" (succ (var "x"));
  infer "eq{x; succ{x}} (free x)" (eq (var "x") (succ (var "x")));
  infer "'a[zero] (second-order variable)" (so "a" [ zero ]);
  infer "succ{'a[zero]}" (succ (so "a" [ zero ]));
  infer "an undeclared term" (const (uop "undeclared"));
  infer "succ with two subterms" (mk_term (mk_op (uop "succ") []) [ mk_bterm [] zero; mk_bterm [] zero ]);
  infer "the typeclass term Term" term_c;
  infer "the typeclass term Prop" prop_c;
  infer "zero constrained to Term" (constrain zero term_c);
  print_endline "== check_rule";
  check "rule eq{zero; zero}" (fun () -> Term_ty_infer.check_rule tenv (MetaTheorem (eq zero zero)) []);
  check "rule zero (goal is no Judgment)" (fun () -> Term_ty_infer.check_rule tenv (MetaTheorem zero) []);
  check "rule eq{x;x} --> eq{succ{x}; succ{x}}" (fun () ->
      Term_ty_infer.check_rule tenv
        (MetaImplies (MetaTheorem (eq (var "x") (var "x")), MetaTheorem (eq (succ (var "x")) (succ (var "x"))))) []);
  check "rule with subgoal zero (no Judgment)" (fun () ->
      Term_ty_infer.check_rule tenv (MetaImplies (MetaTheorem zero, MetaTheorem (eq zero zero))) []);
  check "rule with argument succ{zero}" (fun () ->
      Term_ty_infer.check_rule tenv (MetaTheorem (eq zero zero)) [ succ zero ]);
  check "rule with argument eq{.} constrained to Term" (fun () ->
      Term_ty_infer.check_rule tenv (MetaTheorem (eq zero zero)) [ constrain (eq zero zero) term_c ]);
  print_endline "== check_rewrite";
  check "rewrite succ{zero} <--> zero" (fun () -> Term_ty_infer.check_rewrite tenv (rw (succ zero) zero) []);
  check "rewrite succ{'a} <--> 'a" (fun () -> Term_ty_infer.check_rewrite tenv (rw (succ (so "a" [])) (so "a" [])) []);
  check "rewrite zero <--> tt (Prop below Term)" (fun () -> Term_ty_infer.check_rewrite tenv (rw zero tt) []);
  check "rewrite tt <--> zero (Term not below Prop)" (fun () -> Term_ty_infer.check_rewrite tenv (rw tt zero) []);
  check "rewrite zero <--> eq{zero; zero}" (fun () -> Term_ty_infer.check_rewrite tenv (rw zero (eq zero zero)) []);
  check "rewrite with condition zero" (fun () ->
      Term_ty_infer.check_rewrite tenv (MetaImplies (MetaTheorem zero, rw (succ zero) zero)) []);
  check "rewrite with condition eq{.} (no Term)" (fun () ->
      Term_ty_infer.check_rewrite tenv (MetaImplies (MetaTheorem (eq zero zero), rw (succ zero) zero)) []);
  print_endline "== check_type_rewrite, check_dform, check_iform, check_production";
  check "type rewrite Prop --> Term" (fun () -> Term_ty_infer.check_type_rewrite tenv prop_c term_c);
  check "type rewrite zero --> Term (zero is no type)" (fun () -> Term_ty_infer.check_type_rewrite tenv zero term_c);
  check "dform df{zero} = df{succ{zero}}" (fun () -> Term_ty_infer.check_dform tenv (df zero) (df (succ zero)));
  check "dform df{zero} = zero (no Dform)" (fun () -> Term_ty_infer.check_dform tenv (df zero) zero);
  check "iform succ{zero} <--> eq{zero; zero}" (fun () -> Term_ty_infer.check_iform tenv (rw (succ zero) (eq zero zero)));
  check "iform of an undeclared term" (fun () -> Term_ty_infer.check_iform tenv (rw (const (uop "undeclared")) zero));
  check "production nt nt --> nt" (fun () -> Term_ty_infer.check_production tenv [ nt; nt ] nt);
  check "production nt --> zero (no Nonterminal)" (fun () -> Term_ty_infer.check_production tenv [ nt ] zero);
  print_endline "== erase";
  let c = constrain in
  let t = c (succ (c (succ (c zero term_c)) term_c)) term_c in
  Printf.printf "%-48s %s\n" "the constrained term" (show t);
  Printf.printf "%-48s %s\n" "erase_term" (show (Term_ty_infer.erase_term t));
  Printf.printf "%-48s %s\n" "erase_arg_term" (show (Term_ty_infer.erase_arg_term t));
  Printf.printf "%-48s %s\n" "erase_arg_term of an unconstrained term" (show (Term_ty_infer.erase_arg_term zero));
  let mt = Term_ty_infer.erase_meta_term (MetaImplies (MetaTheorem t, MetaTheorem (c zero term_c))) in
  (match mt with
   | MetaImplies (MetaTheorem a, MetaTheorem b) ->
       Printf.printf "%-48s %s / %s\n" "erase_meta_term" (show a) (show b)
   | _ -> print_endline "erase_meta_term: a different meta-term shape");
  print_endline "== is_seq_ignore_bindings_tp";
  (* mk_ty_hyp_term takes the type of the bound variable first, then the
     hypothesis's type: "Ignore in the binding position" is the first *)
  let seq_b bind hyp = Term_ty_infer.mk_ty_sequent_term (Term_ty_infer.mk_ty_hyp_term bind hyp) term_c term_c in
  let seq hyp = seq_b term_c hyp in
  let ignore_c = const ignore_o in
  List.iter (fun (name, ty) ->
      Printf.printf "%-48s %b\n" name (Term_ty_infer.is_seq_ignore_bindings_tp (decl (uop "s") [] [] ty zero)))
    [ "a sequent binding Ignore", seq_b ignore_c term_c;
      "a sequent binding Term, hypothesis Ignore", seq ignore_c;
      "a sequent binding Term", seq term_c;
      "a sequent with hypothesis cases",
      Term_ty_infer.mk_ty_sequent_term (Term_ty_infer.mk_ty_hyp_cases_term [ term_c, ignore_c ]) term_c term_c;
      "not a sequent type", term_c ];
  print_endline "== dest_ty_sequent_cases";
  let cases, concl, s =
    Term_ty_infer.dest_ty_sequent_cases
      (Term_ty_infer.mk_ty_sequent_term (Term_ty_infer.mk_ty_hyp_cases_term [ term_c, prop_c; type_c, ignore_c ]) dform_c judgment_c)
  in
  Printf.printf "%-48s %s | %s | %s\n" "two cases"
    (String.concat ", " (List.map (fun (a, b) -> show a ^ ":" ^ show b) cases)) (show concl) (show s);
  let cases, _, _ = Term_ty_infer.dest_ty_sequent_cases (seq prop_c) in
  Printf.printf "%-48s %s\n" "one hypothesis"
    (String.concat ", " (List.map (fun (a, b) -> show a ^ ":" ^ show b) cases))
