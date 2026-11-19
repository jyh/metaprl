(* Term_ty_infer.type_subst on existential types whose body is not a
   term: a type variable (exst a: Ty. 'a), a hypothesis type
   (ty_hyp{'a; Term}), hypothesis cases, and a sequent type.  Only the
   TypeTerm and TypeExists arms were reached (2026-11-15 rank:
   type_subst's TypeVar, TypeHyp, TypeHypCases and TypeSequent arms, and
   free_vars_type's TypeHypCases, TypeExists and TypeSequent arms, unreached by
   the unit tests, the theory build and the proof census).  The
   environment is test_term_ty_infer_exists's classes and Pair, with a
   value and a taker of each type: anyv/tka (exst a: Ty. 'a), hv/tkh
   (the hypothesis), cv/tkc (the cases), sv/tkq (the sequent), and
   hv2, cv2, sv2 bound by b where the takers bind a (tkq3 is the
   sequent with the variable in the conclusion only, as sv2 has it);
   hvp, cvp, svp put Pair{Term; Term} where the taker has 'a, and are
   accepted: a taker's existential is solved, so its 'a may be the Pair.
   A value's existential is opened instead (instantiate_ty_var): each
   bound variable becomes a fresh constant, which is not a Pair.  So
   hv2, cv2, sv2 are refused by takers whose types are concrete, with
   the Pair where the value has 'b (tkhp, tkcp, tkqp); a type variable
   left in the constant's place would unify with the Pair.  cv3/tkcp3
   is the one case with 'b in its variable position only.  A taker
   applied to a value of its type unifies two existentials (each body is
   substituted with one fresh constant); applied to zero it opens the
   taker's type (instantiate_ty_var).  Each case prints the inferred
   type, or the first string of the error raised; the expected file is
   the output of the code as written (2026-11-15), never typed.
   Not reached, and why: type_subst's TypeSoVar, TypeCVar and TypeSCVar
   arms (normalize_term never builds those types, so no existential's
   body holds one), and free_vars_type, whose only caller,
   free_vars_subst, runs in rule and rewrite checking (instantiate_subst),
   not in infer_term.
   Pinned as found: tka{hv} (exst a: Ty. 'a given a hypothesis type) is
   refused with tenv_find_type "unknown term", where tka takes zero and
   pair{zero; tt}. *)
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
let app o ts = mk_term (mk_op (uop o) []) (List.map (fun t -> mk_bterm [] t) ts)

let term_c = Term_ty_infer.term_type
let type_c = Term_ty_infer.type_type
let prop_o = pop "Prop"
let judgment_o = pop "Judgment"
let prop_c = const prop_o

let typeclasses =
  List.fold_left (fun tbl (o, supers) -> OpnameTable.add tbl o (OpnameSet.of_list (o :: supers)))
    OpnameTable.empty
    [ Term_ty_infer.term_opname, []; Term_ty_infer.type_opname, []; judgment_o, []; prop_o, [ Term_ty_infer.term_opname ] ]

let var v = mk_var_term (Lm_symbol.add v)
let pair_ty a b = app "Pair" [ a; b ]
let ex v b t = Term_ty_infer.mk_ty_exists_term (Lm_symbol.add v) b t

(* exst a: Ty. exst b: Ty. Pair{'a; 'b} and its variants *)
let some2_ty = ex "a" type_c (ex "b" type_c (pair_ty (var "a") (var "b")))
let swap2_ty = ex "a" type_c (ex "b" type_c (pair_ty (var "b") (var "a")))
let diag_ty = ex "a" type_c (pair_ty (var "a") (var "a"))
let some3_ty = ex "a" type_c (ex "b" type_c (ex "c" type_c (pair_ty (var "a") (pair_ty (var "b") (var "c")))))
let shadow_ty = ex "a" type_c (ex "a" type_c (pair_ty (var "a") (var "a")))
let diag3_ty = ex "a" type_c (ex "b" type_c (pair_ty (var "a") (pair_ty (var "b") (var "b"))))

let hyp_c v t = Term_ty_infer.mk_ty_hyp_term v t
let anyv_ty = ex "a" type_c (var "a")
let hyp_ty = ex "a" type_c (hyp_c (var "a") term_c)
let cases_ty = ex "a" type_c (Term_ty_infer.mk_ty_hyp_cases_term [ var "a", term_c; term_c, var "a" ])
let seq_ty = ex "a" type_c (Term_ty_infer.mk_ty_sequent_term (hyp_c (var "a") term_c) (var "a") (const judgment_o))
(* the same types bound by b, so a taker's a and a value's b must both be substituted *)
let hyp2_ty = ex "b" type_c (hyp_c (var "b") term_c)
let cases2_ty = ex "b" type_c (Term_ty_infer.mk_ty_hyp_cases_term [ var "b", term_c; term_c, var "b" ])
let seq2_ty = ex "b" type_c (Term_ty_infer.mk_ty_sequent_term (hyp_c term_c term_c) (var "b") (const judgment_o))
let seq3_ty = ex "a" type_c (Term_ty_infer.mk_ty_sequent_term (hyp_c term_c term_c) (var "a") (const judgment_o))
(* values with a Pair where the taker has 'a (accepted), and concrete takers with the Pair where the value has 'b *)
let pp = pair_ty term_c term_c
let cases3_ty = ex "b" type_c (Term_ty_infer.mk_ty_hyp_cases_term [ var "b", term_c ])
let hypp_ty = ex "b" type_c (hyp_c pp term_c)
let casesp_ty = ex "b" type_c (Term_ty_infer.mk_ty_hyp_cases_term [ pp, term_c; term_c, pp ])
let seqp_ty = ex "b" type_c (Term_ty_infer.mk_ty_sequent_term (hyp_c term_c term_c) pp (const judgment_o))

let typeenv =
  let env = OpnameTable.fold (fun env o _ -> ShapeTable.add env (shape_of_term (const o)) o) ShapeTable.empty typeclasses in
    ShapeTable.add env (shape_of_term (pair_ty term_c term_c)) Term_ty_infer.term_opname

let decl o bterms ty t = { ty_term = t; ty_opname = o; ty_params = []; ty_bterms = bterms; ty_type = ty }
let bt ty = { ty_bvars = []; ty_bterm = ty }
let c0 s = const (uop s)
let zero = c0 "zero"
let tt = c0 "tt"
let pair a b = app "pair" [ a; b ]
let tk n x = app n [ x ]

let termenv =
  let classes = OpnameTable.fold (fun l o _ -> decl o [] type_c (const o) :: l) [] typeclasses in
  let a = var "a" and b = var "b" and x = var "x" in
  List.fold_left (fun env d -> ShapeTable.add env (shape_of_term d.ty_term) d) ShapeTable.empty
    (classes
     @ [ decl (uop "Pair") [ bt type_c; bt type_c ] type_c (pair_ty x x);
         decl (uop "zero") [] term_c zero;
         decl (uop "tt") [] prop_c tt;
         decl (uop "pair") [ bt a; bt b ] (pair_ty a b) (pair zero zero);
         decl (uop "tkt") [ bt (pair_ty term_c term_c) ] term_c (tk "tkt" zero);
         decl (uop "anyv") [] anyv_ty (c0 "anyv");
         decl (uop "tka") [ bt anyv_ty ] term_c (tk "tka" zero);
         decl (uop "hv") [] hyp_ty (c0 "hv");
         decl (uop "tkh") [ bt hyp_ty ] term_c (tk "tkh" zero);
         decl (uop "cv") [] cases_ty (c0 "cv");
         decl (uop "tkc") [ bt cases_ty ] term_c (tk "tkc" zero);
         decl (uop "sv") [] seq_ty (c0 "sv");
         decl (uop "tkq") [ bt seq_ty ] term_c (tk "tkq" zero);
         decl (uop "hv2") [] hyp2_ty (c0 "hv2");
         decl (uop "cv2") [] cases2_ty (c0 "cv2");
         decl (uop "sv2") [] seq2_ty (c0 "sv2");
         decl (uop "tkq3") [ bt seq3_ty ] term_c (tk "tkq3" zero);
         decl (uop "hvp") [] hypp_ty (c0 "hvp");
         decl (uop "cvp") [] casesp_ty (c0 "cvp");
         decl (uop "svp") [] seqp_ty (c0 "svp");
         decl (uop "tkhp") [ bt (hyp_c pp term_c) ] term_c (tk "tkhp" zero);
         decl (uop "tkcp") [ bt (Term_ty_infer.mk_ty_hyp_cases_term [ pp, term_c; term_c, pp ]) ] term_c (tk "tkcp" zero);
         decl (uop "cv3") [] cases3_ty (c0 "cv3");
         decl (uop "tkcp3") [ bt (Term_ty_infer.mk_ty_hyp_cases_term [ pp, term_c ]) ] term_c (tk "tkcp3" zero);
         decl (uop "tkqp") [ bt (Term_ty_infer.mk_ty_sequent_term (hyp_c term_c term_c) pp (const judgment_o)) ] term_c (tk "tkqp" zero) ])

let tenv =
  { Term_ty_infer.tenv_typeclasses = typeclasses;
    tenv_typereduce = Term_match_table.empty_table;
    tenv_typereductions = Term_ty_infer.Shape2Table.empty;
    tenv_typeenv = typeenv;
    tenv_termenv = termenv }

let run name f =
  let r =
    try f () with
    | RefineError (s, _) -> "REFUSED: " ^ s
    | Failure s -> "FAILURE: " ^ s
    | Invalid_argument s -> "INVALID_ARGUMENT: " ^ s
    | Not_found -> "NOT_FOUND"
  in
  Printf.printf "%-34s %s\n" name r

let infer name t = run name (fun () -> Simple_print.SimplePrint.string_of_term (Term_ty_infer.infer_term tenv t))

let () =
  List.iter (fun (v, tk) ->
      infer v (c0 v);
      infer (tk ^ "{" ^ v ^ "}") (app tk [ c0 v ]);
      infer (tk ^ "{zero}") (app tk [ zero ]);
      infer (tk ^ "{pair{zero; tt}}") (app tk [ pair zero tt ]);
      infer ("tkt{" ^ v ^ "}") (app "tkt" [ c0 v ]))
    [ "anyv", "tka"; "hv", "tkh"; "cv", "tkc"; "sv", "tkq" ];
  infer "tka{hv}" (app "tka" [ c0 "hv" ]);
  infer "tkh{anyv}" (app "tkh" [ c0 "anyv" ]);
  infer "tkh{sv}" (app "tkh" [ c0 "sv" ]);
  infer "tkq{hv}" (app "tkq" [ c0 "hv" ]);
  infer "tkh{hv2}" (app "tkh" [ c0 "hv2" ]);
  infer "tkc{cv2}" (app "tkc" [ c0 "cv2" ]);
  infer "tkq3{sv2}" (app "tkq3" [ c0 "sv2" ]);
  infer "tkq{sv2}" (app "tkq" [ c0 "sv2" ]);
  infer "tkh{hvp}" (app "tkh" [ c0 "hvp" ]);
  infer "tkc{cvp}" (app "tkc" [ c0 "cvp" ]);
  infer "tkq3{svp}" (app "tkq3" [ c0 "svp" ]);
  infer "tkhp{hv2}" (app "tkhp" [ c0 "hv2" ]);
  infer "tkcp{cv2}" (app "tkcp" [ c0 "cv2" ]);
  infer "tkqp{sv2}" (app "tkqp" [ c0 "sv2" ]);
  infer "tkhp{hvp}" (app "tkhp" [ c0 "hvp" ]);
  infer "tkcp{cvp}" (app "tkcp" [ c0 "cvp" ]);
  infer "tkqp{svp}" (app "tkqp" [ c0 "svp" ]);
  infer "tkcp3{cv3}" (app "tkcp3" [ c0 "cv3" ])
