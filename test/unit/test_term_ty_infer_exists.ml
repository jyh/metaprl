(* Term_ty_infer on NESTED existential types (exst a: Ty. exst b: Ty. ...),
   which reach type_subst's TypeExists arm.  No unit test reached that arm
   (coverage recount 11-12: type_subst's structural arms and
   standardize_ty_var's never reached).  A term whose type is an
   existential is opened by instantiate_ty_var when it is checked against
   another type: each bound variable becomes a fresh type constant, and
   type_subst puts that constant into the rest of the type, including an
   inner exst.  A taker whose argument type is an existential accepts a
   Pair{'a; 'a} for any 'a (standardize_ty_var).  The environment is
   test_term_ty_infer_poly's classes and Pair, with
     some2 : exst a: Ty. exst b: Ty. Pair{'a; 'b}
     diag  : exst a: Ty. Pair{'a; 'a}
     some3 : exst a: Ty. exst b: Ty. exst c: Ty. Pair{'a; Pair{'b; 'c}}
   and takers tk2 (some2's type), tks (Pair{'b; 'a}), tkd (diag's type),
   tk3 (some3's type), tkd3 (exst a. exst b. Pair{'a; Pair{'b; 'b}}) and
   tkt (Pair{Term; Term}).  Each case prints the inferred type, or the
   first string of the error raised; the expected file is the output of
   the code as written, never typed.
   tkd{some2} and tkd3{some3} are refused: an exists over two variables
   is not an exists over one variable used twice.  They were accepted
   while type_subst rebuilt an inner exst under the substituted
   variable's name and substituted its body a second time, which left
   the inner variable free. *)
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
let diag3_ty = ex "a" type_c (ex "b" type_c (pair_ty (var "a") (pair_ty (var "b") (var "b"))))

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
         decl (uop "some2") [] some2_ty (c0 "some2");
         decl (uop "diag") [] diag_ty (c0 "diag");
         decl (uop "some3") [] some3_ty (c0 "some3");
         decl (uop "tk2") [ bt some2_ty ] term_c (tk "tk2" zero);
         decl (uop "tks") [ bt swap2_ty ] term_c (tk "tks" zero);
         decl (uop "tkd") [ bt diag_ty ] term_c (tk "tkd" zero);
         decl (uop "tk3") [ bt some3_ty ] term_c (tk "tk3" zero);
         decl (uop "tkd3") [ bt diag3_ty ] term_c (tk "tkd3" zero);
         decl (uop "tkt") [ bt (pair_ty term_c term_c) ] term_c (tk "tkt" zero) ])

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
  infer "some2" (c0 "some2");
  infer "tk2{some2}" (tk "tk2" (c0 "some2"));
  infer "tks{some2}" (tk "tks" (c0 "some2"));
  infer "tkd{some2}" (tk "tkd" (c0 "some2"));
  infer "tkd{diag}" (tk "tkd" (c0 "diag"));
  infer "tk2{diag}" (tk "tk2" (c0 "diag"));
  infer "tk2{pair{zero; tt}}" (tk "tk2" (pair zero tt));
  infer "tkd{pair{zero; tt}}" (tk "tkd" (pair zero tt));
  infer "tkd{pair{zero; zero}}" (tk "tkd" (pair zero zero));
  infer "tkt{some2}" (tk "tkt" (c0 "some2"));
  infer "tkt{diag}" (tk "tkt" (c0 "diag"));
  infer "tk3{some3}" (tk "tk3" (c0 "some3"));
  infer "tkd3{some3}" (tk "tkd3" (c0 "some3"));
  infer "tk3{pair{zero; pair{tt; zero}}}" (tk "tk3" (pair zero (pair tt zero)))
