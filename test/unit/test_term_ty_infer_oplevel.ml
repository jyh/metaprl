(* Term_ty_infer on the two parameter kinds test_term_ty_infer and its
   siblings never infer: an Operator parameter and a level parameter.
   Two declarations, built the way test_term_ty_infer builds its
   environment (class Term only):
     opk[o:op] : Term     lev[l:l] : Term
   Inference looks each declaration up, renames its free variables
   (standardize_ty_term, which reads every parameter kind) and checks each
   parameter against its declared kind (infer_params). Each case prints
   the inferred type, or the first string of the RefineError raised; the
   expected file is the output of the code as written, never typed. *)
open Opname
open Term_sig
open Term_ty_sig
open Refiner.Refiner
open TermType
open Term
open TermShape
open RefineError
open TermMan

let uop s = make_opname [ s; "Test" ]
let const o = mk_term (mk_op o []) []
let term_c = Term_ty_infer.term_type
let type_c = Term_ty_infer.type_type

let typeclasses =
  List.fold_left (fun tbl (o, supers) -> OpnameTable.add tbl o (OpnameSet.of_list (o :: supers)))
    OpnameTable.empty [ Term_ty_infer.term_opname, []; Term_ty_infer.type_opname, [] ]

let typeenv =
  OpnameTable.fold (fun env o _ -> ShapeTable.add env (shape_of_term (const o)) o) ShapeTable.empty typeclasses

let decl o params ty t = { ty_term = t; ty_opname = o; ty_params = params; ty_bterms = []; ty_type = ty }

let with_param o p = mk_term (mk_op (uop o) [ make_param p ]) []
let level n = mk_const_level_exp n
let opk o = with_param "opk" (Operator { opparam_name = make_opname [ o ]; opparam_params = []; opparam_arities = [] })
let lev l = with_param "lev" (MLevel l)

let termenv =
  let classes = OpnameTable.fold (fun l o _ -> decl o [] type_c (const o) :: l) [] typeclasses in
  List.fold_left (fun env d -> ShapeTable.add env (shape_of_term d.ty_term) d) ShapeTable.empty
    (classes @ [ decl (uop "opk") [ TyOperator ] term_c (opk "a"); decl (uop "lev") [ TyLevel ] term_c (lev (level 0)) ])

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
  Printf.printf "%-40s %s\n" name r

let infer name t = run ("infer " ^ name) (fun () -> Simple_print.SimplePrint.string_of_term (Term_ty_infer.infer_term tenv t))

let () =
  infer "opk[a] (an operator parameter)" (opk "a");
  infer "opk[b]" (opk "b");
  infer "lev[1] (a constant level)" (lev (level 1));
  infer "lev['x] (a level variable)" (lev (mk_var_level_exp (Lm_symbol.add "x")));
  infer "lev[\"s\"] (a string, not a level)" (with_param "lev" (String "s"));
  infer "opk[3] (a number, not an operator)" (with_param "opk" (Number (Lm_num.num_of_int 3)))
