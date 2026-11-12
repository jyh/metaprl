(* Term_ty_infer on terms DECLARED with a level or an operator parameter
   (univ[l:l], opr[op:op]): standardize_ty_term's free-variable fold and
   infer_params's TyLevel and TyOperator arms, which no other unit test
   reaches (test_term_ty_infer_params gives a TYPE a parameter, never a
   term's declaration).  Declarations, all of type Term:
     univ[l:l]   opr[op:op]   num[n:n]
   Each case prints the inferred type, or the first string of the error;
   the expected file is the output of the code as written, never typed.
   Model: a parameter of the declared kind (a level, a level variable, an
   operator, an operator variable) is accepted.
   Pinned as found: a parameter of ANOTHER kind is refused by
   tenv_find_type ("unknown term"), because a term's shape keys on its
   parameter kinds; infer_params's "param mismatch" arm is not reached
   from here. *)
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
let typeclasses =
  List.fold_left (fun tbl (o, supers) -> OpnameTable.add tbl o (OpnameSet.of_list (o :: supers)))
    OpnameTable.empty
    [ Term_ty_infer.term_opname, []; Term_ty_infer.type_opname, []; judgment_o, []; prop_o, [ Term_ty_infer.term_opname ] ]

let pterm o p = mk_term (mk_op (uop o) [ make_param p ]) []
let lev n = MLevel (mk_level n [])
let levx v = MLevel (mk_level 0 [ mk_level_var (Lm_symbol.add v) 0 ])
let oper s = Operator { opparam_name = uop s; opparam_params = []; opparam_arities = [] }
let num n = Number (Lm_num.num_of_int n)
let decl params o ty t = { ty_term = t; ty_opname = o; ty_params = params; ty_bterms = []; ty_type = ty }
let typeenv =
  OpnameTable.fold (fun env o _ -> ShapeTable.add env (shape_of_term (const o)) o) ShapeTable.empty typeclasses
let termenv =
  let classes = OpnameTable.fold (fun l o _ -> decl [] o type_c (const o) :: l) [] typeclasses in
  List.fold_left (fun env d -> ShapeTable.add env (shape_of_term d.ty_term) d) ShapeTable.empty
    (classes
     @ [ decl [ TyLevel ] (uop "univ") term_c (pterm "univ" (lev 0));
         decl [ TyOperator ] (uop "opr") term_c (pterm "opr" (oper "zero"));
         decl [ TyNumber ] (uop "num") term_c (pterm "num" (num 0)) ])
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
  Printf.printf "%-28s %s\n" name r

let infer name t = run name (fun () -> Simple_print.SimplePrint.string_of_term (Term_ty_infer.infer_term tenv t))

let () =
  infer "univ[1]" (pterm "univ" (lev 1));
  infer "univ['x]" (pterm "univ" (levx "x"));
  infer "univ[7:n] (a number)" (pterm "univ" (num 7));
  infer "opr[zero]" (pterm "opr" (oper "zero"));
  infer "opr[tt]" (pterm "opr" (oper "tt"));
  infer "opr[@o] (operator var)" (pterm "opr" (MOperator (Lm_symbol.add "o")));
  infer "opr[1] (a level)" (pterm "opr" (lev 1));
  infer "num[3]" (pterm "num" (num 3));
  infer "num[1] (a level)" (pterm "num" (lev 1))
