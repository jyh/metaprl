(* Term_ty_infer's unify_equal_params on the parameter kinds that
   test_term_ty_infer_poly leaves out: Quote, MLevel, Shape and MShape, and
   the Nuprl5 ObId and ParamList.  A parameter of a TYPE is compared when
   two types of the same shape are unified (same{'a; 'a}, and List's
   element in cons{'a; List{'a}}).  The environment is
   test_term_ty_infer_poly's classes and List, with
     types    Q[@] (a Quote parameter), Lv[l:l], Sh[sh], Ob[obid] and
              Pl[paramlist] : Ty, whose members are Terms
     terms    nil : List{'a}   cons{'a; List{'a}} : List{'a}
              same{'a; 'a} : Term     zero : Term     tt : Prop
              q : Q[@]   l0, l1 : Lv[0], Lv[1]   lx : Lv['x]
              s0, s1 : Sh[zero], Sh[tt]   sm : Sh[@s]
              o1 : Ob[1]   p1 : Pl[1]
   Ob and Pl are not in the type environment: shape_of_term refuses their
   parameters, so the environment cannot be built with them.  Each case
   prints the inferred type, or the first string of the error raised; the
   expected file is the output of the code as written, never typed.
   Pinned as found, not changed:
     - a Quote parameter equals a Quote parameter;
     - a level parameter equals ANY level parameter: Lv[0] and Lv[1] are
       one type, and so are Lv[0] and Lv['x];
     - a type with a Shape or MShape parameter is not equal to ITSELF:
       same{s0; s0} and cons{s0; cons{s0; nil}} are refused, because
       unify_equal_params has no Shape, MShape, Operator or MOperator arm;
     - a type with an ObId or ParamList parameter raises Invalid_argument
       "Term.shape_of_term" (not a RefineError), from shape_of_term before
       unify_equal_params is called, so the ObId and ParamList arms of
       unify_equal_params are not reached (its only caller is
       unify_equal_param_lists, called on a shape's parameters and from the
       ParamList arm itself).
   Not reached: those two arms, and an Operator parameter (same case as
   Shape: no arm). *)
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
let judgment_c = const judgment_o

let typeclasses =
  List.fold_left (fun tbl (o, supers) -> OpnameTable.add tbl o (OpnameSet.of_list (o :: supers)))
    OpnameTable.empty
    [ Term_ty_infer.term_opname, []; Term_ty_infer.type_opname, []; judgment_o, []; prop_o, [ Term_ty_infer.term_opname ] ]

let var v = mk_var_term (Lm_symbol.add v)
let list_ty a = app "List" [ a ]

let pterm o p = mk_term (mk_op (uop o) [ make_param p ]) []
let q_ty = pterm "Q" Quote
let lv_ty n = pterm "Lv" (MLevel (mk_level n []))
let lvx_ty v = pterm "Lv" (MLevel (mk_level 0 [ mk_level_var (Lm_symbol.add v) 0 ]))
let sh_ty t = pterm "Sh" (Shape (shape_of_term t))
let msh_ty v = pterm "Sh" (MShape (Lm_symbol.add v))
let ob_ty n = pterm "Ob" (ObId [ make_param (Number (Lm_num.num_of_int n)) ])
let pl_ty n = pterm "Pl" (ParamList [ make_param (Number (Lm_num.num_of_int n)) ])
let decl ?(params = []) o bterms ty t =
  { ty_term = t; ty_opname = o; ty_params = params; ty_bterms = bterms; ty_type = ty }
let bt bvars ty = { ty_bvars = bvars; ty_bterm = ty }
let zero = const (uop "zero")
let tt = const (uop "tt")
let nil = const (uop "nil")
let cons a l = app "cons" [ a; l ]
let same a b = app "same" [ a; b ]
let c0 s = const (uop s)
let typeenv =
  let env = OpnameTable.fold (fun env o _ -> ShapeTable.add env (shape_of_term (const o)) o) ShapeTable.empty typeclasses in
  let env = ShapeTable.add env (shape_of_term (list_ty term_c)) Term_ty_infer.term_opname in
    List.fold_left (fun env t -> ShapeTable.add env (shape_of_term t) Term_ty_infer.term_opname) env
      [ q_ty; lv_ty 0; sh_ty zero ]
let termenv =
  let classes = OpnameTable.fold (fun l o _ -> decl o [] type_c (const o) :: l) [] typeclasses in
  let a = var "a" and x = var "x" in
  List.fold_left (fun env d -> ShapeTable.add env (shape_of_term d.ty_term) d) ShapeTable.empty
    (classes
     @ [ decl (uop "List") [ bt [] type_c ] type_c (list_ty x);
         decl (uop "zero") [] term_c zero;
         decl (uop "tt") [] prop_c tt;
         decl (uop "nil") [] (list_ty a) nil;
         decl (uop "cons") [ bt [] a; bt [] (list_ty a) ] (list_ty a) (cons zero nil);
         decl (uop "same") [ bt [] a; bt [] a ] term_c (same zero zero);
         decl (uop "q") [] q_ty (c0 "q");
         decl (uop "l0") [] (lv_ty 0) (c0 "l0");
         decl (uop "l1") [] (lv_ty 1) (c0 "l1");
         decl (uop "lx") [] (lvx_ty "x") (c0 "lx");
         decl (uop "s0") [] (sh_ty zero) (c0 "s0");
         decl (uop "s1") [] (sh_ty tt) (c0 "s1");
         decl (uop "sm") [] (msh_ty "s") (c0 "sm");
         decl (uop "o1") [] (ob_ty 1) (c0 "o1");
         decl (uop "p1") [] (pl_ty 1) (c0 "p1") ])
let tenv =
  { Term_ty_infer.tenv_typeclasses = typeclasses;
    tenv_typereduce = Term_match_table.empty_table;
    tenv_typereductions = Term_ty_infer.Shape2Table.empty;
    tenv_typeenv = typeenv;
    tenv_termenv = termenv }
(* Print a type with its free variables renamed 'v1, 'v2, ... in order of
   first appearance in the printed text. *)
let show_ty t =
  let s = Simple_print.SimplePrint.string_of_term t in
  let fv = List.map Lm_symbol.string_of_symbol (SymbolSet.to_list (Refiner.Refiner.TermSubst.free_vars_set t)) in
  let pos n = let k = "'" ^ n in
    let rec f i = if i + String.length k > String.length s then max_int
      else if String.sub s i (String.length k) = k then i else f (i + 1) in f 0 in
  let fv = List.sort (fun a b -> Stdlib.compare (pos a, String.length b) (pos b, String.length a)) fv in
  let fv = List.filter (fun n -> pos n <> max_int) fv in
  let names = List.mapi (fun i n -> n, Printf.sprintf "'v%d" (i + 1)) fv in
  (* replace longest names first so a name that is a prefix of another is safe *)
  let names = List.sort (fun (a, _) (b, _) -> Stdlib.compare (String.length b) (String.length a)) names in
  let replace s (n, r) =
    let k = "'" ^ n and b = Buffer.create (String.length s) in
    let rec go i =
      if i >= String.length s then ()
      else if i + String.length k <= String.length s && String.sub s i (String.length k) = k then (Buffer.add_string b r; go (i + String.length k))
      else (Buffer.add_char b s.[i]; go (i + 1))
    in
      go 0; Buffer.contents b
  in
  List.fold_left replace s names

let run name f =
  let r =
    try f () with
    | RefineError (s, StringVarError (m, _)) -> "REFUSED: " ^ s ^ " (" ^ m ^ ")"
    | RefineError (s, _) -> "REFUSED: " ^ s
    | Failure s -> "FAILURE: " ^ s
    | Invalid_argument s -> "INVALID_ARGUMENT: " ^ s
    | Not_found -> "NOT_FOUND"
  in
  Printf.printf "%-52s %s\n" name r

let infer name t = run name (fun () -> show_ty (Term_ty_infer.infer_term tenv t))


let infer name t = run name (fun () -> show_ty (Term_ty_infer.infer_term tenv t))
let () =
  let pairs = [ "q","q"; "l0","l0"; "l0","l1"; "l1","l0"; "l0","lx"; "lx","lx"; "s0","s0"; "s0","s1"; "s0","sm"; "sm","s0"; "sm","sm"; "q","l0"; "o1","o1"; "p1","p1" ] in
  List.iter (fun (a, b) -> infer (Printf.sprintf "same{%s; %s}" a b) (same (c0 a) (c0 b))) pairs;
  List.iter (fun a -> infer (Printf.sprintf "cons{%s; cons{%s; nil}}" a a) (cons (c0 a) (cons (c0 a) nil))) [ "q"; "l0"; "s0"; "sm"; "o1"; "p1" ];
  List.iter (fun a -> infer a (c0 a)) [ "q"; "l0"; "lx"; "s0"; "sm"; "o1"; "p1" ]
