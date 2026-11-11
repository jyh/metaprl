(* Term_ty_infer (refiner/reflib) on POLYMORPHIC declarations: type
   variables, unification of equal types, standardizing a declaration apart
   at each use, type parameters, an existential type and a type reduction,
   which test_term_ty_infer (monomorphic declarations) leaves out.
   The environment is built as in test_term_ty_infer.  A type variable is a
   free first-order variable in a declared type.
     classes  Term, Ty, Judgment, Prop (Prop and Term)
     types    List{Ty}, Pair{Ty; Ty}, Opt{Ty}, Vec[n:n], Lab[s:s] : Ty
              (their members are Terms)
     terms    zero : Term        tt : Prop        succ{Term} : Term
              eq{Term; Term} : Judgment
              nil : List{'a}     cons{'a; List{'a}} : List{'a}
              id{'a} : 'a        pair{'a; 'b} : Pair{'a; 'b}
              fst{Pair{'a; 'b}} : 'a
              map{x: 'a. 'b; List{'a}} : List{'b}
              same{'a; 'a} : Term
              v3 : Vec[3]   v4 : Vec[4]   la : Lab["a"]   lb : Lab["b"]
              some : exists v: Ty. List{'v}
              unpack{List{'a}} : 'a      tl{List{Term}} : Term
              takes{exists v: Ty. List{'v}} : Term   (and takes2, two of them)
              none : Opt{'a}
     a type rewrite Opt{'a} <--> List{'a}, built as Filter_cache_fun builds
     one (a Strict rewrite in typereduce and the shape pair in
     typereductions)
   A type left with variables prints them as 'v1, 'v2, ... in order of
   appearance (their names are fresh symbols).  Each case prints the
   inferred type, or the first string of the RefineError it raises (and the
   message of a StringVarError); the expected file is the output of the
   code as written, never typed.  Pinned as found, not changed:
     - a type variable is fixed by the FIRST argument that mentions it, and
       later arguments are checked as its subtypes, so same{zero; tt} is a
       Term and same{tt; zero} is refused;
     - List's argument is invariant: cons{zero; cons{tt; nil}} is refused
       although a Prop is a Term;
     - an existential on the subtype side is refused against a List
       (unpack{some}, same{nil; some}, tl{some}) and accepted against an
       existential (takes{some}) or a typeclass (same{some; nil});
     - a free variable used at 'a and at List{'a} fails the occurs check;
     - a name used both as a variable and as a second-order variable
       ('x and 'x[zero] in one term) types the variable with the so-var's
       function type: cons{x; ...} is a List of ty_so_var, and succ{x} is
       ACCEPTED as a Term, the arity mismatch unreported;
     - the reduction is found by either mechanism alone: removing the
       typereduce rewrite, or the typereductions pair, leaves every line
       unchanged; only removing both changes them. *)
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
let pair_ty a b = app "Pair" [ a; b ]
let opt_ty a = app "Opt" [ a ]
let pterm o p = mk_term (mk_op (uop o) [ make_param p ]) []
let vec_ty n = pterm "Vec" (Number (Lm_num.num_of_int n))
let lab_ty s = pterm "Lab" (String s)
(* exists v: Ty. List{'v} *)
let some_ty = Term_ty_infer.mk_ty_exists_term (Lm_symbol.add "v") type_c (list_ty (mk_var_term (Lm_symbol.add "v")))

(* every typeclass term is a type in its own class; List and Pair types
   are types whose members are Terms *)
let typeenv =
  let env = OpnameTable.fold (fun env o _ -> ShapeTable.add env (shape_of_term (const o)) o) ShapeTable.empty typeclasses in
  let env = ShapeTable.add env (shape_of_term (list_ty term_c)) Term_ty_infer.term_opname in
    List.fold_left (fun env t -> ShapeTable.add env (shape_of_term t) Term_ty_infer.term_opname) env
      [ pair_ty term_c term_c; opt_ty term_c; vec_ty 0; lab_ty "" ]

let decl ?(params = []) o bterms ty t =
  { ty_term = t; ty_opname = o; ty_params = params; ty_bterms = bterms; ty_type = ty }

let bt bvars ty = { ty_bvars = bvars; ty_bterm = ty }

let zero = const (uop "zero")
let tt = const (uop "tt")
let succ t = app "succ" [ t ]
let eq a b = app "eq" [ a; b ]
let nil = const (uop "nil")
let cons a l = app "cons" [ a; l ]
let id a = app "id" [ a ]
let pair a b = app "pair" [ a; b ]
let fst p = app "fst" [ p ]
let same a b = app "same" [ a; b ]
let c0 s = const (uop s)
let unpack l = app "unpack" [ l ]
let takes l = app "takes" [ l ]
let takes2 a b = app "takes2" [ a; b ]
let tl l = app "tl" [ l ]
let so v args = TermMan.mk_so_var_term (Lm_symbol.add v) [] args
let map v body l = mk_term (mk_op (uop "map") []) [ mk_bterm [ Lm_symbol.add v ] body; mk_bterm [] l ]

let termenv =
  let classes = OpnameTable.fold (fun l o _ -> decl o [] type_c (const o) :: l) [] typeclasses in
  let a = var "a" and b = var "b" and x = var "x" in
  List.fold_left (fun env d -> ShapeTable.add env (shape_of_term d.ty_term) d) ShapeTable.empty
    (classes
     @ [ decl (uop "List") [ bt [] type_c ] type_c (list_ty x);
         decl (uop "Pair") [ bt [] type_c; bt [] type_c ] type_c (pair_ty x x);
         decl (uop "zero") [] term_c zero;
         decl (uop "tt") [] prop_c tt;
         decl (uop "succ") [ bt [] term_c ] term_c (succ zero);
         decl (uop "eq") [ bt [] term_c; bt [] term_c ] judgment_c (eq zero zero);
         decl (uop "nil") [] (list_ty a) nil;
         decl (uop "cons") [ bt [] a; bt [] (list_ty a) ] (list_ty a) (cons zero nil);
         decl (uop "id") [ bt [] a ] a (id zero);
         decl (uop "pair") [ bt [] a; bt [] b ] (pair_ty a b) (pair zero zero);
         decl (uop "fst") [ bt [] (pair_ty a b) ] a (fst zero);
         decl (uop "map") [ bt [ a ] b; bt [] (list_ty a) ] (list_ty b) (map "x" x nil);
         decl (uop "same") [ bt [] a; bt [] a ] term_c (same zero zero);
         decl (uop "Opt") [ bt [] type_c ] type_c (opt_ty x);
         decl ~params:[ TyNumber ] (uop "Vec") [] type_c (vec_ty 0);
         decl ~params:[ TyString ] (uop "Lab") [] type_c (lab_ty "");
         decl (uop "none") [] (opt_ty a) (c0 "none");
         decl (uop "v3") [] (vec_ty 3) (c0 "v3");
         decl (uop "v4") [] (vec_ty 4) (c0 "v4");
         decl (uop "la") [] (lab_ty "a") (c0 "la");
         decl (uop "lb") [] (lab_ty "b") (c0 "lb");
         decl (uop "some") [] some_ty (c0 "some");
         decl (uop "unpack") [ bt [] (list_ty a) ] a (unpack nil);
         decl (uop "takes") [ bt [] some_ty ] term_c (takes nil);
         decl (uop "tl") [ bt [] (list_ty term_c) ] term_c (tl nil);
         decl (uop "takes2") [ bt [] some_ty; bt [] some_ty ] term_c (takes2 nil nil) ])

(* the type rewrite Opt{'a} <--> List{'a}, built as the filter builds one *)
let opt_a = opt_ty (TermMan.mk_so_var_term (Lm_symbol.add "a") [] [])
let list_a = list_ty (TermMan.mk_so_var_term (Lm_symbol.add "a") [] [])
let opt_rw = Rewrite.term_rewrite Rewrite_sig.Strict Rewrite.empty_args_spec [ opt_a ] [ list_a ]

let tenv =
  { Term_ty_infer.tenv_typeclasses = typeclasses;
    tenv_typereduce = Term_match_table.add_item Term_match_table.empty_table opt_a opt_rw;
    tenv_typereductions = Term_ty_infer.Shape2Table.add Term_ty_infer.Shape2Table.empty (shape_of_term opt_a, shape_of_term list_a) (opt_a, list_a);
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

let () =
  infer "nil" nil;
  infer "cons{zero; nil}" (cons zero nil);
  infer "cons{zero; cons{zero; nil}}" (cons zero (cons zero nil));
  infer "cons{tt; nil}" (cons tt nil);
  infer "cons{zero; cons{tt; nil}}" (cons zero (cons tt nil));
  infer "cons{tt; cons{zero; nil}}" (cons tt (cons zero nil));
  infer "cons{nil; nil}" (cons nil nil);
  infer "cons{cons{zero; nil}; nil}" (cons (cons zero nil) nil);
  infer "cons{zero; zero} (no List)" (cons zero zero);
  infer "cons{nil; cons{zero; nil}}" (cons nil (cons zero nil));
  infer "cons{eq{zero; zero}; nil} (a Judgment)" (cons (eq zero zero) nil);
  infer "id{zero}" (id zero);
  infer "id{tt}" (id tt);
  infer "id{nil}" (id nil);
  infer "id{id{tt}}" (id (id tt));
  infer "succ{id{tt}}" (succ (id tt));
  infer "pair{zero; tt}" (pair zero tt);
  infer "pair{nil; nil}" (pair nil nil);
  infer "fst{pair{tt; zero}}" (fst (pair tt zero));
  infer "fst{zero} (no Pair)" (fst zero);
  infer "fst{id{pair{zero; nil}}}" (fst (id (pair zero nil)));
  infer "map{x. succ{x}; cons{zero; nil}}" (map "x" (succ (var "x")) (cons zero nil));
  infer "map{x. cons{x; nil}; cons{tt; nil}}" (map "x" (cons (var "x") nil) (cons tt nil));
  infer "map{x. x; nil}" (map "x" (var "x") nil);
  infer "map{x. eq{x; x}; cons{zero; nil}}" (map "x" (eq (var "x") (var "x")) (cons zero nil));
  infer "same{zero; zero}" (same zero zero);
  infer "same{zero; tt}" (same zero tt);
  infer "same{tt; zero}" (same tt zero);
  infer "same{nil; cons{zero; nil}}" (same nil (cons zero nil));
  infer "same{zero; nil}" (same zero nil);
  infer "same{x; x} (free x)" (same (var "x") (var "x"));
  infer "same{x; nil} (free x)" (same (var "x") nil);
  infer "cons{x; x} (free x)" (cons (var "x") (var "x"));
  (* type parameters *)
  infer "cons{v3; cons{v3; nil}}" (cons (c0 "v3") (cons (c0 "v3") nil));
  infer "cons{v3; cons{v4; nil}} (Vec[3], Vec[4])" (cons (c0 "v3") (cons (c0 "v4") nil));
  infer "cons{la; cons{la; nil}}" (cons (c0 "la") (cons (c0 "la") nil));
  infer "cons{la; cons{lb; nil}} (Lab[a], Lab[b])" (cons (c0 "la") (cons (c0 "lb") nil));
  infer "cons{v3; cons{la; nil}} (Vec, Lab)" (cons (c0 "v3") (cons (c0 "la") nil));
  infer "same{v3; v4}" (same (c0 "v3") (c0 "v4"));
  infer "same{la; lb}" (same (c0 "la") (c0 "lb"));
  (* an existential type *)
  infer "some" (c0 "some");
  infer "unpack{some}" (unpack (c0 "some"));
  infer "unpack{cons{zero; nil}}" (unpack (cons zero nil));
  infer "tl{some} (tl{List{Term}} : Term)" (tl (c0 "some"));
  infer "tl{nil}" (tl nil);
  infer "takes{nil}" (takes nil);
  infer "takes{cons{tt; nil}}" (takes (cons tt nil));
  infer "takes{some}" (takes (c0 "some"));
  infer "takes{zero} (no List)" (takes zero);
  infer "takes2{cons{zero; nil}; cons{tt; nil}}" (takes2 (cons zero nil) (cons tt nil));
  infer "takes2{cons{tt; nil}; cons{zero; nil}}" (takes2 (cons tt nil) (cons zero nil));
  infer "same{some; nil}" (same (c0 "some") nil);
  infer "same{nil; some}" (same nil (c0 "some"));
  infer "cons{some; cons{some; nil}}" (cons (c0 "some") (cons (c0 "some") nil));
  infer "cons{some; cons{nil; nil}}" (cons (c0 "some") (cons nil nil));
  (* a type reduction Opt{'a} <--> List{'a} *)
  infer "none" (c0 "none");
  infer "cons{none; cons{nil; nil}}" (cons (c0 "none") (cons nil nil));
  infer "cons{nil; cons{none; nil}}" (cons nil (cons (c0 "none") nil));
  infer "unpack{nil}" (unpack nil);
  infer "unpack{none}" (unpack (c0 "none"));
  infer "same{nil; none}" (same nil (c0 "none"));
  infer "same{none; cons{zero; nil}}" (same (c0 "none") (cons zero nil));
  infer "cons{none; cons{cons{zero; nil}; nil}}" (cons (c0 "none") (cons (cons zero nil) nil));
  infer "cons{none; cons{zero; nil}} (Opt is no Term)" (cons (c0 "none") (cons zero nil));
  (* a name used both as a variable and as a second-order variable *)
  infer "pair{same{x; y}; pair{'x[zero]; 'y[zero]}}" (pair (same (var "x") (var "y")) (pair (so "x" [ zero ]) (so "y" [ zero ])));
  infer "pair{same{x; y}; pair{'x[zero]; 'y[tt]}}" (pair (same (var "x") (var "y")) (pair (so "x" [ zero ]) (so "y" [ tt ])));
  infer "pair{same{x; y}; pair{'x[zero]; 'y[zero; zero]}}" (pair (same (var "x") (var "y")) (pair (so "x" [ zero ]) (so "y" [ zero; zero ])));
  infer "pair{cons{x; cons{y; nil}}; pair{'x[zero]; 'y[zero]}}" (pair (cons (var "x") (cons (var "y") nil)) (pair (so "x" [ zero ]) (so "y" [ zero ])));
  infer "pair{pair{'x[zero]; 'y[zero]}; same{x; y}}" (pair (pair (so "x" [ zero ]) (so "y" [ zero ])) (same (var "x") (var "y")));
  infer "pair{pair{'x[zero]; 'y[tt]}; same{x; y}}" (pair (pair (so "x" [ zero ]) (so "y" [ tt ])) (same (var "x") (var "y")));
  infer "pair{pair{'x[zero]; 'y[tt]}; cons{x; cons{y; nil}}}" (pair (pair (so "x" [ zero ]) (so "y" [ tt ])) (cons (var "x") (cons (var "y") nil)));
  infer "pair{pair{'x[zero]; 'y[zero]}; cons{x; cons{y; nil}}}" (pair (pair (so "x" [ zero ]) (so "y" [ zero ])) (cons (var "x") (cons (var "y") nil)));
  infer "pair{succ{x}; 'x[zero]}" (pair (succ (var "x")) (so "x" [ zero ]))
