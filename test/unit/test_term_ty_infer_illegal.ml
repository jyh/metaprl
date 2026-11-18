(* Term_ty_infer's guards on the types it unifies:
   unify_equal_term_types_normalized and unify_subtype_term_types_normalized
   refuse a type that is not a first-order term ("illegal type"), the
   left type first, then the right.  No case reached either refusal (the
   2026-11-15 rank: unit tests, theory build and proof census).  The
   types here are the four kinds of term that normalize_term leaves as a
   TypeTerm: a second-order variable 'a['y], a context 'H[[Term]], a
   sequent, and a term with a binding, Bnd{x. Term}.  For each kind: a
   value of the kind given to a taker of Term, and Term given to a taker
   of the kind (the subtype guard, left then right), and the same inside
   Pair{Term; _} (the equal guard: same-shape types unify their
   arguments as equal).  Each case prints the inferred type or the
   innermost error's string and the KIND of its term (a so-variable's
   argument is renamed at instantiation, and a sequent prints on three
   lines).  The expected file is the output of the code as written
   (2026-11-15), never typed.
   Not reached, and why: the is_fso_var_term disjunct (normalize_term
   turns every FO/SO-without-arguments variable into a TypeVar first),
   and the debug_infer printers.  Equivalent here: the is_so_var_term,
   is_context_term and is_sequent_term disjuncts, since in the ds terms
   (TERMS = ds, the default) not (is_fo_term t) is already true of all
   three, and in the std terms too since #362.
   The last block prints is_fo_term and its neighbours on each kind in
   both term modules: on a so-variable is_fo_term is false in std and
   in ds, also for 'a with no arguments, which both call an FO variable
   (is_fso_var_term).  When this test was written std said true; #362
   (term_std: is_fo_term is false for a second-order variable, as in
   term_ds) made the two agree, and this expected file is master's
   output since then (the CI Build run 44256070163, both legs).  The
   guards above are its only callers. *)
open Lm_symbol
open Opname
open Term_sig
open Term_ty_sig
open Refiner.Refiner
open TermType
open Term
open TermMan
open TermShape
open RefineError

let perv = mk_opname "Perv" nil_opname
let pop s = mk_opname s perv
let uop s = make_opname [ s; "Test" ]
let const o = mk_term (mk_op o []) []
let app o ts = mk_term (mk_op (uop o) []) (List.map (fun t -> mk_bterm [] t) ts)

let term_c = Term_ty_infer.term_type
let type_c = Term_ty_infer.type_type
let judgment_o = pop "Judgment"

let typeclasses =
  List.fold_left (fun tbl (o, supers) -> OpnameTable.add tbl o (OpnameSet.of_list (o :: supers)))
    OpnameTable.empty
    [ Term_ty_infer.term_opname, []; Term_ty_infer.type_opname, []; judgment_o, [] ]

let sym = Lm_symbol.add
let var v = mk_var_term (sym v)
let pair_ty a b = app "Pair" [ a; b ]

(* the four kinds of term that normalize_term leaves as a TypeTerm and the guard refuses *)
let so_k = mk_so_var_term (sym "a") [] [ var "y" ]
let ctx_k = mk_context_term (sym "H") term_c [] []
let seq_k = mk_sequent_term { sequent_args = const (uop "sargs"); sequent_hyps = SeqHyp.of_list []; sequent_concl = term_c }
let bnd_k = mk_term (mk_op (uop "Bnd") []) [ mk_bterm [ sym "x" ] term_c ]
let kinds = [ "so", so_k; "ctx", ctx_k; "seq", seq_k; "bnd", bnd_k ]

let typeenv =
  let env = OpnameTable.fold (fun env o _ -> ShapeTable.add env (shape_of_term (const o)) o) ShapeTable.empty typeclasses in
    ShapeTable.add env (shape_of_term (pair_ty term_c term_c)) Term_ty_infer.term_opname

let decl o bterms ty t = { ty_term = t; ty_opname = o; ty_params = []; ty_bterms = bterms; ty_type = ty }
let bt ty = { ty_bvars = []; ty_bterm = ty }
let c0 s = const (uop s)
let tk n x = app n [ x ]
let zero = c0 "zero"

let termenv =
  let classes = OpnameTable.fold (fun l o _ -> decl o [] type_c (const o) :: l) [] typeclasses in
  let x = var "x" in
  let per (k, ty) =
    [ decl (uop ("v" ^ k)) [] ty (c0 ("v" ^ k));                                  (* a value of the kind *)
      decl (uop ("tk" ^ k)) [ bt ty ] term_c (tk ("tk" ^ k) zero);                 (* a taker of the kind *)
      decl (uop ("pv" ^ k)) [] (pair_ty term_c ty) (c0 ("pv" ^ k));                (* Pair{Term; kind} *)
      decl (uop ("ptk" ^ k)) [ bt (pair_ty term_c ty) ] term_c (tk ("ptk" ^ k) zero) ]
  in
  List.fold_left (fun env d -> ShapeTable.add env (shape_of_term d.ty_term) d) ShapeTable.empty
    (classes
     @ [ decl (uop "Pair") [ bt type_c; bt type_c ] type_c (pair_ty x x);
         decl (uop "zero") [] term_c zero;
         decl (uop "pt") [] (pair_ty term_c term_c) (c0 "pt");
         decl (uop "tkt") [ bt term_c ] term_c (tk "tkt" zero);
         decl (uop "ptkt") [ bt (pair_ty term_c term_c) ] term_c (tk "ptkt" zero) ]
     @ List.concat_map per kinds)

let tenv =
  { Term_ty_infer.tenv_typeclasses = typeclasses;
    tenv_typereduce = Term_match_table.empty_table;
    tenv_typereductions = Term_ty_infer.Shape2Table.empty;
    tenv_typeenv = typeenv;
    tenv_termenv = termenv }

(* The kind of a term, never its text: a so-variable's argument is renamed
   when the declaration is instantiated, and a sequent prints on 3 lines. *)
let kind t =
  if is_so_var_term t then "so-var"
  else if is_context_term t then "context"
  else if is_sequent_term t then "sequent"
  else if not (is_fo_term t) then "binding"
  else Simple_print.SimplePrint.string_of_term t

(* The innermost error: its last string and the kind of its term. *)
let rec last s = function
  | StringErrorError (s, e) -> last s e
  | TermErrorError (_, e) -> last s e
  | TermError t -> s ^ " " ^ kind t
  | StringError s -> s
  | _ -> s ^ " (other)"

let run name f =
  let r =
    try f () with
    | RefineError (s, e) -> "REFUSED: " ^ s ^ ": " ^ last "" e
    | Failure s -> "FAILURE: " ^ s
    | Invalid_argument s -> "INVALID_ARGUMENT: " ^ s
    | Not_found -> "NOT_FOUND"
  in
  Printf.printf "%-14s %s\n" name r

let infer name t = run name (fun () -> Simple_print.SimplePrint.string_of_term (Term_ty_infer.infer_term tenv t))

let () =
  infer "ptkt{pt}" (app "ptkt" [ c0 "pt" ]);
  List.iter (fun (k, _) ->
      infer ("tkt{v" ^ k ^ "}") (app "tkt" [ c0 ("v" ^ k) ]);
      infer ("tk" ^ k ^ "{zero}") (app ("tk" ^ k) [ zero ]);
      infer ("ptkt{pv" ^ k ^ "}") (app "ptkt" [ c0 ("pv" ^ k) ]);
      infer ("ptk" ^ k ^ "{pt}") (app ("ptk" ^ k) [ c0 "pt" ]))
    kinds

(* is_fo_term and the kind tests in both term implementations. *)
module Kinds (R : Refiner_sig.RefinerSig) = struct
  open R.Term
  open R.TermMan
  open R.TermType
  let c = mk_term (mk_op (uop "c") []) []
  let show name =
    let so = mk_so_var_term (sym "a") [] [ mk_var_term (sym "y") ] in
    let so0 = mk_so_var_term (sym "a") [] [] in
    let ctx = mk_context_term (sym "H") c [] [] in
    let seq = mk_sequent_term { sequent_args = c; sequent_hyps = SeqHyp.of_list []; sequent_concl = c } in
    let bnd = mk_term (mk_op (uop "Bnd") []) [ mk_bterm [ sym "x" ] c ] in
      List.iter (fun (k, t) ->
          Printf.printf "%-3s %-4s fso=%b fo=%b so=%b ctx=%b seq=%b\n" name k
            (is_fso_var_term t) (is_fo_term t) (is_so_var_term t) (is_context_term t) (is_sequent_term t))
        [ "so", so; "so0", so0; "ctx", ctx; "seq", seq; "bnd", bnd ]
end

let () =
  let module S = Kinds (Refiner_std.Refiner) in
  let module D = Kinds (Refiner_ds.Refiner) in
    S.show "std";
    D.show "ds"
