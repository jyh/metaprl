(* unit-link: filter *)
(* Filter_cache_fun.expand_path and expand_in_summary (the module-path
   lookup behind a qualified name such as Fce.a), and string_of_op_shape's
   parameter and arity printing, which no unit test, theory build or proof
   census reached (2026-11-18 rank737; row 727's test_filter_cache_opname
   stated expand_path unreached for want of an inlined module).  An
   interface fce is saved with a typeclass K, a type T and a term a, each
   both declared and added as an item (inlining reads the items), and is
   inlined into a fresh implementation fcm.  Each line prints the path or
   opname found, or the exception.  Read from the output: before inlining
   nothing expands; after it, [Fce; a], [Fce; T] and [Fce; K] are found by
   the head-module search, and [a] by the search through every opened
   module, giving [Fce; a].  An undeclared name with each parameter kind
   prints the shape in the refusal; a leading quote is dropped.
   Not reached, stated: a nested module (a Module item); no theory has
   one (CHANGES.md, Known not to work).
   The expected file is the output of the code as written (2026-11-18),
   never typed.  Mutants (2026-11-18, each rebuilt and relinked; an
   identity control unchanged): the head search never matching, the
   search through opened modules off, expand_in_summary's name test
   negated, S and N swapped, Q printed as Op, the leading quote kept:
   6 of 6 RED.  The module files are removed at the start and the end
   (the unit tests share one directory). *)
open File_base_type
open Filter_type
open Refiner.Refiner.Term

module C = Filter_cache.MakeCaches (Proof_convert.Convert)
module S = C.StrFilterCache
module SC = C.SigFilterCache

let op s = Opname.make_opname [ s; "Fce" ]
let t s = mk_simple_term (op s) []
let ty term ty = { Term_ty_sig.ty_term = term; ty_opname = Refiner.Refiner.Term.opname_of_term term; ty_params = []; ty_bterms = []; ty_type = ty }
let files = [ "fce.cmiz"; "fce.cmiz.new"; "fce.prla"; "fce.prla.new" ]
let clean () = List.iter (fun f -> try Sys.remove f with Sys_error _ -> ()) files
let rec ex = function Ploc.Exc (_, e) -> ex e | Failure m -> "Failure " ^ m | Invalid_argument m -> "Invalid_argument " ^ m | e -> Printexc.to_string e
let look info lbl kind names params arities =
  let ps = S.get_parsing_state info in
  Printf.printf "%-40s %s\n%!" lbl
    (try "opname " ^ Opname.string_of_opname (ps.mk_opname_kind Ploc.dummy kind names params arities) with e -> ex e)
let path info lbl p =
  Printf.printf "%-40s %s\n%!" lbl (try "[" ^ String.concat "; " (S.expand_path info p) ^ "]" with e -> ex e)

let () =
  clean ();
  (* the interface fce: typeclass K, type T, term a : T *)
  (try
     let si = SC.create_cache (SC.create [ "." ]) "fce" InterfaceType in
     SC.set_mode si InteractiveSummary;
     SC.declare_typeclass si Filter_shape.shape_normal (op "K") Term_ty_infer.type_opname ParentNone;
     SC.declare_type si Filter_shape.shape_normal (ty (t "T") (t "K")) (op "K");
     SC.declare_term si Filter_shape.shape_normal (ty (t "a") (t "T"));
     let sh = Filter_shape.shape_normal in
     SC.add_command si (DeclareTypeClass (sh, op "K", Term_ty_infer.type_opname, ParentNone), Ploc.dummy);
     SC.add_command si (DeclareType (sh, ty (t "T") (t "K"), op "K"), Ploc.dummy);
     SC.add_command si (DeclareTerm (sh, ty (t "a") (t "T")), Ploc.dummy);
     SC.save si () (OnlySuffixes [ "cmiz" ]);
     print_endline "interface fce saved"
   with e -> print_endline ("interface save raised " ^ ex e));
  let info = S.create_cache (S.create [ "." ]) "fcm" ImplementationType in
  S.set_mode info InteractiveSummary;
  print_endline "== before inlining";
  path info "expand_path [Fce; a]" [ "Fce"; "a" ];
  (try S.inline_module info () [ "fce" ]; print_endline "inlined fce" with e -> print_endline ("inline raised " ^ ex e));
  print_endline "== after inlining fce";
  path info "expand_path [Fce; a]" [ "Fce"; "a" ];
  path info "expand_path [Fce; T]" [ "Fce"; "T" ];
  path info "expand_path [Fce; K]" [ "Fce"; "K" ];
  path info "expand_path [Fce; zz]" [ "Fce"; "zz" ];
  path info "expand_path [a]" [ "a" ];
  path info "expand_path [Other; a]" [ "Other"; "a" ];
  path info "expand_path []" [];
  look info "mk_opname [a]" NormalKind [ "a" ] [] [];
  look info "mk_opname [Fce; a]" NormalKind [ "Fce"; "a" ] [] [];
  look info "mk_opname [Fce; zz]" NormalKind [ "Fce"; "zz" ] [] [];
  look info "mk_opname [Other; a]" NormalKind [ "Other"; "a" ] [] [];
  print_endline "== an undeclared name, each parameter kind and arities";
  look info "zz [S; N; V; L; T; Sh; Op; Q] {0; 2}" NormalKind [ "zz" ]
    [ ShapeString; ShapeNumber; ShapeVar; ShapeLevel; ShapeToken; ShapeShape; ShapeOperator; ShapeQuote ] [ 0; 2 ];
  look info "zz [Q; S] (a leading quote dropped)" NormalKind [ "zz" ] [ ShapeQuote; ShapeString ] [ 1 ];
  look info "zz [N] as a token" TokenKind [ "zz" ] [ ShapeNumber ] [];
  clean ()
