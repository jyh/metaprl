(* unit-link: filter *)
(* Every kind of summary item a theory module holds, saved and loaded:
   once as terms (.prla, Filter_summary's term encoding and its decoders,
   dest_term_aux) and once raw (.prlb, Filter_cache.set_raw, which converts
   with Filter_summary.summary_map / item_map).  item_map's arms for these
   kinds were reached by nothing (2026-11-18 rank737; row 733's
   test_filter_cache_raw holds rewrites, a rule and a precedence only).
   The module fci holds a typeclass and two types (DefineTerm and
   DeclareTypeRewrite are checked against them on load), a conditional
   rewrite, an input form, a comment, a type rewrite, a definition, two
   display forms (a term and none), an ML rewrite and an ML axiom, a
   precedence relation, an Id, an improve, an infix, a summary item, a
   toploop item and a magic block.  Each loaded item is printed; an item
   not saved would be marked NEW, a saved one not loaded LOST.  Read from
   the output: all 19 come back equal in both formats.
   Not reached, stated: Resource, Parent and Module (a parent or nested
   module needs another saved module; no theory has a nested one), and
   MLDForm.  The expected file is the output of the code as written
   (2026-11-18), never typed.
   Mutants (2026-11-18, each rebuilt and relinked; an identity control
   unchanged): the decoders' InputForm swap, conditional-rewrite
   assumptions dropped and magic block reversed, and item_map's
   assumptions dropped: 4 RED.  item_map's InputForm swap and magic-block
   reversal SURVIVE, declared: item_map runs on the save and again on the
   load, so a mutant that is its own inverse cancels over the round trip
   (as in test_filter_cache_raw).  The module files are removed at the
   start and the end (the unit tests share one directory). *)
open File_base_type
open Filter_type
open Filter_summary_type
open Refiner.Refiner.Term

module C = Filter_cache.MakeCaches (Proof_convert.Convert)
module S = C.StrFilterCache

let loc = Ploc.dummy
let op s = Opname.make_opname [ s; "Fci" ]
let t s = mk_simple_term (op s) []
let sp = Simple_print.SimplePrint.string_of_term
let no_res = { item_bindings = []; item_item = [] }
let ty term ty = { Term_ty_sig.ty_term = term; ty_opname = opname_of_term term; ty_params = []; ty_bterms = []; ty_type = ty }
let e name = MLast.ExLid (loc, Ploc.VaVal name)
let st name = MLast.StExp (loc, e name, Ploc.VaVal [])
let bnd x = { item_bindings = []; item_item = x }
let files = [ "fci.prlb"; "fci.prla"; "fci.cmiz"; "fci.prlbi"; "fci.prlai"; "fci.prlb.new"; "fci.prla.new"; "fci.cmiz.new" ]
let clean () = List.iter (fun f -> try Sys.remove f with Sys_error _ -> ()) files

let items = [
  DeclareTypeClass (Filter_shape.shape_normal, op "K", Term_ty_infer.type_opname, ParentNone);
  DeclareType (Filter_shape.shape_normal, ty (t "T") (t "K"), op "K");
  DeclareType (Filter_shape.shape_normal, ty (t "U") (t "K"), op "K");
  CondRewrite { crw_name = "cr"; crw_params = []; crw_assums = [ t "ca" ]; crw_redex = t "crr"; crw_contractum = t "crc"; crw_proof = Incomplete; crw_resources = no_res };
  InputForm { iform_name = "ifm"; iform_redex = t "ifr"; iform_contractum = t "ifc" };
  Comment (t "cm");
  DeclareTypeRewrite (t "U", t "T");
  DefineTerm (Filter_shape.shape_normal, ty (t "dt") (t "T"), { term_def_name = "dt"; term_def_value = t "dv"; term_def_resources = no_res; term_def_opaque = false });
  DForm { dform_name = "dft"; dform_modes = Dform.AllModes; dform_options = [ DFormParens ]; dform_redex = t "dfr"; dform_def = TermDForm (t "dfd") };
  DForm { dform_name = "dfn"; dform_modes = Dform.PrimitiveModes; dform_options = [ DFormPrec "p" ]; dform_redex = t "dfn"; dform_def = NoDForm };
  MLRewrite { mlterm_name = "mr"; mlterm_params = []; mlterm_term = t "mrt"; mlterm_def = Some (bnd (e "mrdef")); mlterm_resources = no_res };
  MLAxiom { mlterm_name = "ma"; mlterm_params = []; mlterm_term = t "mat"; mlterm_def = None; mlterm_resources = no_res };
  PrecRel { prec_rel = Precedence.LTRelation; prec_left = "pl"; prec_right = "pr" };
  Id 7;
  Improve { improve_name = "im"; improve_flag = Mp_resource.Public; improve_expr = bnd (e "imx") };
  MLGramUpd (Infix "+++");
  SummaryItem (bnd (st "si"));
  ToploopItem (st "ti");
  MagicBlock { magic_name = "mb"; magic_code = [ st "mb1"; st "mb2" ] };
]

let ex = function MLast.ExLid (_, Ploc.VaVal s) -> s | _ -> "(expr)"
let sx = function MLast.StExp (_, x, _) -> ex x | _ -> "(str_item)"
let describe = function
  | CondRewrite c -> Printf.sprintf "CondRewrite %s: %s => %s --> %s" c.crw_name (String.concat "," (List.map sp c.crw_assums)) (sp c.crw_redex) (sp c.crw_contractum)
  | InputForm i -> Printf.sprintf "InputForm %s: %s <--> %s" i.iform_name (sp i.iform_redex) (sp i.iform_contractum)
  | Comment c -> "Comment " ^ sp c
  | DeclareTypeRewrite (a, b) -> Printf.sprintf "DeclareTypeRewrite %s --> %s" (sp a) (sp b)
  | DefineTerm (_, ty, d) -> Printf.sprintf "DefineTerm %s : %s = %s (opaque %b)" (sp ty.Term_ty_sig.ty_term) (sp ty.Term_ty_sig.ty_type) (sp d.term_def_value) d.term_def_opaque
  | DForm d -> Printf.sprintf "DForm %s: %s %s%s" d.dform_name (sp d.dform_redex)
                 (match d.dform_def with NoDForm -> "no-def" | TermDForm x -> "= " ^ sp x | MLDForm _ -> "ml")
                 (String.concat "" (List.map (function DFormParens -> " parens" | DFormPrec p -> " prec " ^ p | DFormInheritPrec -> " inherit") d.dform_options))
  | MLRewrite m -> Printf.sprintf "MLRewrite %s: %s def %s" m.mlterm_name (sp m.mlterm_term) (match m.mlterm_def with Some b -> ex b.item_item | None -> "-")
  | MLAxiom m -> Printf.sprintf "MLAxiom %s: %s def %s" m.mlterm_name (sp m.mlterm_term) (match m.mlterm_def with Some b -> ex b.item_item | None -> "-")
  | PrecRel p -> Printf.sprintf "PrecRel %s %s %s" p.prec_left (match p.prec_rel with Precedence.LTRelation -> "<" | Precedence.EQRelation -> "=" | Precedence.GTRelation -> ">" | Precedence.NoRelation -> "?") p.prec_right
  | Id n -> "Id " ^ string_of_int n
  | Improve i -> Printf.sprintf "Improve %s %s: %s" i.improve_name (match i.improve_flag with Mp_resource.Public -> "public" | Mp_resource.Private -> "private") (ex i.improve_expr.item_item)
  | MLGramUpd (Infix s) -> "MLGramUpd Infix " ^ s
  | MLGramUpd (Suffix s) -> "MLGramUpd Suffix " ^ s
  | SummaryItem b -> "SummaryItem " ^ sx b.item_item
  | ToploopItem i -> "ToploopItem " ^ sx i
  | MagicBlock m -> Printf.sprintf "MagicBlock %s: %s" m.magic_name (String.concat "; " (List.map sx m.magic_code))
  | Rewrite _ -> "Rewrite" | Rule _ -> "Rule" | Parent _ -> "Parent" | Module _ -> "Module" | Prec p -> "Prec " ^ p
  | Resource (n, _) -> "Resource " ^ n | PRLGrammar _ -> "PRLGrammar" | DeclareTypeClass (_, o, _, _) -> "DeclareTypeClass " ^ Opname.string_of_opname o
  | DeclareType (_, ty, o) -> Printf.sprintf "DeclareType %s : %s" (sp ty.Term_ty_sig.ty_term) (Opname.string_of_opname o) | DeclareTerm _ -> "DeclareTerm"

let run suffix =
  Printf.printf "== saved and loaded as %s\n%!" suffix;
  clean ();
  let info = S.create_cache (S.create [ "." ]) "fci" ImplementationType in
  S.set_mode info InteractiveSummary;
  List.iter (fun i -> try S.add_command info (i, loc) with e -> Printf.printf "add_command %s raised %s\n" (describe i) (Printexc.to_string e)) items;
  (try S.save info () (OnlySuffixes [ suffix ]); print_endline "saved" with e -> print_endline ("save raised " ^ Printexc.to_string e));
  (try
     let module SC = C.SigFilterCache in
     let sinfo = SC.create_cache (SC.create [ "." ]) "fci" InterfaceType in
     SC.save sinfo () (OnlySuffixes [ suffix ^ "i"; "cmiz" ]); print_endline "interface saved"
   with e -> print_endline ("interface save raised " ^ Printexc.to_string e));
  (match S.load (S.create [ "." ]) () "fci" ImplementationType (OnlySuffixes [ suffix ]) with
   | info2 ->
      let got = List.map (fun (i, _) -> describe i) (Filter_summary.info_items (S.info info2)) in
      let want = List.map describe items in
      List.iter (fun d -> Printf.printf "  %s %s\n" (if List.mem d want then "  " else "NEW") d) got;
      List.iter (fun d -> if not (List.mem d got) then Printf.printf "  LOST %s\n" d) want
   | exception e -> print_endline ("load raised " ^ Printexc.to_string e));
  clean ()

let () =
  run "prla";
  Filter_cache.set_raw ();
  run "prlb"
