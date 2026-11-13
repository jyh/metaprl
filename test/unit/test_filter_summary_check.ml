(* unit-link: filter *)
(*
 * Filter_summary's check_implementation: every item of an interface
 * must be implemented, with the same statement, or the filter refuses
 * the implementation with IterfImplemMismatch.  A few interface items
 * need no implementation and are passed on to it instead (an input form,
 * a declaration, an id).
 *
 * Each case is one interface item against an implementation, and prints
 * what check_implementation returns (the kinds of the items it passes
 * on) or the mismatch it raises.
 *
 * On a bisect build at 008a9607e the theory build and the proof census
 * reach none of the mismatch messages: every theory's interface and
 * implementation agree.
 *
 * The expected file is the output of the code.
 *)
open Term_sig
open Opname
open Filter_base_type
open Filter_type
open Filter_summary_type
open Refiner.Refiner
open TermType
open Term

module S = Filter_summary
module T = Filter_summary.FilterSummaryTerm (Refiner.Refiner)

let op s = mk_opname s nil_opname
let c s = mk_simple_term (op s) []
let f s l = mk_simple_term (op s) l
let sym = Lm_symbol.add

let loc = Ploc.dummy
let bnd item = { item_bindings = []; item_item = item }
let no_res = bnd []
let ty t = { Term_ty_sig.ty_term = t; ty_opname = op "tyop"; ty_params = []; ty_bterms = []; ty_type = c "ty" }
let normal = Filter_shape.shape_normal
let iform = Filter_shape.shape_iform

let kind = function
   Rewrite _ -> "Rewrite" | CondRewrite _ -> "CondRewrite" | Rule _ -> "Rule" | MLRewrite _ -> "MLRewrite"
 | MLAxiom _ -> "MLAxiom" | Parent _ -> "Parent" | Module _ -> "Module" | DForm _ -> "DForm" | Prec _ -> "Prec"
 | PrecRel _ -> "PrecRel" | Id _ -> "Id" | Resource _ -> "Resource" | Improve _ -> "Improve"
 | MLGramUpd _ -> "MLGramUpd" | SummaryItem _ -> "SummaryItem" | ToploopItem _ -> "ToploopItem"
 | MagicBlock _ -> "MagicBlock" | Comment _ -> "Comment" | InputForm _ -> "InputForm" | PRLGrammar _ -> "PRLGrammar"
 | DeclareTypeClass _ -> "DeclareTypeClass" | DeclareType _ -> "DeclareType" | DeclareTerm _ -> "DeclareTerm"
 | DefineTerm _ -> "DefineTerm" | DeclareTypeRewrite _ -> "DeclareTypeRewrite"

let info items = List.fold_left (fun info item -> S.add_command info (item, loc)) (S.new_module_info ()) items

let one_line s = String.concat " / " (List.filter (( <> ) "") (String.split_on_char '\n' s))

let check name interf implem =
   let result =
      match T.check_implementation (info implem) (info [interf]) with
         items -> "ok, passed on [" ^ String.concat "; " (List.map (fun (it, _) -> kind it) items) ^ "]"
       | exception Ploc.Exc (_, IterfImplemMismatch s) -> "mismatch: " ^ one_line s
       | exception e -> "raised " ^ Printexc.to_string e
   in
      Printf.printf "  %-34s %s\n" name result

let rw name r c' = Rewrite { rw_name = name; rw_redex = r; rw_contractum = c'; rw_proof = c "pf"; rw_resources = no_res }
let def ?(opaque = false) sc name t v =
   DefineTerm (sc, ty t, { term_def_name = name; term_def_value = v; term_def_resources = no_res; term_def_opaque = opaque })
let crw ?(params = [IntParam (sym "i")]) ?(assums = [c "a1"]) ?(redex = c "cr") name =
   CondRewrite { crw_name = name; crw_params = params; crw_assums = assums; crw_redex = redex;
                 crw_contractum = c "cc"; crw_proof = c "pf"; crw_resources = no_res }
let rule ?(params = [TermParam (c "tp")]) ?(stmt = MetaTheorem (c "goal")) name =
   Rule { rule_name = name; rule_params = params; rule_stmt = stmt; rule_proof = c "pf"; rule_resources = no_res }
let ifm r c' = InputForm { iform_name = "if"; iform_redex = r; iform_contractum = c' }
let ml name t = { mlterm_name = name; mlterm_params = []; mlterm_term = t; mlterm_def = None; mlterm_resources = no_res }
let dform opts r = DForm { dform_name = "df"; dform_modes = AllModes; dform_options = opts; dform_redex = r; dform_def = NoDForm }
let parent p = Parent { parent_name = p; parent_resources = [] }

let () =
   print_endline "Rewrite:";
   let i = rw "r" (c "x") (c "y") in
      check "implemented" i [rw "r" (c "x") (c "y")];
      check "missing" i [rw "other" (c "x") (c "y")];
      check "redex differs" i [rw "r" (c "x2") (c "y")];
      check "contractum differs" i [rw "r" (c "x") (c "y2")];
      check "by a definition" i [def normal "r" (c "x") (c "y")];
      check "by an opaque definition" i [def ~opaque:true normal "r" (c "x") (c "y")];
      check "by an iform definition" i [def iform "r" (c "x") (c "y")];
   print_endline "InputForm:";
   let i = ifm (c "ir") (c "ic") in
      check "implemented" i [ifm (c "ir") (c "ic")];
      check "missing (passed on)" i [];
      check "redex differs" i [ifm (c "ir2") (c "ic")];
      check "contractum differs" i [ifm (c "ir") (c "ic2")];
      check "by an iform definition" i [def iform "if" (c "ir") (c "ic")];
   print_endline "CondRewrite:";
   let i = crw "crw" in
      check "implemented" i [crw "crw"];
      check "missing" i [];
      check "a parameter's kind differs" i [crw ~params:[AddrParam (sym "i")] "crw"];
      check "a parameter's kind differs (2)" (crw ~params:[AddrParam (sym "i")] "crw") [crw "crw"];
      check "one parameter more" i [crw ~params:[IntParam (sym "i"); IntParam (sym "j")] "crw"];
      check "one assumption more" i [crw ~assums:[c "a1"; c "a2"] "crw"];
      check "an assumption differs" i [crw ~assums:[c "a9"] "crw"];
      check "redex differs" i [crw ~redex:(c "cr2") "crw"];
   print_endline "Rule:";
   let i = rule "rl" in
      check "implemented" i [rule "rl"];
      let premise = MetaImplies (MetaTheorem (c "h"), MetaTheorem (c "goal")) in
         check "a premise, with its extract" (rule ~stmt:premise "rl")
            [rule ~stmt:(MetaFunction (c "ext", MetaTheorem (c "h"), MetaTheorem (c "goal"))) "rl"];
      check "missing" i [];
      check "no parameter" i [rule ~params:[] "rl"];
      check "statement differs" i [rule ~stmt:(MetaTheorem (c "goal2")) "rl"];
   print_endline "Declarations:";
   let tc = DeclareTypeClass (normal, op "tc", op "tcty", ParentNone) in
      check "kind: missing (passed on)" tc [];
      check "kind: implemented" tc [DeclareTypeClass (normal, op "tc", op "tcty", ParentNone)];
      check "kind: parent differs" tc [DeclareTypeClass (normal, op "tc", op "tcty", ParentExtends (op "p"))];
      check "kind: type differs" tc [DeclareTypeClass (normal, op "tc", op "tcty2", ParentNone)];
   let dt = DeclareType (normal, ty (c "dt"), op "tc") in
      check "type: missing (passed on)" dt [];
      check "type: implemented" dt [DeclareType (normal, ty (c "dt"), op "tc")];
      check "type: its kind differs" dt [DeclareType (normal, ty (c "dt"), op "tc2")];
   let dterm = DeclareTerm (normal, ty (c "dterm")) in
      check "term: missing (passed on)" dterm [];
      check "term: implemented" dterm [DeclareTerm (normal, ty (c "dterm"))];
      check "term: by a definition" dterm [def normal "d" (c "dterm") (c "v")];
      check "term: shape class differs" dterm [DeclareTerm (iform, ty (c "dterm"))];
   let d = def normal "d" (c "dd") (c "v") in
      check "define: implemented" d [def normal "d" (c "dd") (c "v")];
      check "define: missing" d [];
      check "define: value differs" d [def normal "d" (c "dd") (c "v2")];
      check "define: opaque in the implementation" d [def ~opaque:true normal "d" (c "dd") (c "v")];
      check "define: shape class differs" d [def iform "d" (c "dd") (c "v")];
   let tr = DeclareTypeRewrite (c "tr1", c "tr2") in
      check "type rewrite: missing (passed on)" tr [];
      check "type rewrite: implemented" tr [DeclareTypeRewrite (c "tr1", c "tr2")];
      check "type rewrite: contractum differs" tr [DeclareTypeRewrite (c "tr1", c "tr3")];
   print_endline "ML items:";
   check "MLRewrite implemented" (MLRewrite (ml "m" (c "mt"))) [MLRewrite (ml "m" (c "mt"))];
   check "MLRewrite missing" (MLRewrite (ml "m" (c "mt"))) [MLAxiom (ml "m" (c "mt"))];
   check "MLRewrite term differs" (MLRewrite (ml "m" (c "mt"))) [MLRewrite (ml "m" (c "mt2"))];
   check "MLAxiom implemented" (MLAxiom (ml "a" (c "at"))) [MLAxiom (ml "a" (c "at"))];
   check "MLAxiom missing" (MLAxiom (ml "a" (c "at"))) [MLRewrite (ml "a" (c "at"))];
   check "MLAxiom term differs" (MLAxiom (ml "a" (c "at"))) [MLAxiom (ml "a" (c "at2"))];
   print_endline "Other items:";
   check "Extends implemented" (parent ["Itt"; "x"]) [parent ["Itt"; "x"]];
   check "Extends missing" (parent ["Itt"; "x"]) [parent ["Itt"; "y"]];
   check "DForm implemented" (dform [DFormParens] (c "d")) [dform [DFormParens] (c "d")];
   check "DForm missing" (dform [] (c "d")) [dform [] (c "e")];
   check "DForm options differ" (dform [DFormParens] (c "d")) [dform [DFormPrec "p"] (c "d")];
   check "Prec implemented" (Prec "p") [Prec "q"; Prec "p"];
   check "Prec missing" (Prec "p") [Prec "q"];
   check "Resource implemented" (Resource ("res", c "r")) [Resource ("res", c "other")];
   check "Resource missing" (Resource ("res", c "r")) [];
   check "Infix implemented" (MLGramUpd (Infix "+++")) [MLGramUpd (Infix "+++")];
   check "Infix missing" (MLGramUpd (Infix "+++")) [MLGramUpd (Suffix "+++")];
   check "Suffix missing" (MLGramUpd (Suffix "!!")) [];
   check "Id missing (passed on)" (Id 7) [];
   check "Id the same" (Id 7) [Id 7];
   check "Id differs" (Id 7) [Id 8];
   check "Improve (refused)" (Improve { improve_name = "i"; improve_flag = Public; improve_expr = bnd (c "e") }) [];
   check "Comment" (Comment (c "cm")) [];
   check "Module implemented" (Module ("M", info [rw "r" (c "x") (c "y")])) [Module ("M", info [rw "r" (c "x") (c "y")])];
   check "Module: an item inside differs" (Module ("M", info [rw "r" (c "x") (c "y")])) [Module ("M", info [rw "r" (c "x") (c "z")])];
   check "Module missing" (Module ("M", info [])) [Module ("N", info [])];
   print_endline "Several items:";
   let interf = info [Id 1; ifm (c "ir") (c "ic"); rw "r" (c "x") (c "y"); DeclareTerm (normal, ty (c "dterm"))] in
      match T.check_implementation (info [rw "r" (c "x") (c "y")]) interf with
         items -> Printf.printf "  passed on, in order: [%s]\n" (String.concat "; " (List.map (fun (it, _) -> kind it) items))
       | exception e -> Printf.printf "  raised %s\n" (Printexc.to_string e)
