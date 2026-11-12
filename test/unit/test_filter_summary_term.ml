(* unit-link: filter *)
(*
 * Filter_summary's term form: a module summary as a list of terms and back.
 *
 * FilterSummaryTerm.term_list writes a module_info as terms and
 * of_term_list reads them back; Filter_cache uses the pair for the term
 * file system and the library.  No theory build or proof census reaches
 * either (bisect at 008a9607e: dest_term_aux 89 of 89 points and
 * term_list_aux 36 of 36 unreached).
 *
 * One module_info holds one item of every summary item kind (and every
 * variant inside an item where there are several: dform definitions and
 * options, dform modes, precedence relations, grammar updates, private
 * flags, parameters).  Every type parameter is a term, so the converters
 * are the identity, except meta terms.  The test prints, for each item,
 * its kind and whether it survives
 *    terms1 = term_list info;  info' = of_term_list terms1;
 *    terms2 = term_list info'
 * with terms1 and terms2 alpha-equal item for item, and whether info'
 * has the same kinds in the same order; for a dform it also prints the
 * modes and options read back when they differ from those written.  The
 * expected file is the output of the code as written.
 *
 * Pinned as found:
 * - a dform's DFormInheritPrec option is written as a prec_df term with
 *   no parameter, which the reader takes for DFormPrec and refuses
 *   (dest_string_param), so a module with such a dform cannot be read
 *   back at all (the line for all items in one module raises too);
 * - Modes and ExceptModes come back in reverse order (the reader pushes
 *   them and does not reverse, as it does for the options);
 * - PrimitiveModes is written as no modes, so it comes back as AllModes.
 * An empty PRLGrammar writes no term and comes back as no item.
 *)

open Lm_symbol
open Term_sig
open Opname
open Filter_base_type
open Filter_type
open Filter_summary_type
open Refiner.Refiner
open TermType
open Term
open TermMan

module S = Filter_summary
module T = Filter_summary.FilterSummaryTerm (Refiner.Refiner)

let op s = mk_opname s nil_opname
let c s = mk_simple_term (op s) []
let f s l = mk_simple_term (op s) l
let v s = mk_var_term (Lm_symbol.add s)

let loc = Ploc.dummy
let bnd item = { item_bindings = []; item_item = item }
let bnd_with item = { item_bindings = [ "b1", BindTerm (c "bt"); "b2", BindOpname (op "bo"); "b3", BindNum (Lm_num.num_of_int 7) ]; item_item = item }
let anno = { res_loc = loc; res_name = "res"; res_flag = Public; res_args = [ c "ra" ] }
let anno_priv = { res_loc = loc; res_name = "resp"; res_flag = Private; res_args = [] }
let no_res = bnd []
let some_res = bnd_with [ anno; anno_priv ]
let params = [ IntParam (Lm_symbol.add "i"); AddrParam (Lm_symbol.add "a"); TermParam (c "tp") ]

let ty t = { Term_ty_sig.ty_term = t; ty_opname = op "tyop"; ty_params = []; ty_bterms = []; ty_type = c "ty" }

let sub_info =
   S.add_command (S.new_module_info ()) (Rewrite { rw_name = "inner"; rw_redex = c "x"; rw_contractum = c "y"; rw_proof = c "pf"; rw_resources = no_res }, loc)

let items = [
   "Rewrite", Rewrite { rw_name = "rw"; rw_redex = f "r" [v "x"]; rw_contractum = v "x"; rw_proof = c "pf"; rw_resources = some_res };
   "CondRewrite", CondRewrite { crw_name = "crw"; crw_params = params; crw_assums = [ c "as1"; c "as2" ];
                                crw_redex = c "cr"; crw_contractum = c "cc"; crw_proof = c "pf"; crw_resources = no_res };
   "Rule", Rule { rule_name = "rl"; rule_params = params;
                  rule_stmt = MetaImplies (MetaTheorem (c "h"), MetaIff (MetaTheorem (c "a"), MetaTheorem (c "b")));
                  rule_proof = c "pf"; rule_resources = some_res };
   "Rule (MetaFunction)", Rule { rule_name = "rlf"; rule_params = [];
                  rule_stmt = MetaFunction (c "fn", MetaTheorem (c "a"), MetaLabeled ("lbl", MetaTheorem (c "b")));
                  rule_proof = c "pf"; rule_resources = no_res };
   "MLRewrite (no def)", MLRewrite { mlterm_name = "mlr"; mlterm_params = params; mlterm_term = c "mt"; mlterm_def = None; mlterm_resources = no_res };
   "MLRewrite (def)", MLRewrite { mlterm_name = "mlr2"; mlterm_params = []; mlterm_term = c "mt"; mlterm_def = Some (bnd_with (c "code")); mlterm_resources = no_res };
   "MLAxiom", MLAxiom { mlterm_name = "mla"; mlterm_params = []; mlterm_term = c "ma"; mlterm_def = Some (bnd (c "code")); mlterm_resources = some_res };
   "Parent", Parent { parent_name = [ "Itt"; "itt_x" ]; parent_resources = [ "r1", { resource_input = c "in"; resource_output = c "out" } ] };
   "Module", Module ("Sub", sub_info);
   "DForm (Modes, two)", DForm { dform_name = "df1"; dform_modes = Modes [ "prl"; "tex" ]; dform_options = [];
                                dform_redex = c "d1"; dform_def = TermDForm (c "dd") };
   "DForm (ExceptModes, two)", DForm { dform_name = "df1e"; dform_modes = ExceptModes [ "html"; "tex" ]; dform_options = [];
                                dform_redex = c "d1e"; dform_def = TermDForm (c "dd") };
   "DForm (DFormInheritPrec)", DForm { dform_name = "df1i"; dform_modes = AllModes; dform_options = [ DFormInheritPrec ];
                                dform_redex = c "d1i"; dform_def = TermDForm (c "dd") };
   "DForm (MLDForm)", DForm { dform_name = "df2"; dform_modes = ExceptModes [ "html" ]; dform_options = [ DFormPrec "p"; DFormParens ];
                              dform_redex = c "d2"; dform_def = MLDForm { dform_ml_printer = "printer"; dform_ml_buffer = "buf"; dform_ml_code = bnd_with (c "mlcode") } };
   "DForm (NoDForm, AllModes)", DForm { dform_name = "df3"; dform_modes = AllModes; dform_options = []; dform_redex = c "d3"; dform_def = NoDForm };
   "DForm (PrimitiveModes)", DForm { dform_name = "df4"; dform_modes = PrimitiveModes; dform_options = []; dform_redex = c "d4"; dform_def = TermDForm (c "dd4") };
   "Prec", Prec "p";
   "PrecRel LT", PrecRel { prec_rel = Precedence.LTRelation; prec_left = "p"; prec_right = "q" };
   "PrecRel EQ", PrecRel { prec_rel = Precedence.EQRelation; prec_left = "p"; prec_right = "q" };
   "PrecRel GT", PrecRel { prec_rel = Precedence.GTRelation; prec_left = "p"; prec_right = "q" };
   "PrecRel No", PrecRel { prec_rel = Precedence.NoRelation; prec_left = "p"; prec_right = "q" };
   "Id", Id 12345;
   "Resource", Resource ("resname", c "resource");
   "Improve (Public)", Improve { improve_name = "imp"; improve_flag = Public; improve_expr = bnd_with (c "ie") };
   "Improve (Private)", Improve { improve_name = "imp2"; improve_flag = Private; improve_expr = bnd (c "ie2") };
   "MLGramUpd Infix", MLGramUpd (Infix "+++");
   "MLGramUpd Suffix", MLGramUpd (Suffix "!!");
   "SummaryItem", SummaryItem (bnd_with (c "si"));
   "ToploopItem", ToploopItem (c "tli");
   "MagicBlock", MagicBlock { magic_name = "magic"; magic_code = [ c "m1"; c "m2" ] };
   "Comment", Comment (c "comment");
   "InputForm", InputForm { iform_name = "if"; iform_redex = c "ir"; iform_contractum = c "ic" };
   "PRLGrammar (empty)", PRLGrammar Filter_grammar.empty;
   "DeclareTypeClass (none)", DeclareTypeClass (Filter_shape.shape_normal, op "tc", op "tcty", ParentNone);
   "DeclareTypeClass (extends)", DeclareTypeClass (Filter_shape.shape_normal, op "tc2", op "tcty", ParentExtends (op "tc"));
   "DeclareTypeClass (include)", DeclareTypeClass (Filter_shape.shape_normal, op "tc3", op "tcty", ParentInclude (op "tc"));
   "DeclareType", DeclareType (Filter_shape.shape_normal, ty (c "dt"), op "tc");
   "DeclareTerm", DeclareTerm (Filter_shape.shape_normal, ty (c "dterm"));
   "DefineTerm (opaque)", DefineTerm (Filter_shape.shape_iform, ty (c "deft"),
                      { term_def_name = "def"; term_def_value = c "val"; term_def_resources = no_res; term_def_opaque = true });
   "DefineTerm", DefineTerm (Filter_shape.shape_normal, ty (c "deft2"),
                      { term_def_name = "def2"; term_def_value = c "val2"; term_def_resources = some_res; term_def_opaque = false });
   "DeclareTypeRewrite", DeclareTypeRewrite (c "tr1", c "tr2");
]

let kind = function
   Rewrite _ -> "Rewrite" | CondRewrite _ -> "CondRewrite" | Rule _ -> "Rule" | MLRewrite _ -> "MLRewrite"
 | MLAxiom _ -> "MLAxiom" | Parent _ -> "Parent" | Module _ -> "Module" | DForm _ -> "DForm" | Prec _ -> "Prec"
 | PrecRel _ -> "PrecRel" | Id _ -> "Id" | Resource _ -> "Resource" | Improve _ -> "Improve"
 | MLGramUpd _ -> "MLGramUpd" | SummaryItem _ -> "SummaryItem" | ToploopItem _ -> "ToploopItem"
 | MagicBlock _ -> "MagicBlock" | Comment _ -> "Comment" | InputForm _ -> "InputForm" | PRLGrammar _ -> "PRLGrammar"
 | DeclareTypeClass _ -> "DeclareTypeClass" | DeclareType _ -> "DeclareType" | DeclareTerm _ -> "DeclareTerm"
 | DefineTerm _ -> "DefineTerm" | DeclareTypeRewrite _ -> "DeclareTypeRewrite"

let id x = x
let to_terms =
   { term_f = id; meta_term_f = T.term_of_meta_term; proof_f = (fun _ p -> p); resource_f = id;
     ctyp_f = id; expr_f = id; item_f = id }
let of_terms =
   { term_f = id; meta_term_f = T.meta_term_of_term; proof_f = (fun _ p -> p); resource_f = id;
     ctyp_f = id; expr_f = id; item_f = id }

let attempt f = try Ok (f ()) with e -> Error (Printexc.to_string e)

(* What a dform's modes and options are, since the terms alone do not
 * show every difference (PrimitiveModes and AllModes both write no
 * mode). *)
let modes_string : Dform.dform_modes -> string = function
   Dform.Modes l -> "Modes [" ^ String.concat "; " l ^ "]"
 | ExceptModes l -> "ExceptModes [" ^ String.concat "; " l ^ "]"
 | AllModes -> "AllModes"
 | PrimitiveModes -> "PrimitiveModes"
let option_string = function
   DFormInheritPrec -> "DFormInheritPrec"
 | DFormPrec s -> "DFormPrec " ^ s
 | DFormParens -> "DFormParens"
let dform_string = function
   DForm { dform_modes = m; dform_options = o; _ } ->
      Printf.sprintf " {%s; [%s]}" (modes_string m) (String.concat "; " (List.map option_string o))
 | _ -> ""

let one (name, item) =
   let info = S.add_command (S.new_module_info ()) (item, loc) in
   let result =
      match attempt (fun () -> T.term_list to_terms info) with
         Error e -> "term_list raises " ^ e
       | Ok terms1 ->
            match attempt (fun () -> T.of_term_list of_terms terms1) with
               Error e -> Printf.sprintf "%d term(s); of_term_list raises %s" (List.length terms1) e
             | Ok info' ->
                  let kinds' = List.map (fun (it, _) -> kind it) (S.info_items info') in
                  match attempt (fun () -> T.term_list to_terms info') with
                     Error e -> "second term_list raises " ^ e
                   | Ok terms2 ->
                        let same = List.length terms1 = List.length terms2 && List.for_all2 TermSubst.alpha_equal terms1 terms2 in
                           Printf.sprintf "%d term(s); back as [%s]; %s%s" (List.length terms1)
                              (String.concat "; " kinds') (if same then "same terms" else "TERMS DIFFER")
                              (match S.info_items info' with
                                  [ (it', _) ] when dform_string item <> dform_string it' ->
                                     Printf.sprintf "; wrote%s, read%s" (dform_string item) (dform_string it')
                                | _ -> "")
   in
      Printf.printf "%-28s %s\n" name result

let () =
   List.iter one items;
   (* All of them in one module, in order, but the empty PRLGrammar, which
    * writes no term. *)
   let items = List.filter (fun (name, _) -> name <> "PRLGrammar (empty)") items in
   let info = List.fold_left (fun info (_, item) -> S.add_command info (item, loc)) (S.new_module_info ()) items in
      match attempt (fun () -> T.of_term_list of_terms (T.term_list to_terms info)) with
         Error e -> Printf.printf "all %d items in one module: raises %s\n" (List.length items) e
       | Ok info' ->
            let k = List.map (fun (it, _) -> kind it) (S.info_items info) in
            let k' = List.map (fun (it, _) -> kind it) (S.info_items info') in
               Printf.printf "all %d items in one module: %d back, kinds %s\n" (List.length items) (List.length k')
                  (if k = k' then "in the same order" else "DIFFER")
