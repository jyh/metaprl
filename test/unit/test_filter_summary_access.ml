(* unit-link: filter *)
(*
 * Filter_summary's access functions over a module_info: the find_*
 * lookups by name, find, find_id, find_sub_module, parents,
 * get_resources, get_infixes, get_proofs, set_command and
 * add_prefix_commands.
 *
 * Filter_cache_fun, refine.ml, filter_grammar and the shell call them;
 * no unit test did, and most of them no theory build reaches either
 * (bisect at c013b0579 for the unit tests and 008a9607e for a theory
 * build: test_*/find_* for rewrites, ML rewrites and axioms, modules,
 * dforms and precedences, find_sub_module's search, get_infixes).
 *
 * A module_info is polymorphic in its term types, so every term here is
 * a string.  The test prints what each function returns for names that
 * are present, absent, or present as an item of another kind, and for
 * a name that two items share.  The expected file is the output of the
 * code as written.
 *
 * Pinned as found: each lookup returns the latest item added; get_proofs,
 * get_resources and parents list the latest first; rules, rewrites and
 * conditional rewrites share one name space in set_command, so a Rewrite
 * replaces a Rule of its name; set_command raises Not_found when no item
 * has the new item's name, and always for a kind with no name (Id).
 * Fixed after this test was written: find_sub_module printed a debug
 * line on stderr for every module it passed.
 *)

open Filter_type
open Filter_summary_type

module S = Filter_summary

let loc = Ploc.dummy
let bnd item = { item_bindings = []; item_item = item }
let no_res = bnd []

let rw name redex =
   Rewrite { rw_name = name; rw_redex = redex; rw_contractum = "c"; rw_proof = "pf-" ^ name; rw_resources = no_res }
let crw name =
   CondRewrite { crw_name = name; crw_params = []; crw_assums = []; crw_redex = "cr"; crw_contractum = "cc";
                 crw_proof = "pf-" ^ name; crw_resources = no_res }
let rule name stmt =
   Rule { rule_name = name; rule_params = []; rule_stmt = stmt; rule_proof = "pf-" ^ name; rule_resources = no_res }
let ml name = { mlterm_name = name; mlterm_params = []; mlterm_term = "mt-" ^ name; mlterm_def = None; mlterm_resources = no_res }
let df name redex =
   DForm { dform_name = name; dform_modes = Dform.AllModes; dform_options = []; dform_redex = redex; dform_def = NoDForm }

type info = (string, string, string, string, string, string, string) S.module_info

let sub_inner : info = S.add_command (S.new_module_info ()) (rw "deep" "d", loc)
let sub = S.add_command (S.new_module_info ()) (Module ("Inner", sub_inner), loc)
let sub = S.add_command sub (rw "inner" "i", loc)

(* Source order.  "shared" names a Rewrite, then a Rule, then a DForm. *)
let items = [
   Parent { parent_name = [ "Itt"; "first" ]; parent_resources = [] };
   Id 7;
   rw "rw" "r";
   crw "crw";
   rule "rule" "stmt";
   MLRewrite (ml "mlr");
   MLAxiom (ml "mla");
   Module ("Sub", sub);
   df "df" "d";
   Prec "prec";
   InputForm { iform_name = "if"; iform_redex = "ir"; iform_contractum = "ic" };
   Resource ("res1", "r1");
   MLGramUpd (Infix "+++");
   Parent { parent_name = [ "Itt"; "second" ]; parent_resources = [] };
   Resource ("res2", "r2");
   MLGramUpd (Suffix "!!");
   rw "shared" "s1";
   rule "shared" "s2";
   df "shared" "s3";
   Id 8;
]

let info : info = List.fold_left (fun info item -> S.add_command info (item, loc)) (S.new_module_info ()) items

let describe = function
   Rewrite { rw_name = n; rw_redex = r; _ } -> "Rewrite " ^ n ^ " " ^ r
 | CondRewrite { crw_name = n; _ } -> "CondRewrite " ^ n
 | Rule { rule_name = n; rule_stmt = s; _ } -> "Rule " ^ n ^ " " ^ s
 | MLRewrite { mlterm_name = n; _ } -> "MLRewrite " ^ n
 | MLAxiom { mlterm_name = n; _ } -> "MLAxiom " ^ n
 | Parent { parent_name = p; _ } -> "Parent " ^ String.concat "." p
 | Module (n, _) -> "Module " ^ n
 | DForm { dform_name = n; dform_redex = r; _ } -> "DForm " ^ n ^ " " ^ r
 | Prec s -> "Prec " ^ s
 | PrecRel _ -> "PrecRel"
 | Id i -> "Id " ^ string_of_int i
 | Resource (n, r) -> "Resource " ^ n ^ " " ^ r
 | Improve _ -> "Improve"
 | MLGramUpd (Infix s) -> "MLGramUpd Infix " ^ s
 | MLGramUpd (Suffix s) -> "MLGramUpd Suffix " ^ s
 | SummaryItem _ -> "SummaryItem"
 | ToploopItem _ -> "ToploopItem"
 | MagicBlock _ -> "MagicBlock"
 | Comment _ -> "Comment"
 | InputForm { iform_name = n; _ } -> "InputForm " ^ n
 | PRLGrammar _ -> "PRLGrammar"
 | DeclareTypeClass _ -> "DeclareTypeClass"
 | DeclareType _ -> "DeclareType"
 | DeclareTerm _ -> "DeclareTerm"
 | DefineTerm _ -> "DefineTerm"
 | DeclareTypeRewrite _ -> "DeclareTypeRewrite"

let opt = function
   Some (item, _) -> "Some (" ^ describe item ^ ")"
 | None -> "None"

let attempt f = try f () with e -> "raises " ^ Printexc.to_string e

let show name f = Printf.printf "%-34s %s\n%!" name (attempt f)

let items_of info = String.concat "; " (List.map (fun (item, _) -> describe item) (S.info_items info))

let lookups = [
   "find_rewrite", S.find_rewrite;
   "find_mlrewrite", S.find_mlrewrite;
   "find_mlaxiom", S.find_mlaxiom;
   "find_module", S.find_module;
   "find_dform", S.find_dform;
   "find_prec", S.find_prec;
]

let names = [ "rw"; "crw"; "rule"; "mlr"; "mla"; "Sub"; "df"; "prec"; "if"; "shared"; "absent" ]

let () =
   List.iteri (fun k (item, _) -> Printf.printf "item %2d: %s\n" k (describe item)) (S.info_items info);
   List.iter (fun (fname, f) ->
         List.iter (fun n -> show (Printf.sprintf "%s %s" fname n) (fun () -> opt (f info n))) names) lookups;
   List.iter (fun n -> show ("find " ^ n) (fun () -> describe (fst (S.find info n)))) names;
   show "find_id" (fun () -> string_of_int (S.find_id info));
   show "find_id (empty)" (fun () -> string_of_int (S.find_id (S.new_module_info ())));
   show "parents" (fun () -> String.concat "; " (List.map (String.concat ".") (S.parents info)));
   show "get_resources" (fun () -> String.concat "; " (List.map (fun (n, r) -> n ^ "=" ^ r) (S.get_resources info)));
   show "get_infixes" (fun () ->
         String.concat "; " (List.map (function Infix s -> "Infix " ^ s | Suffix s -> "Suffix " ^ s)
                               (Infix.Set.elements (S.get_infixes info))));
   show "get_proofs" (fun () -> String.concat "; " (List.map (fun (n, p) -> n ^ "=" ^ p) (S.get_proofs info)));
   (* find_sub_module walks a path of nested modules. *)
   List.iter (fun path ->
         show ("find_sub_module [" ^ String.concat "; " path ^ "]")
            (fun () -> let m = S.find_sub_module info path in
                       if m == info then "the module itself" else items_of m))
      [ []; [ "Sub" ]; [ "Sub"; "Inner" ]; [ "Absent" ]; [ "Sub"; "Absent" ] ];
   (* set_command replaces the first item (in info_list order, the
    * latest added) its name test accepts, and raises Not_found when
    * none does, which is always for an item kind with no name test.
    * Printed: each position whose item changed, old -> new. *)
   let changed info' =
      let a = List.map (fun (i, _) -> describe i) (S.info_items info) in
      let b = List.map (fun (i, _) -> describe i) (S.info_items info') in
         if List.length a <> List.length b then Printf.sprintf "%d items, was %d" (List.length b) (List.length a)
         else
            match List.concat (List.mapi (fun k (x, y) -> if x = y then [] else [ Printf.sprintf "%d: %s -> %s" k x y ])
                                 (List.combine a b)) with
               [] -> "no item changed"
             | l -> String.concat "; " l
   in
   let set name item = show name (fun () -> changed (S.set_command info (item, loc))) in
      set "set_command Rewrite rw" (rw "rw" "NEW");
      set "set_command Rule shared" (rule "shared" "NEW");
      set "set_command Rewrite shared" (rw "shared" "NEW");
      set "set_command DForm shared" (df "shared" "NEW");
      set "set_command Prec prec" (Prec "prec");
      set "set_command MLRewrite absent" (MLRewrite (ml "absent"));
      set "set_command Id" (Id 99);
      show "add_prefix_commands" (fun () ->
            items_of (S.add_prefix_commands (S.add_command (S.new_module_info ()) (Prec "last", loc))
                        [ Prec "p1", loc; Prec "p2", loc ]))
