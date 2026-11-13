(* unit-link: filter *)
(*
 * Filter_summary.FilterSummaryTerm.copy_proofs: copying proofs from an
 * old summary (the .prla) into a new one (the .ml just read), as
 * Filter_cache_fun.copy_proofs does for filter_parse and filter_bin.
 *
 * For every rewrite, conditional rewrite and rule of the new summary it
 * looks up the old item of the same name.  Found with the same
 * statement: the proof is copied silently.  Found with another statement,
 * or as another kind of proof: the proof is copied and a warning goes to
 * stderr.  Not found: the item is kept as it is.  Nested modules are
 * copied module by module; every other item passes through.  A theory
 * build reaches the silent copies and few of the warnings (bisect at
 * 008a9607e: copy_proofs 11, copy_rw_proof 7, copy_crw_proof 10,
 * copy_rule_proof 10 and copy_module_proof 4 points unreached; no unit
 * test reached any of it at c013b0579).
 *
 * Every proof here is a string, and copy_proof writes "new<-old", so the
 * output shows which old proof each item took.  The expected file is the
 * output of the code as written, the warnings included.
 *
 * Pinned as found: the warnings come in reverse source order (the items
 * are kept latest first); an old name given twice gives its latest proof;
 * a new module whose name the old summary has only as another kind of
 * item (Prec M2) keeps its own items.
 *)

open Term_sig
open Filter_type
open Filter_summary_type
open Refiner.Refiner
open TermType
open Term

module S = Filter_summary
module T = Filter_summary.FilterSummaryTerm (Refiner.Refiner)

let op s = Opname.mk_opname s Opname.nil_opname
let c s = mk_simple_term (op s) []

let loc = Ploc.dummy
let no_res = { item_bindings = []; item_item = [] }

let rw ?(redex = "a") ?(contractum = "b") name proof =
   Rewrite { rw_name = name; rw_redex = c redex; rw_contractum = c contractum; rw_proof = proof; rw_resources = no_res }
let crw ?(redex = "a") ?(contractum = "b") ?(assums = [ "h" ]) name proof =
   CondRewrite { crw_name = name; crw_params = []; crw_assums = List.map c assums; crw_redex = c redex;
                 crw_contractum = c contractum; crw_proof = proof; crw_resources = no_res }
let rule ?(stmt = "s") name proof =
   Rule { rule_name = name; rule_params = []; rule_stmt = MetaTheorem (c stmt); rule_proof = proof; rule_resources = no_res }

type info = (term, meta_term, string, string, string, string, string) S.module_info

let info_of items : info = List.fold_left (fun info item -> S.add_command info (item, loc)) (S.new_module_info ()) items

let old_inner = info_of [ rw "inner" "old-inner"; rule "inner2" "old-inner2" ]
let new_inner = info_of [ rw "inner" "new-inner"; rule ~stmt:"t" "inner2" "new-inner2"; rw "inner3" "new-inner3" ]

(* The old summary. *)
let old_info = info_of [
   rw "same" "old-same";
   rw "rw-redex" "old-rw-redex";
   rw "rw-contractum" "old-rw-contractum";
   crw "crw-same" "old-crw-same";
   crw "crw-redex" "old-crw-redex";
   crw "crw-contractum" "old-crw-contractum";
   crw "crw-assum" "old-crw-assum";
   crw "crw-assum-count" "old-crw-assum-count";
   rule "rule-same" "old-rule-same";
   rule "rule-stmt" "old-rule-stmt";
   rule "rw-was-rule" "old-rw-was-rule";
   crw "rw-was-crw" "old-rw-was-crw";
   rw "crw-was-rw" "old-crw-was-rw";
   rule "crw-was-rule" "old-crw-was-rule";
   rw "rule-was-rw" "old-rule-was-rw";
   crw "rule-was-crw" "old-rule-was-crw";
   Module ("M", old_inner);
   rw "only-old" "old-only-old";
   Prec "M2";
   rw "dup" "old-dup-1";
   rw "dup" "old-dup-2";
]

(* The new summary. *)
let new_info = info_of [
   rw "same" "new-same";
   rw ~redex:"a2" "rw-redex" "new-rw-redex";
   rw ~contractum:"b2" "rw-contractum" "new-rw-contractum";
   crw "crw-same" "new-crw-same";
   crw ~redex:"a2" "crw-redex" "new-crw-redex";
   crw ~contractum:"b2" "crw-contractum" "new-crw-contractum";
   crw ~assums:[ "h2" ] "crw-assum" "new-crw-assum";
   crw ~assums:[ "h"; "h3" ] "crw-assum-count" "new-crw-assum-count";
   rule "rule-same" "new-rule-same";
   rule ~stmt:"t" "rule-stmt" "new-rule-stmt";
   rw "rw-was-rule" "new-rw-was-rule";
   rw "rw-was-crw" "new-rw-was-crw";
   crw "crw-was-rw" "new-crw-was-rw";
   crw "crw-was-rule" "new-crw-was-rule";
   rule "rule-was-rw" "new-rule-was-rw";
   rule "rule-was-crw" "new-rule-was-crw";
   Module ("M", new_inner);
   Module ("M2", info_of [ rw "m2" "new-m2" ]);
   rw "only-new" "new-only-new";
   rw "dup" "new-dup";
   Prec "prec";
   Id 3;
]

let describe = function
   Rewrite { rw_name = n; rw_proof = p; _ } -> "Rewrite " ^ n ^ ": " ^ p
 | CondRewrite { crw_name = n; crw_proof = p; _ } -> "CondRewrite " ^ n ^ ": " ^ p
 | Rule { rule_name = n; rule_proof = p; _ } -> "Rule " ^ n ^ ": " ^ p
 | Module (n, _) -> "Module " ^ n
 | Prec s -> "Prec " ^ s
 | Id i -> "Id " ^ string_of_int i
 | _ -> "other"

let rec print indent info =
   List.iter (fun (item, _) ->
         Printf.printf "%s%s\n%!" indent (describe item);
         match item with
            Module (_, m) -> print (indent ^ "   ") m
          | _ -> ()) (S.info_items info)

let () =
   let copy_proof p1 p2 = p1 ^ "<-" ^ p2 in
      match T.copy_proofs copy_proof new_info old_info with
         info ->
            flush stdout;
            prerr_endline "-- copied:";
            print "" info
       | exception e ->
            Printf.printf "copy_proofs raises %s\n" (Printexc.to_string e)
