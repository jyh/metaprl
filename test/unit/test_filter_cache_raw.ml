(* unit-link: filter *)
(* Filter_cache's RAW summary format (Filter_cache.set_raw, suffix prlb):
   saving a module converts its summary with Filter_summary.summary_map
   (item_map) and loading converts it back, which nothing reached
   (2026-11-16 rank: test_filter_cache_proofs saves as prla).  The module
   is test_filter_cache_proofs' (three rewrites with Primitive, Derived and
   Incomplete proofs) plus a rule and a precedence; each loaded rewrite
   prints its proof's kind and its redex and contractum, the rule its
   statement.
   Read from the output: find_prec answers from the cache's own list
   (add_prec), not from the module's items, so a precedence declared as an
   item (Prec) is not found before the save, and none, not even one added
   with add_prec, is found after a load.
   Not reached, stated: item_map's arms for the other summary items (conditional
   rewrites, definitions, resources, ...): this module holds
   rewrites, a rule and a precedence only.  The module is named mraw, not m: run.sh runs every test
   in one directory, and test_filter_cache_proofs saves m.
   The expected file is the output of the code as written (2026-11-16),
   never typed. *)
open File_base_type
open Filter_type
open Filter_summary_type
open Refiner.Refiner.Term

module C = Filter_cache.MakeCaches (Proof_convert.Convert)
module S = C.StrFilterCache

let loc = Ploc.dummy
let t s = mk_simple_term (Opname.make_opname [ s; "Fcp" ]) []
let no_res = { item_bindings = []; item_item = [] }
let rw name proof =
  Rewrite { rw_name = name; rw_redex = t ("r" ^ name); rw_contractum = t ("c" ^ name); rw_proof = proof; rw_resources = no_res }
let kind = function
  | Primitive x -> "Primitive " ^ Simple_print.SimplePrint.string_of_term x
  | Derived _ -> "Derived"
  | Incomplete -> "Incomplete"
  | Interactive _ -> "Interactive"

let run suffix =
  Printf.printf "== saved and loaded as %s\n%!" suffix;
  let cache = S.create [ "." ] in
  let info = S.create_cache cache "mraw" ImplementationType in
  S.set_mode info InteractiveSummary;
  S.add_command info (rw "p" (Primitive (t "axiom")), loc);
  S.add_command info (rw "d" (Derived (MLast.ExLid (loc, Ploc.VaVal "idT"))), loc);
  S.add_command info (rw "i" Incomplete, loc);
  S.add_command info (Rule { rule_name = "r"; rule_params = []; rule_stmt = Term_sig.MetaImplies (Term_sig.MetaTheorem (t "ra"), Term_sig.MetaTheorem (t "rg")); rule_proof = Incomplete; rule_resources = no_res }, loc);
  S.add_command info (Prec "p1", loc);
  Printf.printf "before save: precedence p1 found: %b\n" (S.find_prec info "p1");
  S.add_prec info "p2";
  Printf.printf "before save: precedence p2 (add_prec) found: %b\n" (S.find_prec info "p2");
  (try S.save info () (OnlySuffixes [ suffix ]); print_endline "saved" with e -> print_endline ("save raised " ^ Printexc.to_string e));
  (try
     let module SC = C.SigFilterCache in
     let sinfo = SC.create_cache (SC.create [ "." ]) "mraw" InterfaceType in
     SC.save sinfo () (OnlySuffixes [ suffix ^ "i"; "cmiz" ]); print_endline "interface saved"
   with e -> print_endline ("interface save raised " ^ Printexc.to_string e));
  let cache2 = S.create [ "." ] in
  (match S.load cache2 () "mraw" ImplementationType (OnlySuffixes [ suffix ]) with
   | info2 ->
      List.iter (fun (n, p) ->
          let rx = match S.find_rewrite info2 n with
            | Some (Rewrite r, _) -> Simple_print.SimplePrint.string_of_term r.rw_redex ^ " --> " ^ Simple_print.SimplePrint.string_of_term r.rw_contractum
            | _ -> "(no rewrite)" in
          Printf.printf "loaded      %-4s %-20s %s\n" n (kind p) rx) (S.proofs info2)
   | exception e -> print_endline ("load raised " ^ Printexc.to_string e));
  (match S.load (S.create [ "." ]) () "mraw" ImplementationType (OnlySuffixes [ suffix ]) with
   | info3 ->
      (match S.find info3 "r" with
       | Rule r, _ -> Printf.printf "loaded rule r: %s\n" (match r.rule_stmt with Term_sig.MetaImplies (Term_sig.MetaTheorem a, Term_sig.MetaTheorem g) -> Simple_print.SimplePrint.string_of_term a ^ " --> " ^ Simple_print.SimplePrint.string_of_term g | _ -> "(another statement)")
       | _ -> print_endline "r is not a rule"
       | exception Not_found -> print_endline "rule r not found");
      Printf.printf "after load: precedence p1 found: %b, p2 found: %b\n" (S.find_prec info3 "p1") (S.find_prec info3 "p2")
   | exception e -> print_endline ("second load raised " ^ Printexc.to_string e))

let () =
  Filter_cache.set_raw ();
  run "prlb"
