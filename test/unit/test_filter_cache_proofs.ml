(* unit-link: filter *)
(* Filter_cache's proof marshalling (filter/base/filter_cache.ml:
   marshal_proof and unmarshal_proof), which no unit test, theory build
   or proof census reached (2026-11-15 re-rank, deadsplit680):
   test_filter_cache_save saves an empty module, so no proof was ever
   written.  Here a module m gets three rewrites whose proofs are
   Primitive (a term), Derived (an expression) and Incomplete; it is saved
   as m.prla, loaded by a fresh cache, and each loaded proof's kind is
   printed, with the lines of m.prla that name a proof kind.  Interactive
   proofs are not made: their value is the proof editor's.  The expected
   file is the output of the code as written (2026-11-15). *)
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

let () =
  let cache = S.create [ "." ] in
  let info = S.create_cache cache "m" ImplementationType in
  S.set_mode info InteractiveSummary;
  S.add_command info (rw "p" (Primitive (t "axiom")), loc);
  S.add_command info (rw "d" (Derived (MLast.ExLid (loc, Ploc.VaVal "idT"))), loc);
  S.add_command info (rw "i" Incomplete, loc);
  List.iter (fun (n, p) -> Printf.printf "before save %-4s %s\n" n (kind p)) (S.proofs info);
  (try S.save info () (OnlySuffixes [ "prla" ]); print_endline "saved" with e -> print_endline ("save raised " ^ Printexc.to_string e));
  (* loading an implementation reads its interface first: save an empty one *)
  (try
     let module SC = C.SigFilterCache in
     let sinfo = SC.create_cache (SC.create [ "." ]) "m" InterfaceType in
     SC.save sinfo () (OnlySuffixes [ "cmiz" ]); print_endline "interface saved"
   with e -> print_endline ("interface save raised " ^ Printexc.to_string e));
  let cache2 = S.create [ "." ] in
  (match S.load cache2 () "m" ImplementationType (OnlySuffixes [ "prla" ]) with
   | info2 -> List.iter (fun (n, p) -> Printf.printf "loaded      %-4s %s\n" n (kind p)) (S.proofs info2)
   | exception e -> print_endline ("load raised " ^ Printexc.to_string e))
