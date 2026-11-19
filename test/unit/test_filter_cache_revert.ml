(* unit-link: filter *)
(* Filter_cache_fun's revert_proofs and clear_info (filter/base/
   filter_cache_fun.ml), which only the shell's package_info calls and
   no unit test, theory build or proof census reached (2026-11-16
   re-rank, deadsplit724).  revert_proofs: a module fcr is saved as
   fcr.prlb with proofs p Primitive and d Incomplete; a cache holding the
   other proofs (p Incomplete, d Primitive) is reverted, its proofs are
   printed before and after, then the files present, and the fcr.cmoz the
   revert wrote is loaded by a fresh cache.  Pinned as found: the comment
   above revert_proofs says it loads from the .prla and saves the .prlb;
   the code reads the .prlb and writes the .cmoz.  clear_info: one cache
   loads fcr.cmoz, the file is rewritten (both proofs Incomplete), the
   same cache loads it again and is served its stored summary, then
   clear_info, and the next load reads the file.  The expected file is
   the output of the code as written (2026-11-18), never typed.
   Mutants (2026-11-18, each rebuilt and relinked; an identity control
   unchanged): the revert keeping the current proofs, not saving the
   .cmoz, not setting the cache's info, clear_info keeping the summary,
   and clear_info not removing it from the library: each RED.
   The module is fcr and its files are removed at the start and the end:
   the unit tests share one directory (see test_filter_cache_proofs). *)
open File_base_type
open Filter_type
open Filter_summary_type
open Refiner.Refiner.Term

module C = Filter_cache.MakeCaches (Proof_convert.Convert)
module S = C.StrFilterCache

let loc = Ploc.dummy
let t s = mk_simple_term (Opname.make_opname [ s; "Fcr" ]) []
let no_res = { item_bindings = []; item_item = [] }
let rw name proof =
  Rewrite { rw_name = name; rw_redex = t ("r" ^ name); rw_contractum = t ("c" ^ name); rw_proof = proof; rw_resources = no_res }
let kind = function
  | Primitive x -> "Primitive " ^ Simple_print.SimplePrint.string_of_term x
  | Derived _ -> "Derived"
  | Incomplete -> "Incomplete"
  | Interactive _ -> "Interactive"
let show tag info = List.iter (fun (n, p) -> Printf.printf "%-22s %-3s %s\n" tag n (kind p)) (S.proofs info)
let try_ tag f = try f () with e -> Printf.printf "%-22s raised %s\n" tag (Printexc.to_string e)
let files = [ "fcr.prlb"; "fcr.prla"; "fcr.cmiz"; "fcr.cmoz"; "fcr.prlb.new"; "fcr.prla.new"; "fcr.cmiz.new"; "fcr.cmoz.new" ]
let exists () = Printf.printf "%-22s %s\n" "files" (String.concat " " (List.filter Sys.file_exists files))

let () =
  List.iter (fun f -> try Sys.remove f with Sys_error _ -> ()) files;
  let mk proofs =
    let info = S.create_cache (S.create [ "." ]) "fcr" ImplementationType in
    S.set_mode info InteractiveSummary;
    List.iter (fun (n, p) -> S.add_command info (rw n p, loc)) proofs;
    info
  in
  (* the .prlb holds p Primitive, d Incomplete *)
  let saved = mk [ "p", Primitive (t "axiom"); "d", Incomplete ] in
  try_ "save prlb" (fun () -> S.save saved () (OnlySuffixes [ "prlb" ]));
  try_ "save interface" (fun () ->
    let module SC = C.SigFilterCache in
    SC.save (SC.create_cache (SC.create [ "." ]) "fcr" InterfaceType) () (OnlySuffixes [ "cmiz" ]));
  exists ();
  (* a cache whose proofs differ: p Incomplete, d Primitive *)
  let cur = mk [ "p", Incomplete; "d", Primitive (t "other") ] in
  show "before revert" cur;
  try_ "revert" (fun () -> S.revert_proofs cur ());
  show "after revert" cur;
  exists ();
  (* the .cmoz revert wrote, loaded by a fresh cache *)
  try_ "load cmoz" (fun () -> show "loaded cmoz" (S.load (S.create [ "." ]) () "fcr" ImplementationType (OnlySuffixes [ "cmoz" ])));
  (* clear_info: one cache loads fcr, the file changes, the cache loads it
     again, then clear_info and a third load *)
  let cc = S.create [ "." ] in
  let ld tag = try_ tag (fun () -> show tag (S.load cc () "fcr" ImplementationType (OnlySuffixes [ "cmoz" ]))) in
  ld "first load";
  let first = try Some (S.load cc () "fcr" ImplementationType (OnlySuffixes [ "cmoz" ])) with _ -> None in
  try_ "rewrite cmoz" (fun () -> S.save (mk [ "p", Incomplete; "d", Incomplete ]) () (OnlySuffixes [ "cmoz" ]));
  ld "load, file changed";
  (match first with Some i -> try_ "clear_info" (fun () -> S.clear_info i) | None -> print_endline "no first info");
  ld "load after clear_info";
  List.iter (fun f -> try Sys.remove f with Sys_error _ -> ()) files
