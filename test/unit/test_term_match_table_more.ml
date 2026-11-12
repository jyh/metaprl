(* Term_match_table (refiner/reflib), the paths test_term_match_table's
   random first-order tables do not take and the proof census does
   (2026-11-11 reach census, 7 lines): the two resource adapters
   (table_resource_info and rmap_table_resource_info, through
   Mp_resource, as the 26 table resources use them), add_map with a
   second-order variable that carries contexts (simplify_term), a sequent
   pattern looked up on a sequent whose hypothesis at a matched position
   is a context (the lookup falls back), and a bucket in which an earlier
   entry's applicability test fails (repeated pattern variables) or the
   caller's predicate rejects an entry.  Each
   line prints the lookup's result; the expected file is the output of
   the code as written (2026-11-11).
   PINNED AS FOUND: add_map of a sequent pattern <H> >- k{'a<H>} is
   refused (Rewrite_util.check_arity).  simplify_term (the "XXX HACK" that
   strips arguments and bound contexts from second-order variables) turns
   'a<H> into 'a<> inside a sequent that binds H, and the rewrite it then
   compiles no longer agrees with itself on 'a's contexts. *)
open Refiner.Refiner
open TermType
open Term
open TermMan
open Term_sig
open Term_match_table

let op s = Opname.make_opname [ s ]
let v = Lm_symbol.add
let app o ts = mk_simple_term (op o) ts
let c s = app s []
let so name conts = mk_so_var_term (v name) (List.map v conts) []
let seq hyps concl = mk_sequent_term { sequent_args = c "arg"; sequent_hyps = SeqHyp.of_list hyps; sequent_concl = concl }
let sp = Simple_print.SimplePrint.string_of_term
let show_opt = function None -> "none" | Some s -> s

let get_tbl = Mp_resource.create_resource "tmt_tbl" (table_resource_info (fun t -> t))
let get_map = Mp_resource.create_resource "tmt_map" (rmap_table_resource_info (fun t -> t))

let () =
  Mp_resource.improve Mp_resource.Public "tmt_tbl" (Obj.repr (app "f" [ so "a" [] ], "f-any"));
  Mp_resource.improve Mp_resource.Public "tmt_tbl" (Obj.repr (app "f" [ c "c" ], "f-c"));
  Mp_resource.improve Mp_resource.Public "tmt_map" (Obj.repr (app "g" [ so "a" [ "H" ] ], [ app "h" [ so "a" [ "H" ] ] ], "g-to-h"));
  Mp_resource.close_theory "tmt";
  let bm = Mp_resource.find (Mp_resource.theory_bookmark "tmt") in
  let tbl : string term_table = get_tbl bm and map : string term_map_table = get_map bm in
  let look t = show_opt (lookup tbl select_all t) in
  Printf.printf "resource table, f{c}: %s\n" (look (app "f" [ c "c" ]));
  Printf.printf "resource table, f{d}: %s\n" (look (app "f" [ c "d" ]));
  Printf.printf "resource table, g{c}: %s\n" (look (app "g" [ c "c" ]));
  let lm t = match lookup_rmap map select_all t with
    | None -> "none" | Some (ts, x) -> x ^ " -> [" ^ String.concat "; " (List.map sp ts) ^ "]" in
  Printf.printf "resource rmap, g{c}: %s\n" (lm (app "g" [ c "c" ]));
  Printf.printf "resource rmap, g{k{c}}: %s\n" (lm (app "g" [ app "k" [ c "c" ] ]));
  Printf.printf "resource rmap, f{c}: %s\n" (lm (app "f" [ c "c" ]));
  (* sequent patterns *)
  let st = add_item empty_table (seq [ Context (v "H", [], []); Hypothesis (v "x", so "A" [ "H" ]); Hypothesis (v "y", so "B" [ "H" ]) ] (so "C" [ "H" ])) "two-hyps" in
  let st = add_item st (seq [ Context (v "H", [], []); Hypothesis (v "x", so "A" [ "H" ]) ] (so "C" [ "H" ])) "one-hyp" in
  let ls t = show_opt (lookup st select_all t) in
  Printf.printf "sequent, y: A; z: B >- C: %s\n" (ls (seq [ Hypothesis (v "y", c "A"); Hypothesis (v "z", c "B") ] (c "C")));
  Printf.printf "sequent, <J>; z: B >- C: %s\n" (ls (seq [ Context (v "J", [], []); Hypothesis (v "z", c "B") ] (c "C")));
  Printf.printf "sequent, z: B; <J> >- C: %s\n" (ls (seq [ Hypothesis (v "z", c "B"); Context (v "J", [], []) ] (c "C")));
  Printf.printf "sequent, >- C: %s\n" (ls (seq [] (c "C")));
  (* a bucket where the first entry's applicability test fails *)
  let pa = app "f" [ so "a" []; so "a" [] ] and pb = app "f" [ so "a" []; so "b" [] ] in
  List.iter (fun (name, tbl) ->
      let l t = show_opt (lookup tbl select_all t) in
      let all t = String.concat "," (List.sort compare (match lookup_bucket tbl select_all t with None -> [] | Some l -> l)) in
      let some t = String.concat "," (List.sort compare (match lookup_bucket tbl (fun x -> x <> "any") t with None -> [] | Some l -> l)) in
      Printf.printf "%s: f{c; c} %s · f{c; d} %s · bucket f{c; d} [%s] · bucket f{c; c} without \"any\" [%s]\n" name
        (l (app "f" [ c "c"; c "c" ])) (l (app "f" [ c "c"; c "d" ])) (all (app "f" [ c "c"; c "d" ])) (some (app "f" [ c "c"; c "c" ])))
    [ "f{'a;'a} then f{'a;'b}", add_item (add_item empty_table pa "same") pb "any";
      "f{'a;'b} then f{'a;'a}", add_item (add_item empty_table pb "any") pa "same" ];
  (* add_map with a context-carrying second-order variable *)
  let mt = add_map empty_map_table (app "k" [ so "a" [ "H"; "J" ] ]) [ app "m" [ so "a" [ "H"; "J" ] ]; c "n" ] "k-to-m" in
  let lm mt t = match lookup_rmap mt select_all t with
      | None -> "none" | Some (ts, x) -> x ^ " -> [" ^ String.concat "; " (List.map sp ts) ^ "]" in
  Printf.printf "add_map k{'a<H;J>}, k{c}: %s\n" (lm mt (app "k" [ c "c" ]));
  let r = try
      let mt = add_map empty_map_table (seq [ Context (v "H", [], []) ] (app "k" [ so "a" [ "H" ] ])) [ app "m" [ so "a" [ "H" ] ] ] "seq-k" in
      lm mt (seq [ Context (v "J", [], []) ] (app "k" [ c "c" ]))
    with RefineError.RefineError (s, _) -> "refused (" ^ s ^ ")" in
  Printf.printf "add_map <H> >- k{'a<H>}, <J> >- k{c}: %s\n" r
