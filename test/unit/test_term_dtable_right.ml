(* Term_dtable's right-to-left entries (refiner/reflib), which the proof
   census reaches and no unit test did (2026-11-12 census, 2 lines: the
   lookup in the right-to-left table, and shift_fst, which hands the
   entry's value its pair).  test_term_dtable's right-to-left rule has a
   variable right side, which no ground goal reaches (its header says
   so); here the right sides are w{'A} and w2{'A; 'B}, with one subgoal
   for the second.  Each lookup prints the derivation built by the entry
   that answers, or Not_found.  The expected file is the output of the
   code as written (2026-11-12), never typed.
   Pinned as found: a right-to-left entry is keyed by the right side
   only, so a <= w{b} is answered with the derivation of b <= w{b}, the
   mirror of the left-to-right case test_term_dtable records. *)
open Lm_symbol
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan

let op o = Opname.make_opname [ o ]
let c o = mk_simple_term (op o) []
let w t = mk_simple_term (op "w") [ t ]
let m x = mk_so_var_term (add x) [] []
let sp = Simple_print.SimplePrint.string_of_term
let value name subs (t1, t2) =
  name ^ "[" ^ sp t1 ^ " <= " ^ sp t2 ^ "]"
  ^ (if subs = [] then "" else "(" ^ String.concat ", " (List.map (fun (_, _, d) -> d) subs) ^ ")")

let () =
  let base = Term_dtable.insert Term_dtable.empty_dtable [ (c "a", c "b") ] (value "ab") in
  let base = Term_dtable.insert_right base [ (m "A", w (m "A")) ] (value "wrap") in
  let base = Term_dtable.insert_right base [ (m "A", mk_simple_term (op "w2") [ m "A"; m "B" ]); (m "A", m "B") ] (value "wrap2") in
  let table = Term_dtable.extract base in
  let look name t1 t2 =
    Printf.printf "%-24s %s\n" name (try Term_dtable.lookup table t1 t2 with Not_found -> "Not_found")
  in
  look "a <= w{a}" (c "a") (w (c "a"));
  look "a <= w{b}" (c "a") (w (c "b"));
  look "a <= w{w{a}}" (c "a") (w (w (c "a")));
  look "a <= w2{a; b}" (c "a") (mk_simple_term (op "w2") [ c "a"; c "b" ]);
  look "a <= w2{a; c}" (c "a") (mk_simple_term (op "w2") [ c "a"; c "c" ]);
  look "a <= b" (c "a") (c "b")
