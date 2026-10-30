(* Arith.find_contradiction (refiner/reflib), the core of itt_int_arith's
   arithT: given inequalities t1 >= t2 + n, it returns a subset whose
   conjunction is false, or raises RefineError when it finds none.  On 3,000
   random systems of 1-7 inequalities over the atoms a, b, c, d (with
   constants -3..3, and sometimes an atom compared with itself), against
   Bellman-Ford over integers as the model (a system of difference
   constraints is unsatisfiable exactly when some cycle's constants sum
   above 0):
     - it raises exactly when the model finds the system satisfiable;
     - what it returns is a sub-multiset of the input;
     - what it returns is itself unsatisfiable (a certificate).
   It prints each count with how many systems it was tried on, and the
   first difference.  The generator is a fixed linear congruential
   sequence, not Random. *)
open Refiner.Refiner.Term

let state = ref 59
let next () = state := (!state * 1103515245 + 12345) land 0x7fffffff; !state lsr 8
let pick n = next () mod n

let atoms = [| "a"; "b"; "c"; "d" |]
let term_of = Array.map (fun s -> mk_var_term (Lm_symbol.add s)) atoms
let show (i, j, n, k) = Printf.sprintf "#%d %s>=%s%+d" k atoms.(i) atoms.(j) n

(* Bellman-Ford for longest paths: i >= j + n is an edge j -> i of weight n;
   unsatisfiable iff a cycle of positive weight exists. *)
let unsat sys =
  let d = Array.make 4 0 in
  let changed = ref true and rounds = ref 0 in
  while !changed && !rounds <= 5 do
    changed := false; incr rounds;
    List.iter (fun (i, j, n, _) -> if d.(j) + n > d.(i) then (d.(i) <- d.(j) + n; changed := true)) sys
  done;
  !changed

let rec remove_one x = function [] -> None | y :: r -> if y = x then Some r else Option.map (fun r -> y :: r) (remove_one x r)
let rec submultiset xs ys = match xs with [] -> true | x :: r -> (match remove_one x ys with None -> false | Some ys -> submultiset r ys)

let names = [| "raises iff the system is satisfiable"; "returns a sub-multiset of the input";
               "what it returns is unsatisfiable" |]
let tried = Array.make 3 0 and ok = Array.make 3 0 and first = Array.make 3 None
let note k b what = tried.(k) <- tried.(k) + 1; if b then ok.(k) <- ok.(k) + 1 else if first.(k) = None then first.(k) <- Some what

let () =
  let n = 3000 and nunsat = ref 0 in
  for _ = 1 to n do
    let sys = List.init (1 + pick 7) (fun k ->
        let i = pick 4 in let j = if pick 6 = 0 then i else pick 4 in (i, j, pick 7 - 3, k)) in
    let want = unsat sys in
    if want then incr nunsat;
    let what = String.concat ", " (List.map show sys) in
    let input = List.map (fun (i, j, c, k) -> (term_of.(i), term_of.(j), Lm_num.num_of_int c, k)) sys in
    let got = try Some (Arith.find_contradiction input) with Refiner.Refiner.RefineError.RefineError _ -> None | e -> Some [ (term_of.(0), term_of.(0), Lm_num.num_of_int (-99), -1 - String.length (Printexc.to_string e)) ] in
    note 0 ((got <> None) = want) (what ^ (if want then ": unsatisfiable, it found nothing" else ": satisfiable, it returned a subset"));
    match got with
    | None -> ()
    | Some l ->
        let ks = List.map (fun (_, _, _, k) -> k) l in
        let back = List.filter_map (fun k -> List.find_opt (fun (_, _, _, k') -> k' = k) sys) ks in
        note 1 (List.length back = List.length ks && submultiset ks (List.map (fun (_, _, _, k) -> k) sys))
          (what ^ ": returned " ^ String.concat " " (List.map string_of_int ks));
        note 2 (unsat back) (what ^ ": returned " ^ String.concat ", " (List.map show back))
  done;
  Printf.printf "%d systems, %d unsatisfiable\n" n !nunsat;
  Array.iteri (fun k name ->
      Printf.printf "%-38s %5d of %5d\n" name ok.(k) tried.(k);
      match first.(k) with None -> () | Some w -> Printf.printf "  first difference: %s\n" w) names
