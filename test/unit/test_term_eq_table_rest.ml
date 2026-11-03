(* Term_eq_table's other half (test_term_eq_table covers add, replace,
   remove, find, mem, length and list_of): iter, map, fold_map, deletemax,
   union and print, none entered by a unit test (the 11-02 reflib coverage
   page). The same generator and model as test_term_eq_table: random tables
   over a small pool of terms, each against an association list keyed by
   the term as written, each key's values newest first. Checked on 300
   tables:
     - iter visits every (key, value) pair of the model once;
     - map f gives each key the model's values mapped by f, in order;
     - fold_map (fun k v acc -> add acc k (v + 1000)) empty t (the
       accumulator comes first) holds
       every pair once (values compared as a multiset per key), and visits a
       key's values newest first, so adding each reverses them;
     - deletemax, repeated until empty, returns each model key once with
       its values, and the rest has the other keys;
     - union t1 t2 gives each key the values of t1 then t2 (Base.append);
     - deletemax of the empty table, and print of a two-key table.
   It prints each count with how many checks were made, and the first
   difference. *)
open Term_sig
open Refiner.Refiner.Term

let state = ref 47
let next () = state := (!state * 1103515245 + 12345) land 0x7fffffff; !state lsr 8
let pick n = next () mod n

type t = C | G of t | F of t * t | Lam of string * t | V of string
let vars = [| "x"; "y"; "z" |]
let rec gen d =
  if d = 0 || pick 4 = 0 then (if pick 2 = 0 then C else V vars.(pick 3))
  else match pick 3 with
    | 0 -> G (gen (d - 1))
    | 1 -> F (gen (d - 1), gen (d - 1))
    | _ -> Lam (vars.(pick 3), gen (d - 1))

(* The renamed form: the binder at depth d becomes ua, ub, uc, ...  The
   pool's variables are x, y, z, so nothing is captured.  (No digits:
   Lm_symbol.add reads a trailing number as the symbol's index.) *)
let rec rename d env = function
  | C -> C | G a -> G (rename d env a) | F (a, b) -> F (rename d env a, rename d env b)
  | Lam (x, a) -> let x' = "u" ^ String.make 1 (Char.chr (97 + d)) in Lam (x', rename (d + 1) ((x, x') :: env) a)
  | V v -> V (try List.assoc v env with Not_found -> v)
let variant t = if pick 2 = 0 then t else rename 0 [] t

let rec show = function
  | C -> "c" | G a -> "g{" ^ show a ^ "}" | F (a, b) -> "f{" ^ show a ^ "; " ^ show b ^ "}"
  | Lam (x, a) -> "lam " ^ x ^ "." ^ show a | V v -> v

let op s = Opname.make_opname [ s ]
let add = Lm_symbol.add
let rec build = function
  | C -> mk_simple_term (op "c") []
  | G a -> mk_simple_term (op "g") [ build a ]
  | F (a, b) -> mk_simple_term (op "f") [ build a; build b ]
  | Lam (x, a) -> mk_term (mk_op (op "lam") []) [ mk_bterm [ add x ] (build a) ]
  | V v -> mk_var_term (add v)

(* Read a refiner term back, to compare list_of's keys by de Bruijn form. *)
let rec back t =
  if is_var_term t then V (Lm_symbol.to_string (dest_var t))
  else
    let { term_op = o; term_terms = bts } = dest_term t in
    let name = String.concat "!" (Opname.dest_opname (dest_op o).op_name) in
    match name, List.map dest_bterm bts with
    | "c", [] -> C
    | "g", [ { bvars = []; bterm = a } ] -> G (back a)
    | "f", [ { bvars = []; bterm = a }; { bvars = []; bterm = b } ] -> F (back a, back b)
    | "lam", [ { bvars = [ x ]; bterm = a } ] -> Lam (Lm_symbol.to_string x, back a)
    | _ -> V ("?" ^ name)

module T = Term_eq_table.MakeTermTable (struct type data = int let append = ( @ ) end)


let names = [| "iter visits the model's pairs"; "map f = the model's values mapped, in order";
               "fold_map holds every pair (multiset per key)"; "fold_map visits a key's values newest first";
               "deletemax drains each key once with its values"; "union t1 t2 = t1's values then t2's" |]
let tried = Array.make 6 0 and ok = Array.make 6 0 and first = Array.make 6 None
let note k b what = tried.(k) <- tried.(k) + 1; if b then ok.(k) <- ok.(k) + 1 else if first.(k) = None then first.(k) <- Some what

let random_table pool =
  let tbl = ref T.empty and model = ref [] in
  let get k = try List.assoc k !model with Not_found -> [] in
  let set k vs = model := (if vs = [] then [] else [ k, vs ]) @ List.remove_assoc k !model in
  for _ = 1 to 1 + pick 20 do
    let k = variant pool.(pick (Array.length pool)) in
    (match pick 4 with
     | 0 | 1 -> let v = pick 100 in tbl := T.add !tbl (build k) v; set k (v :: get k)
     | 2 -> let vs = List.init (pick 3) (fun _ -> pick 100) in tbl := T.replace !tbl (build k) vs; set k vs
     | _ -> tbl := T.remove !tbl (build k); set k (match get k with [] -> [] | _ :: r -> r))
  done;
  !tbl, !model

let pairs model = List.sort compare (List.concat_map (fun (k, vs) -> List.map (fun v -> (k, v)) vs) model)
let norm l = List.sort compare (List.map (fun (t, vs) -> back t, vs) l)
let show_model m = String.concat "; " (List.map (fun (k, vs) -> show k ^ " -> [" ^ String.concat ";" (List.map string_of_int vs) ^ "]") m)

let () =
  for _ = 1 to 300 do
    let pool = Array.init (2 + pick 5) (fun _ -> gen 3) in
    let tbl, model = random_table pool in
    let what = "model " ^ show_model model in
    let seen = ref [] in
    T.iter (fun k v -> seen := (back k, v) :: !seen) tbl;
    note 0 (List.sort compare !seen = pairs model) what;
    note 1 (norm (T.list_of (T.map (fun _ v -> v * 3 + 1) tbl))
            = List.sort compare (List.map (fun (k, vs) -> k, List.map (fun v -> v * 3 + 1) vs) model)) what;
    let fm = T.fold_map (fun k v acc -> T.add acc k (v + 1000)) T.empty tbl in
    let fl = norm (T.list_of fm) in
    note 2 (List.sort compare (List.map (fun (k, vs) -> k, List.sort compare vs) fl)
            = List.sort compare (List.map (fun (k, vs) -> k, List.sort compare (List.map (fun v -> v + 1000) vs)) model)) what;
    note 3 (fl = List.sort compare (List.map (fun (k, vs) -> k, List.rev_map (fun v -> v + 1000) vs) model)) what;
    let rec drain t acc = if T.is_empty t then acc else let k, vs, t' = T.deletemax t in drain t' ((back k, vs) :: acc) in
    note 4 ((try List.sort compare (drain tbl []) with e -> [ (V (Printexc.to_string e), []) ]) = List.sort compare model) what;
    let tbl2, model2 = random_table pool in
    let want = List.sort compare (List.filter (fun (_, vs) -> vs <> [])
        (List.map (fun k -> k, (try List.assoc k model with Not_found -> []) @ (try List.assoc k model2 with Not_found -> []))
           (List.sort_uniq compare (List.map fst model @ List.map fst model2)))) in
    note 5 (norm (T.list_of (T.union tbl tbl2)) = want) (what ^ " | t2 " ^ show_model model2)
  done;
  Array.iteri (fun k name ->
      Printf.printf "%-48s %4d of %4d\n" name ok.(k) tried.(k);
      match first.(k) with None -> () | Some w -> Printf.printf "  first difference: %s\n" w) names;
  Printf.printf "deletemax of the empty table: %s\n"
    (try let _ = T.deletemax T.empty in "returned" with e -> "raised " ^ Printexc.to_string e);
  let t = T.add (T.add (T.add T.empty (build C) 1) (build (G C)) 2) (build C) 3 in
  T.print Lm_printf.stdstr t;
  Printf.printf "print of {c -> [3;1]; g{c} -> [2]}: %S\n" (Lm_printf.flush_stdstr ())
