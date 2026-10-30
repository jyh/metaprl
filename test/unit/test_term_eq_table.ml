(* Term_eq_table (refiner/reflib), the term-keyed tables of proof_boot,
   itt_supinf and itt_int_arith.  Its keys are hash-consed terms
   (TermNorm.add), and the hash-consing compares bound variables by NAME
   (term_hash.ml: compare_bterm_header, bvars1 = bvars2), so a key is a term
   up to syntactic identity, not up to alpha equality: lam x.x and lam u.u
   are two keys.  On 400 random tables, each built by 1-25 random
   operations (add, replace with 0-2 values, remove) on keys drawn from a
   small pool of terms over c, g{_}, f{_;_}, lam x._ and the variables
   x, y, z, each key used either as written or with its bound variables
   renamed (an alpha-equal, differently named term), against a model: an
   association list keyed by the term as written, each key's values newest
   first:
     - after every operation, find_all / find / mem on both forms of every
       pool key agree with the model;
     - at the end, length is the number of keys and list_of holds the
       model's keys with the model's value lists.
   It also counts the lookups of a key whose alpha-equal, differently
   named form held values in the model (each must find nothing).  It
   prints each count with how many checks were made, and the first
   difference.  The generator is a fixed linear congruential sequence,
   not Random. *)
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

let names = [| "find_all = the model's values"; "find = the newest value, else Not_found";
               "mem = the key has values"; "length = the number of keys";
               "list_of = the model's keys and values" |]
let tried = Array.make 5 0 and ok = Array.make 5 0 and first = Array.make 5 None
let note k b what = tried.(k) <- tried.(k) + 1; if b then ok.(k) <- ok.(k) + 1 else if first.(k) = None then first.(k) <- Some what

let () =
  let n = 400 and shared = ref 0 and apart = ref 0 in
  for _ = 1 to n do
    let pool = Array.init (2 + pick 5) (fun _ -> gen 3) in
    let tbl = ref T.empty and model = ref [] and ops = ref [] in
    let get k = try List.assoc k !model with Not_found -> [] in
    let set k vs = model := (if vs = [] then [] else [ k, vs ]) @ List.remove_assoc k !model in
    for _ = 1 to 1 + pick 25 do
      let key = pool.(pick (Array.length pool)) in
      let kt = variant key in let k = kt in
      (match pick 4 with
       | 0 | 1 -> let v = pick 100 in
           tbl := T.add !tbl (build kt) v; set k (v :: get k); ops := Printf.sprintf "add %s %d" (show kt) v :: !ops
       | 2 -> let vs = List.init (pick 3) (fun _ -> pick 100) in
           tbl := T.replace !tbl (build kt) vs; set k vs;
           ops := Printf.sprintf "replace %s [%s]" (show kt) (String.concat ";" (List.map string_of_int vs)) :: !ops
       | _ -> tbl := T.remove !tbl (build kt);
           set k (match get k with [] -> [] | _ :: r -> r); ops := Printf.sprintf "remove %s" (show kt) :: !ops);
      Array.iter (fun key ->
          List.iter (fun kt ->
              let want = get kt in
              let other = if kt = key then rename 0 [] key else key in
              if want = [] && other <> kt && get other <> [] then incr apart;
              let what () = Printf.sprintf "after [%s], key %s, model [%s]" (String.concat "; " (List.rev !ops)) (show kt)
                  (String.concat ";" (List.map string_of_int want)) in
              let got = try T.find_all !tbl (build kt) with e -> [ -1000 - String.length (Printexc.to_string e) ] in
              note 0 (got = want) (what () ^ ", got [" ^ String.concat ";" (List.map string_of_int got) ^ "]");
              let one = try Some (T.find !tbl (build kt)) with Not_found -> None in
              note 1 (one = (match want with [] -> None | v :: _ -> Some v)) (what ());
              note 2 (T.mem !tbl (build kt) = (want <> [])) (what ()))
            (List.sort_uniq compare [ key; rename 0 [] key ])) pool
    done;
    if Array.exists (fun k -> rename 0 [] k <> k) pool then incr shared;
    let what = Printf.sprintf "after [%s]" (String.concat "; " (List.rev !ops)) in
    note 3 (T.length !tbl = List.length !model) (Printf.sprintf "%s: length %d, model %d keys" what (T.length !tbl) (List.length !model));
    let got = List.sort compare (List.map (fun (t, vs) -> back t, vs) (T.list_of !tbl)) in
    note 4 (got = List.sort compare !model) what
  done;
  Printf.printf "%d tables, %d with a key that has a binder (so two forms)\n" n !shared;
  Printf.printf "%d lookups of a key whose alpha-equal, differently named form held values\n" !apart;
  Array.iteri (fun k name ->
      Printf.printf "%-42s %5d of %5d\n" name ok.(k) tried.(k);
      match first.(k) with None -> () | Some w -> Printf.printf "  first difference: %s\n" w) names
