(* Term_match_table (refiner/reflib), the pattern tables behind 26
   resources (reduce, the decision tables, typeinf).  On 600 random tables
   of 1-6 patterns over f{_;_}, g{_}, c and pattern variables 'a 'b (a
   repeated variable must match equal subterms; a third of the tables also
   hold f{'a; 'a}, looked up with f{u; u} or f{u; v}), each looked up with
   a random closed term, against first-order matching as the model:
     - lookup_all returns exactly the values whose pattern matches;
     - lookup is None exactly when none matches, else a matching value;
     - the pattern lookup chooses is never strictly more general than
       another matching pattern ("the most specific pattern match");
     - among identical patterns, the most recently added value wins
       ("most recently added items will be preferred in lookups").
   It prints each count with how many tables it was tried on, and the
   first difference.  The generator is a fixed linear congruential
   sequence, not Random. *)
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan

let state = ref 31
let next () = state := (!state * 1103515245 + 12345) land 0x7fffffff; !state lsr 8
let pick n = next () mod n

type p = PV of string | F of p * p | G of p | C
let op s = Opname.make_opname [ s ]
let rec build = function
  | PV v -> mk_so_var_term (Lm_symbol.add v) [] []
  | C -> mk_simple_term (op "c") []
  | G a -> mk_simple_term (op "g") [ build a ]
  | F (a, b) -> mk_simple_term (op "f") [ build a; build b ]
let rec show = function
  | PV v -> "'" ^ v | C -> "c" | G a -> "g{" ^ show a ^ "}" | F (a, b) -> "f{" ^ show a ^ "; " ^ show b ^ "}"
let rec gpat d =
  if d = 0 || pick 3 = 0 then (if pick 2 = 0 then PV [| "a"; "b" |].(pick 2) else C)
  else if pick 2 = 0 then G (gpat (d - 1)) else F (gpat (d - 1), gpat (d - 1))
let rec gterm d = if d = 0 || pick 3 = 0 then C else if pick 2 = 0 then G (gterm (d - 1)) else F (gterm (d - 1), gterm (d - 1))

(* First-order matching; a pattern variable is bound once.  On patterns,
   a target variable is a constant: m p q succeeds when p is at least as
   general as q. *)
let rec m s p t =
  match p, t with
  | PV v, _ -> (match List.assoc_opt v s with None -> Some ((v, t) :: s) | Some u -> if u = t then Some s else None)
  | C, C -> Some s
  | G a, G b -> m s a b
  | F (a1, a2), F (b1, b2) -> (match m s a1 b1 with None -> None | Some s -> m s a2 b2)
  | _ -> None
let matches p t = m [] p t <> None
let strictly_more_general p q = matches p q && not (matches q p)
let rec repeated = function
  | p -> let rec vars = function PV v -> [ v ] | C -> [] | G a -> vars a | F (a, b) -> vars a @ vars b in
         let vs = vars p in List.length vs <> List.length (List.sort_uniq compare vs)

let tried = Array.make 4 0 and ok = Array.make 4 0 and first = Array.make 4 None
let note k b what = tried.(k) <- tried.(k) + 1; if b then ok.(k) <- ok.(k) + 1 else if first.(k) = None then first.(k) <- Some what

let () =
  let n = 600 in
  let any = ref 0 and several = ref 0 and rep = ref 0 in
  for _ = 1 to n do
    let pats = List.init (1 + pick 6) (fun _ -> gpat 3) in
    (* sometimes add a pattern twice, to see which value wins *)
    let pats = if pick 3 = 0 then pats @ [ List.nth pats (pick (List.length pats)) ] else pats in
    (* and sometimes f{'a; 'a}, with a term that may have equal halves *)
    let dup = pick 3 = 0 in
    let pats = if dup then pats @ [ F (PV "a", PV "a") ] else pats in
    let indexed = List.mapi (fun k p -> k, p) pats in
    let tbl = List.fold_left (fun t (k, p) -> Term_match_table.add_item t (build p) k) Term_match_table.empty_table indexed in
    let t = if dup then (let u = gterm 2 in F (u, if pick 2 = 0 then u else gterm 2)) else gterm 4 in
    let what = Printf.sprintf "patterns [%s], term %s" (String.concat "; " (List.map show pats)) (show t) in
    let want = List.filter_map (fun (k, p) -> if matches p t then Some k else None) indexed in
    if want <> [] then incr any;
    if List.length want > 1 then incr several;
    if List.exists (fun k -> repeated (List.assoc k indexed)) want then incr rep;
    let rec all acc l = match l () with None -> acc | Some (x, l) -> all (x :: acc) l in
    let got = try all [] (Term_match_table.lookup_all tbl Term_match_table.select_all (build t)) with _ -> [ -1 ] in
    note 0 (List.sort compare got = List.sort compare want) what;
    let one = try Term_match_table.lookup tbl Term_match_table.select_all (build t) with _ -> Some (-1) in
    note 1 (match one with None -> want = [] | Some k -> List.mem k want) what;
    match one with
    | Some k when List.mem k want ->
        let pk = List.assoc k indexed in
        note 2 (not (List.exists (fun j -> strictly_more_general pk (List.assoc j indexed)) want)) what;
        let same = List.filter (fun (_, p) -> p = pk) indexed in
        if List.length same > 1 then note 3 (k = List.fold_left (fun a (j, _) -> max a j) (-1) same) what
    | _ -> ()
  done;
  Printf.printf "%d tables: %d with a matching pattern, %d with several, %d where a repeated variable matches\n" n !any !several !rep;
  List.iteri (fun k name ->
      Printf.printf "%-44s %4d of %4d\n" name ok.(k) tried.(k);
      match first.(k) with None -> () | Some w -> Printf.printf "  first difference: %s\n" w)
    [ "lookup_all = the matching values"; "lookup: None iff no match, else a match";
      "lookup's pattern is not strictly more general"; "identical patterns: the newest value wins" ]
