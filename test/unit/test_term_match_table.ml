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

(* lookup_bucket and lookup_rmap, against the same model.  A pattern is
   "most specific" among the matching ones when no other matching pattern
   is strictly less general.
     - lookup_bucket is None exactly when nothing matches, and otherwise is
       the values of every entry added with one most specific pattern, a
       pattern being the same up to the names of its variables ('a and 'b
       share a bucket);
     - lookup_rmap (a table of pattern -> contracta, here g{'v} for each
       variable 'v of the pattern, or c) is None exactly when nothing
       matches, and otherwise is a most specific pattern's newest value
       with its contracta instantiated by the match. *)
let rec pvars = function PV v -> [ v ] | C -> [] | G a -> pvars a | F (a, b) -> pvars a @ pvars b
(* A pattern up to the names of its variables. *)
let canon p =
  let names = ref [] in
  let rec go = function
    | PV v -> (match List.assoc_opt v !names with Some i -> PV (string_of_int i) | None -> let i = List.length !names in names := (v, i) :: !names; PV (string_of_int i))
    | C -> C | G a -> G (go a) | F (a, b) -> let a = go a in F (a, go b) in
  go p
let contracta p = match List.sort_uniq Stdlib.compare (pvars p) with [] -> [ C ] | vs -> List.map (fun v -> G (PV v)) vs
let rec inst s = function PV v -> List.assoc v s | C -> C | G a -> G (inst s a) | F (a, b) -> F (inst s a, inst s b)
let rec of_term t =
  let { Term_sig.term_op; term_terms } = dest_term t in
  match Opname.dest_opname (dest_op term_op).Term_sig.op_name, List.map (fun b -> of_term (dest_bterm b).Term_sig.bterm) term_terms with
  | [ "c" ], [] -> C | [ "g" ], [ a ] -> G a | [ "f" ], [ a; b ] -> F (a, b) | _ -> failwith "of_term"

let () =
  state := 4711;
  let n = 600 in
  let bt = ref 0 and bok = ref 0 and bfirst = ref None and rt = ref 0 and rok = ref 0 and rfirst = ref None in
  for _ = 1 to n do
    let pats = List.init (1 + pick 6) (fun _ -> gpat 3) in
    let pats = if pick 2 = 0 then pats @ [ List.nth pats (pick (List.length pats)) ] else pats in
    let indexed = List.mapi (fun k p -> k, p) pats in
    let t = gterm 4 in
    let what = Printf.sprintf "patterns [%s], term %s" (String.concat "; " (List.map show pats)) (show t) in
    let matching = List.filter (fun (_, p) -> matches p t) indexed in
    let specific = List.filter (fun (_, p) -> not (List.exists (fun (_, q) -> strictly_more_general p q) matching)) matching in
    (* lookup_bucket *)
    let tbl = List.fold_left (fun tb (k, p) -> Term_match_table.add_item tb (build p) k) Term_match_table.empty_table indexed in
    incr bt;
    let got = try Term_match_table.lookup_bucket tbl Term_match_table.select_all (build t) with _ -> Some [ -1 ] in
    let ok = match got with
      | None -> matching = []
      | Some vs ->
          List.exists (fun (_, p) -> List.sort compare vs = List.sort compare (List.filter_map (fun (k, q) -> if canon q = canon p then Some k else None) indexed)) specific in
    if ok then incr bok else if !bfirst = None then bfirst := Some what;
    (* lookup_rmap *)
    let mt = List.fold_left (fun tb (k, p) -> Term_match_table.add_map tb (build p) (List.map build (contracta p)) k) Term_match_table.empty_map_table indexed in
    incr rt;
    let got = try Option.map (fun (cs, k) -> List.map of_term cs, k) (Term_match_table.lookup_rmap mt Term_match_table.select_all (build t)) with _ -> Some ([], -1) in
    let ok = match got with
      | None -> matching = []
      | Some (cs, k) ->
          (match List.assoc_opt k indexed with
           | Some p when List.mem_assoc k specific ->
               let newest = List.fold_left (fun a (j, q) -> if q = p then max a j else a) (-1) indexed in
               (match m [] p t with Some s -> k = newest && cs = List.map (inst s) (contracta p) | None -> false)
           | _ -> false) in
    if ok then incr rok else if !rfirst = None then rfirst := Some what
  done;
  Printf.printf "%-44s %4d of %4d\n" "lookup_bucket: a most specific pattern's values" !bok !bt;
  (match !bfirst with None -> () | Some w -> Printf.printf "  first difference: %s\n" w);
  Printf.printf "%-44s %4d of %4d\n" "lookup_rmap: its contracta, instantiated" !rok !rt;
  match !rfirst with None -> () | Some w -> Printf.printf "  first difference: %s\n" w
