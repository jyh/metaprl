(* Term_dtable (refiner/reflib), the table behind Itt_subtype's
   prove_subtypeT (the intro step for every subtype goal), against a model.  A small subtyping system is inserted the three ways
   itt theories insert one (insert, insert_left, insert_right), and
   `lookup t1 t2` is compared on every pair of ground terms up to depth 1
   with a model of the lookup written over plain trees: whole-goal entries
   first (newest first), then left-to-right entries keyed by t1, then
   right-to-left entries keyed by t2; a candidate whose subgoals fail is
   skipped.  The value of each entry is the derivation it builds, so the
   comparison is of derivations.  The test also records, for each answer,
   whether the derivation's conclusion is the pair that was asked, and
   which rules answer any ground pair.  Two of those records may be bugs:
   a left-to-right entry answers every goal whose left side matches, with
   the derivation of a different pair (as Itt_set's set rule would for
   {a: A | B} subtype C); and a right-to-left entry whose right side is a
   variable is keyed by the variable shape, so no ground goal reaches it
   (as Itt_void's void rule, void subtype 'a). *)
open Lm_symbol
open Term_sig
open Refiner.Refiner.Term
open Refiner.Refiner.TermType
open Refiner.Refiner.TermMan

(* Ground terms and patterns over a, b, c, v, s{x}, p{x; y}; M is a
   metavariable. *)
type t = O of string * t list | M of string

let rec show = function
  | M v -> "'" ^ v
  | O (o, []) -> o
  | O (o, ts) -> o ^ "{" ^ String.concat "; " (List.map show ts) ^ "}"

let rec build = function
  | M v -> mk_so_var_term (add v) [] []
  | O (o, ts) -> mk_simple_term (Opname.make_opname [ o ]) (List.map build ts)

let rec unbuild trm =
  if is_so_var_term trm then (let v, _, _ = dest_so_var trm in M (string_of_symbol v)) else
  let { term_op; term_terms } = dest_term trm in
  let o = List.hd (Opname.dest_opname (dest_op term_op).op_name) in
  O (o, List.map (fun b -> unbuild (dest_bterm b).bterm) term_terms)

(* The rules: name, kind, goal pair, subgoal pairs. *)
type kind = D | LR | RL
let rules = [
  "pair", D, (O ("p", [ M "A"; M "B" ]), O ("p", [ M "C"; M "D" ])), [ M "A", M "C"; M "B", M "D" ];
  "ab", D, (O ("a", []), O ("b", [])), [];
  "bc", D, (O ("b", []), O ("c", [])), [];
  "set", LR, (O ("s", [ M "A" ]), M "A"), [];
  "void", RL, (O ("v", []), M "A"), [];
  "ab2", D, (O ("a", []), O ("b", [])), [];
  "cross", D, (O ("p", [ M "A"; M "B" ]), O ("p", [ M "C"; M "D" ])), [ M "A", M "D"; M "B", M "C" ];
]

(* The value of an entry: its derivation, "name[t1 <= t2](subderivations)". *)
let value name subs (t1, t2) =
  name ^ "[" ^ show (unbuild t1) ^ " <= " ^ show (unbuild t2) ^ "]"
  ^ (if subs = [] then "" else "(" ^ String.concat ", " (List.map (fun (_, _, d) -> d) subs) ^ ")")

let table =
  let base =
    List.fold_left (fun base (name, kind, (g1, g2), subs) ->
        let l = (build g1, build g2) :: List.map (fun (x, y) -> build x, build y) subs in
        match kind with
        | D -> Term_dtable.insert base l (value name)
        | LR -> Term_dtable.insert_left base l (value name)
        | RL -> Term_dtable.insert_right base l (value name))
      Term_dtable.empty_dtable rules
  in
  Term_dtable.extract base

let lookup t1 t2 = try Some (Term_dtable.lookup table (build t1) (build t2)) with Not_found -> None

(* The model. *)
let rec matches env p t =
  match p, t with
  | M v, _ -> (match List.assoc_opt v env with Some u -> if u = t then Some env else None | None -> Some ((v, t) :: env))
  | O (o, ps), O (o', ts) when o = o' && List.length ps = List.length ts ->
      List.fold_left2 (fun e p t -> match e with None -> None | Some e -> matches e p t) (Some env) ps ts
  | _ -> None
let rec inst env = function M v -> List.assoc v env | O (o, ts) -> O (o, List.map (inst env) ts)
(* The key a table uses: the head operator and arity, or "var" for a
   metavariable. *)
let key = function M _ -> "var" | O (o, ts) -> o ^ "/" ^ string_of_int (List.length ts)

(* Entries as the table holds them: each insert_left / insert_right adds a
   one-sided entry and a whole-goal entry, newest first. *)
type entry = { name : string; side : kind; g1 : t; g2 : t; subs : (t * t) list }
let entries =
  List.rev (List.concat_map (fun (name, kind, (g1, g2), subs) ->
      let whole = { name; side = D; g1; g2; subs } in
      match kind with
      | D -> [ whole ]
      | LR | RL -> [ { name; side = kind; g1; g2; subs }; whole ]) rules)
  (* one-sided and whole-goal entries sit in different tables, so only the
     order within one side matters *)

let rec model t1 t2 =
  let try_entries side cands =
    let rec go = function
      | [] -> None
      | e :: rest ->
          let env =
            match side with
            | D -> (match matches [] e.g1 t1 with Some env -> matches env e.g2 t2 | None -> None)
            | LR -> matches [] e.g1 t1
            | RL -> matches [] e.g2 t2
          in
          (match env with
           | None -> go rest
           | Some env ->
               (* a one-sided entry concludes the pair its pattern gives *)
               let c1 = (match side with RL -> (try inst env e.g1 with Not_found -> t1) | _ -> t1)
               and c2 = (match side with LR -> (try inst env e.g2 with Not_found -> t2) | _ -> t2) in
               let subs = List.map (fun (x, y) -> (try Some (inst env x, inst env y) with Not_found -> None)) e.subs in
               if List.mem None subs then go rest else
               let ds = List.map (fun s -> match s with Some (x, y) -> model x y | None -> None) subs in
               if List.mem None ds then go rest
               else
                 Some (e.name ^ "[" ^ show c1 ^ " <= " ^ show c2 ^ "]"
                       ^ (if ds = [] then "" else "(" ^ String.concat ", " (List.filter_map Fun.id ds) ^ ")")))
    in
    go cands
  in
  let on side k f = List.filter (fun e -> e.side = side && f e = k) entries in
  match try_entries D (List.filter (fun e -> e.side = D && key e.g1 = key t1 && key e.g2 = key t2) entries) with
  | Some d -> Some d
  | None ->
      (match try_entries LR (on LR (key t1) (fun e -> key e.g1)) with
       | Some d -> Some d
       | None -> try_entries RL (on RL (key t2) (fun e -> key e.g2)))

let rec terms d =
  let leaves = [ O ("a", []); O ("b", []); O ("c", []); O ("v", []) ] in
  if d = 0 then leaves
  else
    let sub = terms (d - 1) in
    leaves @ List.map (fun x -> O ("s", [ x ])) sub @ List.concat_map (fun x -> List.map (fun y -> O ("p", [ x; y ])) sub) sub

(* The conclusion a derivation states: the pair inside its first [...]. *)
let conclusion d =
  let i = String.index d '[' and j = String.index d ']' in
  String.sub d (i + 1) (j - i - 1)

let () =
  let ts = terms 1 in
  let n = ref 0 and agree = ref 0 and found = ref 0 and other_pair = ref 0 in
  let first = ref None and first_other = ref None in
  let used = Hashtbl.create 8 in
  List.iter (fun t1 -> List.iter (fun t2 ->
      incr n;
      let r = lookup t1 t2 and m = model t1 t2 in
      if r = m then incr agree else if !first = None then first := Some (t1, t2, r, m);
      match r with
      | None -> ()
      | Some d ->
          incr found;
          List.iter (fun (name, _, _, _) ->
              if String.length d >= String.length name && String.sub d 0 (String.length name) = name then
                Hashtbl.replace used name ()) rules;
          if conclusion d <> show t1 ^ " <= " ^ show t2 then begin
            incr other_pair;
            if !first_other = None then first_other := Some (t1, t2, d)
          end) ts) ts;
  let opt = function None -> "Not_found" | Some d -> d in
  Printf.printf "pairs of terms up to depth 1: %d; the table and the model agree on %d\n" !n !agree;
  (match !first with
   | None -> ()
   | Some (t1, t2, r, m) -> Printf.printf "  first difference: %s <= %s: table %s, model %s\n" (show t1) (show t2) (opt r) (opt m));
  Printf.printf "lookups that answer: %d\n" !found;
  Printf.printf "rules that answer some pair as the outermost step: %s\n"
    (String.concat ", " (List.filter (fun (name, _, _, _) -> Hashtbl.mem used name) rules |> List.map (fun (n, _, _, _) -> n)));
  Printf.printf "rules that answer no pair: %s\n"
    (String.concat ", " (List.filter (fun (name, _, _, _) -> not (Hashtbl.mem used name)) rules |> List.map (fun (n, _, _, _) -> n)));
  (* Behaviour that the test records and that may be a bug. *)
  Printf.printf "answers whose derivation concludes a different pair than the one asked: %d\n" !other_pair;
  (match !first_other with
   | None -> ()
   | Some (t1, t2, d) -> Printf.printf "  first: %s <= %s answered by %s\n" (show t1) (show t2) d);
  List.iter (fun (t1, t2) -> Printf.printf "lookup %s <= %s: %s\n" (show t1) (show t2) (opt (lookup t1 t2)))
    [ O ("v", []), O ("a", []);  O ("v", []), M "X";  O ("s", [ O ("a", []) ]), O ("a", []);
      O ("s", [ O ("a", []) ]), O ("c", []);  O ("a", []), O ("b", []);  O ("a", []), O ("c", []) ]
