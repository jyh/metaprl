(* Term_match_table on sequent patterns (refiner/reflib), whose code
   (compile_sequent, execute_hyps, execute_hyps_both) no unit test reached
   (2026-11-02 profile).  A sequent pattern has at most one context; its
   hypotheses sit before it (Left), after it (Right), on both sides (Both),
   or there is none (Exact).  On 600 tables of 1-5 such patterns,
     sequent[s]{ x1: P1; ...; <H>; ...; xn: Pn >- Q },
   with P, Q first-order patterns over f{_;_}, g{_}, c and variables 'a 'b
   (a variable bound once across the whole pattern), each looked up with a
   sequent of closed hypotheses (half the time an instance of one of the
   patterns, with 0-2 hypotheses for its context), against a model -- a context matches
   any number of hypotheses, the others match in order:
     - lookup_all returns exactly the values whose pattern matches;
     - lookup is None exactly when none matches, and otherwise a match.
   The generator is a fixed linear congruential sequence, not Random. *)
open Term_sig
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan

let state = ref 2121
let next () = state := (!state * 1103515245 + 12345) land 0x7fffffff; !state lsr 8
let pick n = next () mod n

type p = PV of string | F of p * p | G of p | C
let rec gpat d =
  if d = 0 || pick 3 = 0 then (if pick 3 = 0 then PV [| "a"; "b" |].(pick 2) else C)
  else if pick 2 = 0 then G (gpat (d - 1)) else F (gpat (d - 1), gpat (d - 1))
let rec gterm d = if d = 0 || pick 3 = 0 then C else if pick 2 = 0 then G (gterm (d - 1)) else F (gterm (d - 1), gterm (d - 1))
let rec show = function PV v -> "'" ^ v | C -> "c" | G a -> "g{" ^ show a ^ "}" | F (a, b) -> "f{" ^ show a ^ "; " ^ show b ^ "}"

(* A sequent pattern: hypotheses before the context, whether there is
   one, hypotheses after it, the conclusion. *)
type sp = { before : p list; ctx : bool; after : p list; concl : p }
let gsp () =
  let n () = List.init (pick 3) (fun _ -> gpat 2) in
  let before = n () and ctx = pick 3 > 0 in
  { before; ctx; after = (if ctx then n () else []); concl = gpat 2 }
let sshow s =
  let hs = List.map show s.before @ (if s.ctx then [ "<H>" ] else []) @ List.map show s.after in
  "{ " ^ String.concat "; " hs ^ " >- " ^ show s.concl ^ " }"

let rec m s p t =
  match p, t with
  | PV v, _ -> (match List.assoc_opt v s with None -> Some ((v, t) :: s) | Some u -> if u = t then Some s else None)
  | C, C -> Some s
  | G a, G b -> m s a b
  | F (a1, a2), F (b1, b2) -> (match m s a1 b1 with None -> None | Some s -> m s a2 b2)
  | _ -> None
let rec ml s ps ts = match ps, ts with
  | [], [] -> Some s
  | p :: ps, t :: ts -> (match m s p t with None -> None | Some s -> ml s ps ts)
  | _ -> None
let matches sp (hyps, concl) =
  let n = List.length hyps and b = List.length sp.before and a = List.length sp.after in
  let ok_len = if sp.ctx then n >= b + a else n = b + a in
  ok_len &&
  (let first = List.filteri (fun i _ -> i < b) hyps and last = List.filteri (fun i _ -> i >= n - a) hyps in
   match ml [] sp.before first with
   | None -> false
   | Some s -> (match ml s sp.after last with None -> false | Some s -> m s sp.concl concl <> None))

let op s = Opname.make_opname [ s ]
let rec build = function
  | PV v -> mk_so_var_term (Lm_symbol.add v) [] []
  | C -> mk_simple_term (op "c") []
  | G a -> mk_simple_term (op "g") [ build a ]
  | F (a, b) -> mk_simple_term (op "f") [ build a; build b ]
let seq hyps concl = mk_sequent_term { sequent_args = mk_simple_term (op "s") []; sequent_hyps = SeqHyp.of_list hyps; sequent_concl = concl }
let build_sp sp =
  let hyp i p = Hypothesis (Lm_symbol.add (Printf.sprintf "x%d" i), build p) in
  seq (List.mapi hyp sp.before @ (if sp.ctx then [ Context (Lm_symbol.add "H", [], []) ] else [])
       @ List.mapi (fun i p -> hyp (i + 10) p) sp.after) (build sp.concl)
let build_t (hyps, concl) = seq (List.mapi (fun i t -> Hypothesis (Lm_symbol.add (Printf.sprintf "h%d" i), build t)) hyps) (build concl)

let () =
  let n = 600 in
  let tried = Array.make 2 0 and ok = Array.make 2 0 and first = Array.make 2 None and any = ref 0 and several = ref 0 in
  let kinds = Hashtbl.create 4 in
  let note k b what = tried.(k) <- tried.(k) + 1; if b then ok.(k) <- ok.(k) + 1 else if first.(k) = None then first.(k) <- Some what in
  for _ = 1 to n do
    let pats = List.init (1 + pick 5) (fun _ -> gsp ()) in
    List.iter (fun sp ->
        let k = match sp.ctx, sp.before, sp.after with
          | false, _, _ -> "exact" | true, _ :: _, _ :: _ -> "both" | true, _ :: _, [] -> "left" | true, [], _ :: _ -> "right" | true, [], [] -> "context only" in
        Hashtbl.replace kinds k (1 + try Hashtbl.find kinds k with Not_found -> 0)) pats;
    let indexed = List.mapi (fun k p -> k, p) pats in
    let tbl = List.fold_left (fun tb (k, p) -> Term_match_table.add_item tb (build_sp p) k) Term_match_table.empty_table indexed in
    (* half the time an instance of one of the patterns, so matches are common *)
    let t =
      if pick 2 = 0 then List.init (pick 5) (fun _ -> gterm 2), gterm 2
      else
        let sp = List.nth pats (pick (List.length pats)) in
        let a = gterm 2 and b = gterm 2 in
        let rec inst = function PV "a" -> a | PV _ -> b | C -> C | G x -> G (inst x) | F (x, y) -> F (inst x, inst y) in
        List.map inst sp.before @ (if sp.ctx then List.init (pick 3) (fun _ -> gterm 2) else []) @ List.map inst sp.after, inst sp.concl in
    let what = Printf.sprintf "patterns [%s], sequent { %s >- %s }" (String.concat "; " (List.map sshow pats))
        (String.concat "; " (List.map show (fst t))) (show (snd t)) in
    let want = List.filter_map (fun (k, p) -> if matches p t then Some k else None) indexed in
    if want <> [] then incr any;
    if List.length want > 1 then incr several;
    let rec all acc l = match l () with None -> acc | Some (x, l) -> all (x :: acc) l in
    let got = try all [] (Term_match_table.lookup_all tbl Term_match_table.select_all (build_t t)) with _ -> [ -1 ] in
    note 0 (List.sort compare got = List.sort compare want) what;
    let one = try Term_match_table.lookup tbl Term_match_table.select_all (build_t t) with _ -> Some (-1) in
    note 1 (match one with None -> want = [] | Some k -> List.mem k want) what
  done;
  Printf.printf "%d tables: %d with a matching pattern, %d with several\n" n !any !several;
  Printf.printf "patterns by kind:%s\n" (String.concat "" (List.map (fun k -> Printf.sprintf " %s %d" k (try Hashtbl.find kinds k with Not_found -> 0)) [ "exact"; "left"; "right"; "both"; "context only" ]));
  List.iteri (fun k name ->
      Printf.printf "%-44s %4d of %4d\n" name ok.(k) tried.(k);
      match first.(k) with None -> () | Some w -> Printf.printf "  first difference: %s\n" w)
    [ "lookup_all = the matching values"; "lookup: None iff no match, else a match" ]
