(* The refiner's rewrite combinators (refiner/refiner/refine.ml), which no
   unit test reached (2026-11-02 profile: refine.ml at 0 %).  Three
   rewrites are created in a null refiner with create_rewrite
     swap  f{'a; 'b} --> f{'b; 'a}      ung  g{'a} --> 'a      wrap  c --> g{c}
   and combined at random with andthenrw, orelserw, rwhigher and rwaddr;
   each combination is applied, through rwtactic and refine, to 300 random
   closed terms over f, g and c, and the goal it leaves is compared with a
   model:
     andthenrw r s   r, then s on the result; fails if either fails
     orelserw r s    r, or s if r fails
     rwhigher r      r at the root, or else at the outermost subterms where
                     it applies; where it applies nowhere it leaves the term
                     as it is, and so never fails (measured: the .mli says
                     only "the outermost where it does not fail")
     rwaddr a r      r at the subterm at address a; fails if a is not there
   The generator is a fixed linear congruential sequence, not Random. *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.Refine

let state = ref 7171
let next () = state := (!state * 1103515245 + 12345) land 0x7fffffff; !state lsr 8
let pick n = next () mod n

type d = C | G of d | F of d * d
let rec gen depth = if depth = 0 || pick 3 = 0 then C else if pick 2 = 0 then G (gen (depth - 1)) else F (gen (depth - 1), gen (depth - 1))
let rec show = function C -> "c" | G a -> "g{" ^ show a ^ "}" | F (a, b) -> "f{" ^ show a ^ "; " ^ show b ^ "}"

type r = Swap | Ung | Wrap | Then of r * r | Else of r * r | Higher of r | Addr of int list * r
let rec gr depth =
  match pick (if depth = 0 then 3 else 7) with
  | 0 -> Swap | 1 -> Ung | 2 -> Wrap
  | 3 -> Then (gr (depth - 1), gr (depth - 1))
  | 4 -> Else (gr (depth - 1), gr (depth - 1))
  | 5 -> Higher (gr (depth - 1))
  | _ -> Addr (List.init (1 + pick 2) (fun _ -> 1 + pick 2), gr (depth - 1))
let rec rshow = function
  | Swap -> "swap" | Ung -> "ung" | Wrap -> "wrap"
  | Then (a, b) -> "(" ^ rshow a ^ " then " ^ rshow b ^ ")" | Else (a, b) -> "(" ^ rshow a ^ " orelse " ^ rshow b ^ ")"
  | Higher a -> "higher " ^ rshow a | Addr (p, a) -> "addr [" ^ String.concat ";" (List.map string_of_int p) ^ "] " ^ rshow a

(* The model. *)
let rec model r t =
  match r, t with
  | Swap, F (a, b) -> Some (F (b, a))
  | Ung, G a -> Some a
  | Wrap, C -> Some (G C)
  | (Swap | Ung | Wrap), _ -> None
  | Then (a, b), _ -> Option.bind (model a t) (model b)
  | Else (a, b), _ -> (match model a t with Some t' -> Some t' | None -> model b t)
  | Higher a, _ ->
      (* never fails: where a applies nowhere the term is left as it is *)
      let rec hi t =
        match model a t with
        | Some t' -> t'
        | None -> (match t with C -> C | G x -> G (hi x) | F (x, y) -> F (hi x, hi y)) in
      Some (hi t)
  | Addr (p, a), _ ->
      let rec at p t =
        match p, t with
        | [], _ -> model a t
        | 1 :: p, G x -> Option.map (fun x -> G x) (at p x)
        | 1 :: p, F (x, y) -> Option.map (fun x -> F (x, y)) (at p x)
        | 2 :: p, F (x, y) -> Option.map (fun y -> F (x, y)) (at p y)
        | _ -> None in
      at p t

let op s = Opname.make_opname [ s ]
let rec build = function C -> mk_simple_term (op "c") [] | G a -> mk_simple_term (op "g") [ build a ] | F (a, b) -> mk_simple_term (op "f") [ build a; build b ]
let rec back t =
  let { Term_sig.term_op; term_terms } = dest_term t in
  match Opname.dest_opname (dest_op term_op).Term_sig.op_name, List.map (fun b -> back (dest_bterm b).Term_sig.bterm) term_terms with
  | [ "c" ], [] -> C | [ "g" ], [ a ] -> G a | [ "f" ], [ a; b ] -> F (a, b) | _ -> failwith "back"

let refiner = null_refiner "test_refine_rw"
let sov x = mk_so_var_term (Lm_symbol.add x) [] []
let prim name redex contractum = match create_rewrite refiner name redex contractum with PrimRW r -> r | CondRW _ -> failwith "cond"
let swap = prim "swap" (mk_simple_term (op "f") [ sov "a"; sov "b" ]) (mk_simple_term (op "f") [ sov "b"; sov "a" ])
let ung = prim "ung" (mk_simple_term (op "g") [ sov "a" ]) (sov "a")
let wrap = prim "wrap" (build C) (build (G C))
let rec to_rw = function
  | Swap -> swap | Ung -> ung | Wrap -> wrap
  | Then (a, b) -> andthenrw (to_rw a) (to_rw b) | Else (a, b) -> orelserw (to_rw a) (to_rw b)
  | Higher a -> rwhigher (to_rw a)
  | Addr (p, a) -> rwaddr (TermAddr.make_address (List.map (fun i -> Term_addr_sig.Subterm i) p)) (to_rw a)

let apply r t =
  try
    match refine any_sentinal (rwtactic 0 (to_rw r)) (mk_msequent (build t) []) with
    | [ m ], _ -> Some (back (msequent_goal m))
    | _ -> None
  with
  | Failure s when s = "back" -> failwith "the goal is not a term over f, g, c"
  | _ -> None (* the refiner refused the rewrite *)

let () =
  let rules = 60 and terms = 5 in
  let tried = ref 0 and agree = ref 0 and rewrote = ref 0 and first = ref None in
  let kinds = Hashtbl.create 8 in
  for _ = 1 to rules do
    let r = gr 3 in
    for _ = 1 to terms do
      let t = gen 4 in
      incr tried;
      let want = model r t and got = apply r t in
      if got <> None then incr rewrote;
      let rec top = function Swap | Ung | Wrap -> "primitive" | Then _ -> "andthenrw" | Else _ -> "orelserw" | Higher _ -> "rwhigher" | Addr _ -> "rwaddr" in
      let k = top r in
      let a, b = try Hashtbl.find kinds k with Not_found -> 0, 0 in
      Hashtbl.replace kinds k (a + 1, if want = got then b + 1 else b);
      if want = got then incr agree
      else if !first = None then
        first := Some (rshow r, show t, (match want with None -> "fails" | Some x -> show x), (match got with None -> "fails" | Some x -> show x))
    done
  done;
  Printf.printf "%d rewrites x %d terms: %d cases, %d rewritten\n" rules terms !tried !rewrote;
  List.iter (fun k -> let a, b = try Hashtbl.find kinds k with Not_found -> 0, 0 in Printf.printf "  %-10s %3d of %3d agree with the model\n" k b a)
    [ "primitive"; "andthenrw"; "orelserw"; "rwhigher"; "rwaddr" ];
  Printf.printf "all: %d of %d agree with the model\n" !agree !tried;
  match !first with None -> () | Some (r, t, w, g) -> Printf.printf "  first difference: %s on %s: model %s, got %s\n" r t w g
