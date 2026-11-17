(* Refine.extract_term and compute_dependencies for theorems in a refiner
   that JOINED the primitives' refiner (through its label, twice), so that
   find_of_refiner walks a label and a pair to find the primitives; no test
   reached those arms (2026-11-16 rank).  test_refine_extract's generator,
   model and primitives, with the primitives in a refiner of their own:
   60 random theorems, half of them delayed; then one extract printed, and
   a theorem in a refiner that holds none of its primitives (refused, by
   the sentinel check before any lookup).
   The expected file is the output of the code as written (2026-11-16),
   never typed. *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.Refine

let state = ref 3131
let next () = state := (!state * 1103515245 + 12345) land 0x7fffffff; !state lsr 8
let pick n = next () mod n

type p = C | G of p | F of p * p | V of string
let rec gen depth avail =
  (* a pattern and the variables still unused *)
  match pick 5 with
  | 0 when avail <> [] -> V (List.hd avail), List.tl avail
  | _ when depth = 0 -> C, avail
  | 1 | 2 -> let a, avail = gen (depth - 1) avail in G a, avail
  | 3 -> let a, avail = gen (depth - 1) avail in let b, avail = gen (depth - 1) avail in F (a, b), avail
  | _ -> C, avail
let rec vars = function C -> [] | V x -> [ x ] | G a -> vars a | F (a, b) -> vars a @ vars b
let rec show = function C -> "c" | V x -> "'" ^ x | G a -> "g{" ^ show a ^ "}" | F (a, b) -> "f{" ^ show a ^ "; " ^ show b ^ "}"

let op s = Opname.make_opname [ s ]
let rec term = function
  | C -> mk_simple_term (op "c") [] | G a -> mk_simple_term (op "g") [ term a ]
  | F (a, b) -> mk_simple_term (op "f") [ term a; term b ] | V x -> mk_so_var_term (Lm_symbol.add x) [] []
let show_t t = Simple_print.SimplePrint.string_of_term t

(* the model *)
let rec model args = function
  | C -> mk_simple_term (op "k") [] | G a -> mk_simple_term (op "q") [ model args a ]
  | F (a, b) -> mk_simple_term (op "p") [ model args a; model args b ] | V x -> List.assoc x args
let rec uses = function C -> [ "ax" ] | V _ -> [] | G a -> "gi" :: uses a | F (a, b) -> "fi" :: uses a @ uses b

let name = "test_refine_extract_join"
let pname = "test_refine_extract_join_prims"
let pb = null_refiner pname
let es = Rewrite.empty_args_spec
let ra = Rewrite.empty_rw_args
let mterm subs goal = List.fold_right (fun s acc -> Term_sig.MetaImplies (Term_sig.MetaTheorem s, acc)) subs (Term_sig.MetaTheorem goal)
let opname n = Opname.mk_opname n (op name)
let prim n subs goal args ext =
  let tac = create_rule pb n es [] (mterm subs goal) in
  prim_rule pb n es [] (mterm subs goal) args ext; tac
let sv x = term (V x)
let ax = prim "ax" [] (term C) [] (mk_simple_term (op "k") [])
let gi = prim "gi" [ sv "a" ] (term (G (V "a"))) [ sv "x" ] (mk_simple_term (op "q") [ sv "x" ])
let fi = prim "fi" [ sv "a"; sv "b" ] (term (F (V "a", V "b"))) [ sv "x"; sv "y" ] (mk_simple_term (op "p") [ sv "x"; sv "y" ])

(* prove a pattern with the primitives under assumptions vs (the rule's
   subgoals), closing each variable by nth_hyp *)
let rec prove_under sent vs p =
  let goal = mk_msequent (term p) (List.map sv vs) in
  match p with
  | V x ->
     let rec index i = function y :: l -> if y = x then i else index (i + 1) l | [] -> failwith "index" in
     snd (refine sent (nth_hyp (index 0 vs)) goal)
  | _ ->
     let tac = match p with C -> ax | G _ -> gi | _ -> fi in
     let _, ext = refine sent (tac ra []) goal in
     compose ext (List.map (prove_under sent vs) (match p with C | V _ -> [] | G a -> [ a ] | F (a, b) -> [ a; b ]))
let prove sent p = prove_under sent (vars p) p

(* the theorems' refiner joins the primitives' refiner through its label, twice *)
let lp = label_refiner pb "PRIMS"
let build = null_refiner name
let () = join_refiner build lp; join_refiner build lp
let count = ref 0
(* create and justify a rule for pattern p; its name *)
let theorem ?(delayed = false) ?sent p =
  incr count;
  let n = "thm" ^ string_of_int !count in
  let subs = List.map sv (vars p) in
  let tac = create_rule build n es [] (mterm subs (term p)) in
  let sent = match sent with Some s -> s | None -> sentinal_of_refiner (refiner_of_build build) in
  let ext = prove sent p in
  if delayed then delayed_rule build n es [] (mterm subs (term p)) () (fun () -> ext)
  else derived_rule build n es [] (mterm subs (term p)) () ext;
  n, tac

let deps n = List.sort_uniq compare (List.map (fun (_, o) -> List.hd (Opname.dest_opname o)) (compute_dependencies (refiner_of_build build) (opname n)))
let () =
  let rules = 60 in
  let ext_ok = ref 0 and dep_ok = ref 0 and first = ref None in
  for k = 1 to rules do
    let p, _ = gen 4 [ "a"; "b" ] in
    let n, _ = theorem ~delayed:(k mod 2 = 0) p in
    let args = List.map (fun x -> x, term (V ("e" ^ x))) (vars p) in
    let got = try Some (extract_term (refiner_of_build build) (opname n) (List.map snd args)) with Invalid_argument s -> (if !first = None then first := Some ("refused: " ^ s)); None | Refiner.Refiner.RefineError.RefineError _ -> None in
    (match got with Some t when show_t t = show_t (model args p) -> incr ext_ok | _ -> ());
    if deps n = List.sort_uniq compare (uses p) then incr dep_ok
  done;
  Printf.printf "%-52s %d of %d\n" "extract_term through the join, as the model says" !ext_ok rules;
  Printf.printf "%-52s %d of %d\n" "compute_dependencies through the join" !dep_ok rules;
  (match !first with Some s -> Printf.printf "first refusal: %s\n" s | None -> ());
  let n, _ = theorem (F (G C, V "a")) in
  Printf.printf "%-52s %s\n" "extract of f{g{c}; 'a} with 'a := 'ea" (show_t (extract_term (refiner_of_build build) (opname n) [ term (V "ea") ]));
  (* a refiner that holds a theorem, but not the primitives under it *)
  let alone = null_refiner "test_refine_extract_join_alone" in
  let tac = create_rule alone "lone" es [] (mterm [] (term C)) in
  ignore tac;
  derived_rule alone "lone" es [] (mterm [] (term C)) () (prove (sentinal_of_refiner (refiner_of_build build)) C);
  Printf.printf "%-52s %s\n" "extract of a theorem whose primitives are elsewhere"
    (try show_t (extract_term (refiner_of_build alone) (Opname.mk_opname "lone" (op "test_refine_extract_join_alone")) []) with Invalid_argument s -> "Invalid_argument " ^ s)
