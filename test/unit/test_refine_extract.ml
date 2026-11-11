(* The refiner's extracts (refiner/refiner/refine.ml compose, derived_rule,
   delayed_rule, extract_term, compute_dependencies and the term_of_extract
   behind them), which no unit test reached (2026-11-11 reach census:
   refine.ml 72 of 896 points).
   Three primitive rules with extracts are justified in a null refiner:
     ax  |- c                     extract k
     gi  'a |- g{'a}              extract q{'x}     ('x the subgoal's)
     fi  'a, 'b |- f{'a; 'b}      extract p{'x; 'y}
   A random pattern P over f, g, c and the variables 'a, 'b (each at most
   once) is created as a rule  'v1 --> ... --> P  whose subgoals are P's
   variables in left-to-right order, and proved: the goal P with the
   subgoals as assumptions is refined with the primitives down to its
   variables, each closed by nth_hyp, every step under a sentinel of the
   refiner, the extracts joined with compose.  Half the rules are
   justified with derived_rule, half with delayed_rule.  Compared with a
   model:
     extract_term on the rule, with one second-order variable per subgoal
     as its argument, is P with c, g, f read as k, q, p and each variable
     read as its argument;
     compute_dependencies lists the primitives P uses (as a set).
   Fixed cases (measured, 2026-11-11):
     - a proof built under any_sentinal is refused by extract_term
       (Invalid_argument "Sentinals mismatch in extractor function");
     - derived_rule on a name that was never created is refused; a proof of
       a DIFFERENT goal is accepted, because the proof is checked lazily,
       and refused when its extract is first asked for;
     - extract_term refuses a closed term as an argument (an argument must
       be as general as its subgoal) and the wrong number of arguments;
     - compose refuses a goal mismatch and extracts from two sentinels;
     - a theorem proved with another derived theorem as a step depends on
       the PRIMITIVES under that theorem, and the theorem itself is not
       listed: dependencies are followed through derived rules to their
       primitive leaves;
     - nth_hyp counts assumptions from 0 (msequent_nth_assum from 1).
   Not covered: sequents (the extract machinery's sequent half), parameters
   and addresses, rewrites' justifications.
   The generator is a fixed linear congruential sequence, not Random. *)
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

let name = "test_refine_extract"
let build = null_refiner name
let es = Rewrite.empty_args_spec
let ra = Rewrite.empty_rw_args
let mterm subs goal = List.fold_right (fun s acc -> Term_sig.MetaImplies (Term_sig.MetaTheorem s, acc)) subs (Term_sig.MetaTheorem goal)
let opname n = Opname.mk_opname n (op name)
let prim n subs goal args ext =
  let tac = create_rule build n es [] (mterm subs goal) in
  prim_rule build n es [] (mterm subs goal) args ext; tac
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
  let rules = 300 in
  let tried = ref 0 and ext_ok = ref 0 and dep_ok = ref 0 and with_args = ref 0 and first = ref None in
  for k = 1 to rules do
    let p, _ = gen 4 [ "a"; "b" ] in
    let n, _ = theorem ~delayed:(k mod 2 = 0) p in
    let args = List.map (fun x -> x, term (V ("e" ^ x))) (vars p) in
    if args <> [] then incr with_args;
    incr tried;
    let got = try Some (extract_term (refiner_of_build build) (opname n) (List.map snd args)) with Invalid_argument _ | Refiner.Refiner.RefineError.RefineError _ -> None in
    let ok = match got with Some t -> show_t t = show_t (model args p) | None -> false in
    if ok then incr ext_ok
    else if !first = None then first := Some (Printf.sprintf "extract of %s: %s" (show p) (match got with Some t -> show_t t | None -> "refused"));
    if deps n = List.sort_uniq compare (uses p) then incr dep_ok
    else if !first = None then first := Some (Printf.sprintf "dependencies of %s: %s" (show p) (String.concat " " (deps n)))
  done;
  Printf.printf "%-52s %d of %d (%d with arguments)\n" "extract_term as the model says" !ext_ok !tried !with_args;
  Printf.printf "%-52s %d of %d\n" "compute_dependencies as the model says" !dep_ok !tried;
  (match !first with Some s -> Printf.printf "first disagreement: %s\n" s | None -> ())

let attempt label f = Printf.printf "%-52s %s\n%!" label (try f () with Invalid_argument s -> "Invalid_argument " ^ s | Refiner.Refiner.RefineError.RefineError _ -> "refused")

let () =
  attempt "a proof built under any_sentinal" (fun () ->
      let n, _ = theorem ~sent:any_sentinal (G C) in show_t (extract_term (refiner_of_build build) (opname n) []));
  attempt "derived_rule on a name never created" (fun () ->
      derived_rule build "never" es [] (mterm [] (term C)) () (prove (sentinal_of_refiner (refiner_of_build build)) C); "accepted");
  attempt "derived_rule with a proof of another goal" (fun () ->
      ignore (create_rule build "other" es [] (mterm [] (term (G C))) : prim_tactic);
      derived_rule build "other" es [] (mterm [] (term (G C))) () (prove (sentinal_of_refiner (refiner_of_build build)) C); "accepted");
  attempt "and then its extract" (fun () -> show_t (extract_term (refiner_of_build build) (opname "other") []));
  let n, _ = theorem (G (V "a")) in
  attempt "extract_term with a closed term as the argument" (fun () -> show_t (extract_term (refiner_of_build build) (opname n) [ model [] C ]));
  attempt "extract_term with no argument for one subgoal" (fun () -> show_t (extract_term (refiner_of_build build) (opname n) []));
  attempt "extract_term with two arguments for one" (fun () -> show_t (extract_term (refiner_of_build build) (opname n) [ term (V "x"); term (V "y") ]));
  attempt "compose with a goal mismatch" (fun () ->
      let sent = sentinal_of_refiner (refiner_of_build build) in
      let _, ext = refine sent (gi ra []) (mk_msequent (term (G C)) []) in
      ignore (compose ext [ prove sent (G C) ]); "accepted");
  attempt "compose across two sentinels" (fun () ->
      let s1 = sentinal_of_refiner (refiner_of_build build) and s2 = sentinal_of_refiner (refiner_of_build build) in
      let _, ext = refine s1 (gi ra []) (mk_msequent (term (G C)) []) in
      ignore (compose ext [ prove s2 C ]); "accepted");
  (* a theorem proved with another theorem as a step *)
  let lemma, lemma_tac = theorem (G C) in
  incr count;
  let top = "thm" ^ string_of_int !count in
  ignore (create_rule build top es [] (mterm [] (term (F (G C, C)))) : prim_tactic);
  let sent = sentinal_of_refiner (refiner_of_build build) in
  let _, ext = refine sent (fi ra []) (mk_msequent (term (F (G C, C))) []) in
  let _, lext = refine sent (lemma_tac ra []) (mk_msequent (term (G C)) []) in
  derived_rule build top es [] (mterm [] (term (F (G C, C)))) () (compose ext [ lext; prove sent C ]);
  Printf.printf "%-52s %s\n" "a theorem using a lemma depends on" (String.concat " " (List.map (fun d -> if d = lemma then "the lemma" else d) (deps top)));
  attempt "and its extract" (fun () -> show_t (extract_term (refiner_of_build build) (opname top) []))
