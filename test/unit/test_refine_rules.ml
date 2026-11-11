(* The refiner's rules (refiner/refiner/refine.ml create_rule, prim_rule,
   sentinal_of_refiner), which no unit test reached (2026-11-11 reach
   census: refine.ml 72 of 896 points, none in create_rule).
   Random rules  S1 --> ... --> Sn --> G  are created in a null refiner,
   where G and the Si are patterns over f{_;_}, g{_}, c and the variables
   'a and 'b (each Si uses only variables of G), and applied through
   refine to random closed goals, with a random number of assumptions.
   The subgoals are compared with a model:
     the rule applies when G matches the goal, a repeated variable
     matching equal terms; the subgoals are the Si under that match, in
     order, and each keeps the goal's assumptions; otherwise it is refused.
   Fixed cases (measured, 2026-11-11):
     - a subgoal variable that G does not bind is refused when the rule is
       CREATED, not when it is applied;
     - null_sentinal refuses every rule;
     - sentinal_of_refiner refuses a rule that is created but not
       justified, and a sentinel is a snapshot: a rule justified by
       prim_rule after the sentinel was taken is still refused by it,
       and accepted by a sentinel taken afterwards (check_sentinal also
       prints one line on stderr when it refuses).
   Not covered: the patterns have no binders, so the Strict mode create_rule
   compiles with is not told apart from Relaxed (they differ only on bound
   variables); rules with parameters, addresses or second-order variables
   with arguments; derived_rule, delayed_rule and extracts.
   The generator is a fixed linear congruential sequence, not Random. *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.Refine

let state = ref 4242
let next () = state := (!state * 1103515245 + 12345) land 0x7fffffff; !state lsr 8
let pick n = next () mod n

type p = C | G of p | F of p * p | V of string
let rec gen_closed depth = if depth = 0 || pick 3 = 0 then C else if pick 2 = 0 then G (gen_closed (depth - 1)) else F (gen_closed (depth - 1), gen_closed (depth - 1))
let rec gen_pat depth =
  match pick 6 with
  | 0 -> V "a" | 1 -> V "b"
  | 2 -> C
  | _ when depth = 0 -> C
  | 3 -> G (gen_pat (depth - 1))
  | _ -> F (gen_pat (depth - 1), gen_pat (depth - 1))
let rec vars = function C -> [] | V x -> [ x ] | G a -> vars a | F (a, b) -> vars a @ vars b
let rec gen_sub bound depth =
  match pick 5 with
  | 0 | 1 when bound <> [] -> V (List.nth bound (pick (List.length bound)))
  | _ when depth = 0 -> C
  | 2 -> G (gen_sub bound (depth - 1))
  | 3 -> F (gen_sub bound (depth - 1), gen_sub bound (depth - 1))
  | _ -> C
let rec show = function C -> "c" | V x -> "'" ^ x | G a -> "g{" ^ show a ^ "}" | F (a, b) -> "f{" ^ show a ^ "; " ^ show b ^ "}"

(* the model *)
let rec matches env p t =
  match p, t with
  | V x, _ -> (match List.assoc_opt x env with Some u -> if u = t then Some env else None | None -> Some ((x, t) :: env))
  | C, C -> Some env
  | G p, G t -> matches env p t
  | F (p1, p2), F (t1, t2) -> (match matches env p1 t1 with Some env -> matches env p2 t2 | None -> None)
  | _ -> None
let rec inst env = function C -> C | V x -> List.assoc x env | G a -> G (inst env a) | F (a, b) -> F (inst env a, inst env b)
let model subs goal t = Option.map (fun env -> List.map (inst env) subs) (matches [] goal t)

(* the refiner *)
let op s = Opname.make_opname [ s ]
let rec term = function
  | C -> mk_simple_term (op "c") [] | G a -> mk_simple_term (op "g") [ term a ]
  | F (a, b) -> mk_simple_term (op "f") [ term a; term b ] | V x -> mk_so_var_term (Lm_symbol.add x) [] []
let rec back t =
  let { Term_sig.term_op; term_terms } = dest_term t in
  match Opname.dest_opname (dest_op term_op).Term_sig.op_name, List.map (fun b -> back (dest_bterm b).Term_sig.bterm) term_terms with
  | [ "c" ], [] -> C | [ "g" ], [ a ] -> G a | [ "f" ], [ a; b ] -> F (a, b) | _ -> failwith "back"
let mterm subs goal = List.fold_right (fun s acc -> Term_sig.MetaImplies (Term_sig.MetaTheorem (term s), acc)) subs (Term_sig.MetaTheorem (term goal))
let build = null_refiner "test_refine_rules"
let count = ref 0
let rule subs goal = incr count; create_rule build ("r" ^ string_of_int !count) Rewrite.empty_args_spec [] (mterm subs goal)

(* subgoals and whether each kept the assumptions, or None when refused *)
let apply sent tac t assums =
  match refine sent (tac Rewrite.empty_rw_args []) (mk_msequent (term t) (List.map term assums)) with
  | sg, _ -> Some (List.map (fun m -> back (msequent_goal m), List.map back (msequent_all_assums m) = assums) sg)
  | exception Refiner.Refiner.RefineError.RefineError _ -> None

let () =
  let rules = 200 and goals = 40 in
  let tried = ref 0 and agree = ref 0 and applied = ref 0 and kept = ref 0 and first = ref None in
  for _ = 1 to rules do
    let goal = gen_pat 3 in
    let bound = List.sort_uniq compare (vars goal) in
    let subs = List.init (pick 4) (fun _ -> gen_sub bound 2) in
    let tac = rule subs goal in
    for k = 1 to goals do
      (* every other goal is an instance of the rule's conclusion *)
      let t =
        if k mod 2 = 0 then gen_closed 3
        else inst (List.map (fun x -> x, gen_closed 2) bound) goal in
      let assums = List.init (pick 3) (fun _ -> gen_closed 2) in
      incr tried;
      let expect = model subs goal t in
      let got = apply any_sentinal tac t assums in
      let ok =
        match expect, got with
        | None, None -> true
        | Some e, Some g ->
           incr applied;
           if List.for_all snd g then incr kept;
           List.map fst g = e
        | _ -> false in
      if ok then incr agree
      else if !first = None then
        first := Some (Printf.sprintf "rule %s --> %s on %s" (String.concat " --> " (List.map show subs)) (show goal) (show t))
    done
  done;
  Printf.printf "%-52s %d of %d\n" "rules applied as the model says" !agree !tried;
  Printf.printf "%-52s %d of %d\n" "applications that kept every assumption" !kept !applied;
  (match !first with Some s -> Printf.printf "first disagreement: %s\n" s | None -> ());
  Printf.printf "%-52s %b\n" "some applied and some refused" (!applied > 0 && !applied < !tried)

let show_result = function
  | None -> "refused"
  | Some sg -> "subgoals [" ^ String.concat "; " (List.map (fun (g, _) -> show g) sg) ^ "]"

let () =
  (* a subgoal variable the conclusion does not bind *)
  Printf.printf "%-52s %s\n%!" "create g{'a} with subgoal 'b"
    (match (rule [ V "b" ] (G (V "a")) : prim_tactic) with _ -> "created" | exception Refiner.Refiner.RefineError.RefineError _ -> "refused at creation");
  let axiom = rule [] C in
  Printf.printf "%-52s %s\n%!" "axiom c, any_sentinal" (show_result (apply any_sentinal axiom C []));
  Printf.printf "%-52s %s\n%!" "axiom c, null_sentinal" (show_result (apply null_sentinal axiom C []));
  let before = sentinal_of_refiner (refiner_of_build build) in
  Printf.printf "%-52s %s\n%!" "axiom c, sentinel of the refiner, not justified" (show_result (apply before axiom C []));
  prim_rule build ("r" ^ string_of_int !count) Rewrite.empty_args_spec [] (mterm [] C) [] (mk_simple_term (op "ext") []);
  Printf.printf "%-52s %s\n%!" "after prim_rule, the sentinel taken before" (show_result (apply before axiom C []));
  let after = sentinal_of_refiner (refiner_of_build build) in
  Printf.printf "%-52s %s\n%!" "after prim_rule, a sentinel taken after" (show_result (apply after axiom C []))
