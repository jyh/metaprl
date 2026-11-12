(* JProver (refiner/reflib: jall), LJ proof reconstruction: the rule
   permutations it performs when turning a matrix proof into a
   single-conclusion LJ sequent proof, which the propositional and
   first-order tests reach only in part.  Measured 2026-11-11 against the
   proof census (bisect, jall.ml): after those tests, the census still ran
   the beta-proof purity reduction (a beta split whose left or right layer
   is not needed is dropped), the split permutation below the topmost beta
   expansion, and the "wait" decisions for an implication or negation on
   the left while the succedent is non-empty, and no unit test did.  Every
   formula here is a textbook theorem of intuitionistic logic (so of
   classical logic too), chosen because its reconstruction takes one of
   those paths: hypothetical syllogism and its variants (an implication on
   the left whose other premise is needed later), proof by cases, the
   distributive laws, and negations on the left.  The same JLogic over
   plain terms as test_jprover_fo; each formula is run in LJ and LJmc at
   multiplicity 3 and its outcome printed; a line is marked "<- DIFFERS"
   when either does not prove it.  For every one the reconstructed LJ
   proof is printed step by step (rule, term, term), which pins the
   permuted proof. *)
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Jlogic_sig

let op s = Opname.make_opname [ s ]
let o_not = op "not" and o_and = op "and" and o_or = op "or" and o_imp = op "implies"
let o_all = op "all" and o_ex = op "exists"
let dom = mk_simple_term (op "D") []

type t =
  | V of string | K of string
type f =
  | P of t | Q of t | R of t * t | S
  | Not of f | And of f * f | Or of f * f | Imp of f * f
  | All of string * f | Ex of string * f

let rec show = function
  | P t -> "P " ^ st t | Q t -> "Q " ^ st t | R (t, u) -> "R " ^ st t ^ " " ^ st u | S -> "S"
  | Not a -> "~" ^ show a | And (a, b) -> "(" ^ show a ^ " & " ^ show b ^ ")"
  | Or (a, b) -> "(" ^ show a ^ " | " ^ show b ^ ")" | Imp (a, b) -> "(" ^ show a ^ " => " ^ show b ^ ")"
  | All (x, a) -> "all " ^ x ^ ". " ^ show a | Ex (x, a) -> "ex " ^ x ^ ". " ^ show a
and st = function V x -> x | K c -> c

let term = function V x -> mk_var_term (Lm_symbol.add x) | K c -> mk_simple_term (op c) []
let rec build = function
  | P t -> mk_simple_term (op "P") [ term t ]
  | Q t -> mk_simple_term (op "Q") [ term t ]
  | R (t, u) -> mk_simple_term (op "R") [ term t; term u ]
  | S -> mk_simple_term (op "S") []
  | Not a -> mk_simple_term o_not [ build a ]
  | And (a, b) -> mk_simple_term o_and [ build a; build b ]
  | Or (a, b) -> mk_simple_term o_or [ build a; build b ]
  | Imp (a, b) -> mk_simple_term o_imp [ build a; build b ]
  | All (x, a) -> mk_dep0_dep1_term o_all (Lm_symbol.add x) dom (build a)
  | Ex (x, a) -> mk_dep0_dep1_term o_ex (Lm_symbol.add x) dom (build a)

module L = struct
  let is_all_term = is_dep0_dep1_term o_all
  let dest_all = dest_dep0_dep1_term o_all
  let is_exists_term = is_dep0_dep1_term o_ex
  let dest_exists = dest_dep0_dep1_term o_ex
  let is_and_term = is_dep0_dep0_term o_and
  let dest_and = two_subterms
  let is_or_term = is_dep0_dep0_term o_or
  let dest_or = two_subterms
  let is_implies_term = is_dep0_dep0_term o_imp
  let dest_implies = two_subterms
  let is_not_term = is_dep0_term o_not
  let dest_not = one_subterm
  let is_box_term _ = false
  let dest_box _ = invalid_arg "dest_box"
  (* each reconstructed step: its rule and its two terms *)
  type inference = string list
  let empty_inf = []
  let append_inf l t1 t2 r =
    let sp = Simple_print.SimplePrint.string_of_term in
    Printf.sprintf "%s  %s  /  %s" (Jall.ruletable r) (sp t1) (sp t2) :: l
end
module Pr = Jall.JProver (L)

let x = V "x" and y = V "y" and a = K "a" and b = K "b"

(* status, formula *)
(* status, formula *)
let cases = [
  `Both, Imp (Imp (P a, Q a), Imp (Imp (Q a, S), Imp (P a, S)));
  `Both, Imp (All ("x", Imp (P x, Q x)), Imp (All ("x", Imp (Q x, S)), Imp (P a, S)));
  `Both, Imp (All ("x", Imp (P x, Q x)), Imp (Imp (Q a, S), Imp (P a, S)));
  `Both, Imp (Imp (All ("x", P x), S), Imp (Imp (S, Q a), Imp (All ("x", P x), Q a)));
  `Both, Imp (And (Imp (P a, S), Imp (Q a, S)), Imp (Or (P a, Q a), S));
  `Both, Imp (Or (P a, Q a), Imp (Imp (P a, S), Imp (Imp (Q a, S), S)));
  `Both, Imp (All ("x", Imp (P x, Or (Q x, S))), Imp (All ("x", Imp (Q x, S)), Imp (P a, S)));
  `Both, Imp (Imp (Imp (P a, S), S), Imp (Imp (P a, Q a), Imp (Imp (Q a, S), S)));
  `Both, Imp (And (Or (P a, Q a), Or (P a, S)), Or (P a, And (Q a, S)));
  `Both, Imp (Or (P a, And (Q a, S)), And (Or (P a, Q a), Or (P a, S)));
  `Both, Imp (Imp (P a, Imp (Q a, S)), Imp (Imp (P a, Q a), Imp (P a, S)));
  `Both, Imp (Imp (Or (P a, Q a), S), And (Imp (P a, S), Imp (Q a, S)));
  `Both, Imp (And (Not (P a), Or (P a, S)), S);
  `Both, Imp (And (Not (P a), Not (Q a)), Not (Or (P a, Q a)));
  `Both, Imp (Not (P a), Imp (Or (P a, Q a), Q a));
  `Both, Imp (Imp (Not (P a), S), Imp (Imp (P a, S), Not (Not S)));
]

let prove calc f =
  try ignore (Pr.gen_prover (Some 3) calc [] [ build f ]); "proved" with
  | Refiner.Refiner.RefineError.RefineError _ -> "not provable"

(* JProver names its eigenvariables c_jprover<n> from a process-wide
   counter; rename them c1, c2, ... in order of first appearance in each
   proof so the output does not depend on what ran before. *)
let normalise lines =
  let tbl = Hashtbl.create 8 in
  let pre = "c_jprover" in
  let lp = String.length pre in
  let rename line =
    let b = Buffer.create (String.length line) and n = String.length line in
    let rec go i =
      if i >= n then ()
      else if i + lp <= n && String.sub line i lp = pre && i + lp < n && line.[i + lp] >= '0' && line.[i + lp] <= '9' then begin
        let j = ref (i + lp) in
        while !j < n && line.[!j] >= '0' && line.[!j] <= '9' do incr j done;
        let key = String.sub line i (!j - i) in
        let v = try Hashtbl.find tbl key with Not_found -> let v = Printf.sprintf "c%d" (Hashtbl.length tbl + 1) in Hashtbl.add tbl key v; v in
        Buffer.add_string b v; go !j
      end else (Buffer.add_char b line.[i]; go (i + 1))
    in
    go 0; Buffer.contents b
  in
  List.map rename lines

let () =
  let only = try Some (int_of_string Sys.argv.(1)) with _ -> None in
  List.iteri (fun k (st, f) ->
      if only = None || only = Some k then begin
        let sname = match st with `Both -> "both" | `COnly -> "C only" | `None -> "none" in
        let lj = prove (Intuit SingleConcl) f and ljmc = prove (Intuit MultiConcl) f in
        let want = if st = `Both then "proved" else "not provable" in
        let ok = lj = want && ljmc = want in
        Printf.printf "%2d %-6s %s\n   LJ %s · LJmc %s%s\n%!" k sname (show f) lj ljmc (if ok then "" else "  <- DIFFERS")
      end) cases;
  if only = None then begin
    List.iter (fun k ->
        let f = snd (List.nth cases k) in
        Printf.printf "LJ proof of %d, %s:\n" k (show f);
        List.iter (Printf.printf "   %s\n") (normalise (List.rev (Pr.gen_prover (Some 3) (Intuit SingleConcl) [] [ build f ]))))
      (List.init (List.length cases) (fun k -> k))
  end
