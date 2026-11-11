(* JProver (refiner/reflib: jall, jtunify) in its S4 calculus: the
   multi-modal box[i] of theories/s4lp (S4_Logic), which neither the
   propositional nor the first-order test reaches.  A JLogic over plain
   terms with not, and, or, implies and box{i; A} (box_i A, written [i]A),
   atoms p, q, r.  Each formula's status is the textbook one for S4n
   (classical propositional logic with independent S4 modalities box_1,
   box_2, ...: each reflexive (T: [i]A => A) and transitive
   (4: [i]A => [i][i]A), with K), not computed:
     valid    a theorem of S4n;
     invalid  not a theorem (a counter-model exists).
   Each is run at multiplicity 3 with the hypotheses and conclusions given
   (S4 is multiple-conclusion) and its outcome printed (proved / not
   provable); a line is marked "<- DIFFERS" when the outcome contradicts
   the status.  For every theorem the reconstructed proof is printed
   step by step (rule, term, term). *)
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Jlogic_sig

let op s = Opname.make_opname [ s ]
let o_not = op "not" and o_and = op "and" and o_or = op "or" and o_imp = op "implies"
let o_box = op "box"

type f = A of string | Not of f | And of f * f | Or of f * f | Imp of f * f | Box of int * f

let rec show = function
  | A s -> s | Not a -> "~" ^ show a
  | And (a, b) -> "(" ^ show a ^ " & " ^ show b ^ ")" | Or (a, b) -> "(" ^ show a ^ " | " ^ show b ^ ")"
  | Imp (a, b) -> "(" ^ show a ^ " => " ^ show b ^ ")" | Box (i, a) -> "[" ^ string_of_int i ^ "]" ^ show a

let rec build = function
  | A s -> mk_simple_term (op s) []
  | Not a -> mk_simple_term o_not [ build a ]
  | And (a, b) -> mk_simple_term o_and [ build a; build b ]
  | Or (a, b) -> mk_simple_term o_or [ build a; build b ]
  | Imp (a, b) -> mk_simple_term o_imp [ build a; build b ]
  | Box (i, a) -> mk_number_dep0_term o_box (Lm_num.num_of_int i) (build a)

module L = struct
  let is_all_term _ = false
  let dest_all _ = invalid_arg "dest_all"
  let is_exists_term _ = false
  let dest_exists _ = invalid_arg "dest_exists"
  let is_and_term = is_dep0_dep0_term o_and
  let dest_and = two_subterms
  let is_or_term = is_dep0_dep0_term o_or
  let dest_or = two_subterms
  let is_implies_term = is_dep0_dep0_term o_imp
  let dest_implies = two_subterms
  let is_not_term = is_dep0_term o_not
  let dest_not = one_subterm
  let is_box_term = is_number_dep0_term o_box
  let dest_box t = let n, a = dest_number_dep0_term o_box t in Lm_num.int_of_num n, a
  (* each reconstructed step: its rule and its two terms *)
  type inference = string list
  let empty_inf = []
  let append_inf l t1 t2 r =
    let sp = Simple_print.SimplePrint.string_of_term in
    Printf.sprintf "%s  %s  /  %s" (Jall.ruletable r) (sp t1) (sp t2) :: l
end
module Pr = Jall.JProver (L)

let p = A "p" and q = A "q" and r = A "r"
let b1 a = Box (1, a) and b2 a = Box (2, a)

(* status, hypotheses, conclusions *)
let cases = [
  `Valid, [], [ Imp (b1 p, p) ];                                         (* T *)
  `Valid, [], [ Imp (b1 p, b1 (b1 p)) ];                                 (* 4 *)
  `Valid, [], [ Imp (b1 (Imp (p, q)), Imp (b1 p, b1 q)) ];               (* K *)
  `Valid, [], [ Imp (b1 (And (p, q)), And (b1 p, b1 q)) ];
  `Valid, [], [ Imp (And (b1 p, b1 q), b1 (And (p, q))) ];
  `Valid, [], [ Imp (Or (b1 p, b1 q), b1 (Or (p, q))) ];
  `Valid, [], [ Imp (b1 p, Not (b1 (Not p))) ];                          (* D *)
  `Valid, [], [ Imp (p, Not (b1 (Not p))) ];
  `Valid, [], [ b1 (Or (p, Not p)) ];                                    (* necessitation *)
  `Valid, [], [ Imp (b1 (b2 p), b2 p) ];
  `Valid, [], [ Imp (b1 (b2 p), b1 (b2 (b2 p))) ];
  `Valid, [ b1 p; b1 (Imp (p, q)) ], [ b1 q ];
  `Valid, [ b1 p ], [ q; p ];
  `Valid, [], [ Imp (b1 (Imp (p, q)), Imp (b1 (Imp (q, r)), b1 (Imp (p, r)))) ];
  `Invalid, [], [ Imp (p, b1 p) ];
  `Invalid, [], [ Imp (b1 (Or (p, q)), Or (b1 p, b1 q)) ];
  `Invalid, [], [ Imp (Not (b1 p), b1 (Not (b1 p))) ];                   (* 5 *)
  `Invalid, [], [ Imp (b1 p, b2 p) ];
  `Invalid, [], [ Imp (b1 (b2 p), b2 (b1 p)) ];
  `Invalid, [], [ Imp (Not (b1 (Not p)), b1 (Not (b1 (Not p)))) ];
  `Invalid, [ b1 p ], [ b1 q ];
  `Invalid, [], [ b1 p; b1 (Not p) ];
]

let prove hyps concls =
  try ignore (Pr.gen_prover (Some 3) S4 (List.map build hyps) (List.map build concls)); "proved" with
  | Refiner.Refiner.RefineError.RefineError _ -> "not provable"

let seq hyps concls =
  String.concat ", " (List.map show hyps) ^ " |- " ^ String.concat ", " (List.map show concls)

let () =
  let only = try Some (int_of_string Sys.argv.(1)) with _ -> None in
  List.iteri (fun k (st, hyps, concls) ->
      if only = None || only = Some k then begin
        let res = prove hyps concls in
        let want = if st = `Valid then "proved" else "not provable" in
        Printf.printf "%2d %-7s %s\n   %s%s\n%!" k (if st = `Valid then "valid" else "invalid")
          (seq hyps concls) res (if res = want then "" else "  <- DIFFERS")
      end) cases;
  if only = None then
    List.iter (fun k ->
        match List.nth cases k with
        | `Valid, hyps, concls ->
            Printf.printf "S4 proof of %d, %s:\n%!" k (seq hyps concls);
            List.iter (Printf.printf "   %s\n%!")
              (List.rev (Pr.gen_prover (Some 3) S4 (List.map build hyps) (List.map build concls)))
        | `Invalid, _, _ -> ())
      (List.init (List.length cases) (fun k -> k))
