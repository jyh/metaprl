(* Match_seq.match_some_hyps (refiner/reflib), the relaxed matcher behind
   itt_logic's assum_term (which builds the formula an assumption stands
   for from the hypotheses the goal does not already have): it matches the
   small sequent's hypotheses, in order, against a subsequence of the big
   sequent's, need not match them all nor the conclusion, but must match
   every context, and returns the number of small hypotheses matched.  No
   unit test called it (test_match_seq covers match_hyps).  The model: the
   largest k such that the first k small hypotheses are, in order, a
   subsequence of the big sequent's (contexts by name and arguments,
   hypotheses by alpha-equality under the hypotheses matched before them), and no small
   context lies at or after k; with no such k the match is refused.  Each
   line prints the code's answer, the model's, and "<- DIFFERS".
   PINNED AS FOUND, not changed: when no hypothesis matches, the answer is
   1, the same as when exactly the first one does (succ of a search that
   returns 0 for both); the model says 0 there and the lines are marked
   "(pinned: none matched)".  assum_term then treats the first hypothesis as matched, so
   the formula it builds lacks it; the refiner checks what that formula
   proves, so the cost is a failed step, not a wrong one.
   AND PINNED AS FOUND: the match is greedy, not maximal.  A small
   hypothesis is matched to the first big one that fits, and once the big
   sequent is exhausted the relaxed mode accepts without trying another
   assignment; so [x:A; x2:A; y:g{x2}] against [z:A; w:g{z}] gives 1 where
   2 are matchable.  assum_term calls its count "approximate". *)
open Refiner.Refiner
open TermType
open Term
open TermMan
open Term_sig

let op s = Opname.make_opname [ s ]
let v = Lm_symbol.add
let c s = mk_simple_term (op s) []
let g a = mk_simple_term (op "g") [ a ]
let var x = mk_var_term (v x)
let seq hyps = explode_sequent (mk_sequent_term { sequent_args = c "arg"; sequent_hyps = SeqHyp.of_list hyps; sequent_concl = c "C" })
let h x t = Hypothesis (v x, t)
let k n = Context (v n, [], [])

(* the model, on hypotheses whose terms are closed or mention earlier
   hypotheses by name (renamed in step with the match) *)
let model big small =
  let big = Array.of_list big and small = Array.of_list small in
  let nb = Array.length big and ns = Array.length small in
  let eqh (bv, sv) a b = match a, b with
    | Context (x, _, ts1), Context (y, _, ts2) ->
        Lm_symbol.eq x y && List.length ts1 = List.length ts2 && List.for_all2 (fun a b -> TermSubst.alpha_equal_vars a bv b sv) ts1 ts2
    | Hypothesis (_, t1), Hypothesis (_, t2) -> TermSubst.alpha_equal_vars t1 bv t2 sv
    | _ -> false in
  (* greedy earliest match of the prefix of length k; true if it embeds *)
  let embeds kk =
    let rec go i j bv sv = if j = kk then true else if i = nb then false
      else if eqh (bv, sv) big.(i) small.(j) then
        let bv', sv' = match big.(i), small.(j) with
          | Hypothesis (x, _), Hypothesis (y, _) -> x :: bv, y :: sv | _ -> bv, sv in
        go (i + 1) (j + 1) bv' sv' || go (i + 1) j bv sv
      else go (i + 1) j bv sv in
    go 0 0 [] [] in
  let ctx_after kk = let r = ref false in for j = kk to ns - 1 do (match small.(j) with Context _ -> r := true | _ -> ()) done; !r in
  let rec best kk = if kk < 0 then None else if embeds kk && not (ctx_after kk) then Some kk else best (kk - 1) in
  best ns

let show_h = function
  | Hypothesis (x, t) -> Lm_symbol.to_string x ^ ":" ^ Simple_print.SimplePrint.string_of_term t
  | Context (x, _, []) -> "<" ^ Lm_symbol.to_string x ^ ">"
  | Context (x, _, ts) -> "<" ^ Lm_symbol.to_string x ^ "[" ^ String.concat ";" (List.map Simple_print.SimplePrint.string_of_term ts) ^ "]>"
let show l = "[" ^ String.concat "; " (List.map show_h l) ^ "]"

let cases = [
  [ k "H"; h "x" (c "A"); h "y" (c "B") ], [ k "H"; h "z" (c "A") ];
  [ k "H"; h "x" (c "A"); h "y" (c "B") ], [ k "H"; h "z" (c "B") ];
  [ k "H"; h "x" (c "A") ], [ k "H"; h "z" (c "A"); h "w" (c "B") ];
  [ k "H"; h "x" (c "A") ], [ k "H"; h "z" (c "B"); h "w" (c "A") ];
  [ h "x" (c "A"); h "y" (c "B") ], [ h "z" (c "A"); h "w" (c "B") ];
  [ h "x" (c "A"); h "y" (c "B") ], [ h "z" (c "B") ];
  [ h "x" (c "A"); h "y" (c "B") ], [ h "z" (c "D") ];
  [ h "x" (c "A") ], [ h "z" (c "D"); h "w" (c "A") ];
  [ h "x" (c "A") ], [];
  [], [ h "z" (c "A") ];
  [ h "x" (c "A"); h "y" (g (var "x")) ], [ h "z" (c "A"); h "w" (g (var "z")) ];
  [ h "x" (c "A"); h "y" (g (var "x")) ], [ h "z" (c "B"); h "w" (g (var "z")) ];
  [ h "x" (c "A"); h "x2" (c "A"); h "y" (g (var "x2")) ], [ h "z" (c "A"); h "w" (g (var "z")) ];
  [ k "H"; h "x" (c "A"); k "J" ], [ k "H"; k "J" ];
  [ k "H"; h "x" (c "A") ], [ k "H"; h "z" (c "A"); k "J" ];
  [ k "J"; h "x" (c "A") ], [ k "H"; h "z" (c "A") ];
  [ Context (v "H", [], [ c "a" ]); h "x" (c "A") ], [ Context (v "H", [], [ c "a" ]); h "z" (c "A") ];
  [ Context (v "H", [], [ c "a" ]); h "x" (c "A") ], [ Context (v "H", [], [ c "b" ]); h "z" (c "A") ];
]

let () =
  List.iter (fun (big, small) ->
      let code = try string_of_int (Match_seq.match_some_hyps (seq big) (seq small)) with RefineError.RefineError _ -> "refused" in
      let m = match model big small with Some n -> string_of_int n | None -> "refused" in
      let mark = if code = m then "" else if m = "0" && code = "1" then "  (pinned: none matched)"
        else (match int_of_string_opt code, int_of_string_opt m with
            | Some a, Some b when a > 0 && a < b -> "  (pinned: greedy, not maximal)"
            | _ -> "  <- DIFFERS") in
      Printf.printf "%-40s %-28s code %-7s model %s%s\n" (show big) (show small) code m mark) cases
