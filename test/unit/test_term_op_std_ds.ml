(* term_std against term_ds (the refiner's, TERMS = ds) for TermOp's
   traversals, on the case where they disagreed in a TERMS = both build:
   Refine.mk_rewrite_hack maps "add the context H to the contexts list of
   every second-order variable and context" with map_down over a rewrite's
   terms. In term_ds a context hypothesis is not a term, so it is not
   mapped; term_std encodes it as a context node and mapped it too.
   The terms below are built in both implementations, mapped with
   map_down and map_up, and printed as their contexts lists: each line
   prints term_std's, then whether term_ds's is the same. The visits of
   iter_down and iter_up are counted the same way. *)
open Lm_symbol
open Term_sig

module P (R : Refiner_sig.RefinerSig) = struct
  open R.Term
  open R.TermMan
  let v = add
  let op s = Opname.make_opname [ s ]
  let so x conts args = mk_so_var_term (v x) (List.map v conts) args
  let vs l = String.concat "," (List.map string_of_symbol l)
  let rec sg t =
    if is_var_term t then string_of_symbol (dest_var t)
    else if is_so_var_term t then
      let x, conts, args = dest_so_var t in
      string_of_symbol x ^ "<|" ^ vs conts ^ "|>(" ^ String.concat ";" (List.map sg args) ^ ")"
    else if is_context_term t then
      let x, body, conts, args = dest_context t in
      "<" ^ string_of_symbol x ^ "<|" ^ vs conts ^ "|>(" ^ String.concat ";" (List.map sg args) ^ ")> " ^ sg body
    else if is_sequent_term t then
      let (s : R.TermType.esequent) = explode_sequent t in
      "sequent{" ^ String.concat "; " (List.map (function
          | Hypothesis (x, a) -> string_of_symbol x ^ ": " ^ sg a
          | Context (x, conts, args) ->
              "<" ^ string_of_symbol x ^ "<|" ^ vs conts ^ "|>(" ^ String.concat ";" (List.map sg args) ^ ")>")
          (SeqHyp.to_list s.sequent_hyps)) ^ " >- " ^ sg s.sequent_concl ^ "}"
    else
      let { term_op; term_terms } = dest_term t in
      String.concat "!" (Opname.dest_opname (dest_op term_op).op_name)
      ^ (if term_terms = [] then "" else "{" ^ String.concat "; " (List.map (fun b -> sg (dest_bterm b).bterm) term_terms) ^ "}")

  let h = v "H"
  let cmap conts = if List.mem h conts then conts else h :: conts
  let map t =
    if is_so_var_term t then let x, conts, ts = dest_so_var t in mk_so_var_term x (cmap conts) ts
    else if is_context_term t then let x, b, conts, ts = dest_context t in mk_context_term x b (cmap conts) ts
    else t

  let seq =
    mk_sequent_term
      { sequent_args = mk_simple_term (op "sequent_arg") [];
        sequent_hyps = SeqHyp.of_list
          [ Context (v "J", [], []); Hypothesis (v "x", so "A" [ "J" ] []);
            Context (v "K", [ v "J" ], [ mk_var_term (v "x") ]) ];
        sequent_concl = so "C" [ "J"; "K" ] [ mk_var_term (v "x") ] }
  let ctx = mk_context_term (v "L") (so "B" [ "L" ] []) [] [ so "D" [] [] ]
  let terms = [ "sequent", seq; "rewrite{sequent; context}", mk_simple_term (op "rewrite") [ seq; ctx ] ]
  let count it t = let n = ref 0 in it (fun _ -> incr n) t; !n
  let lines =
    List.concat_map (fun (name, t) ->
        [ name ^ "  map_down: " ^ sg (R.TermOp.map_down map t);
          name ^ "  map_up:   " ^ sg (R.TermOp.map_up map t);
          name ^ "  iter_down visits " ^ string_of_int (count R.TermOp.iter_down t)
          ^ ", iter_up visits " ^ string_of_int (count R.TermOp.iter_up t) ]) terms
end

module S = P (Refiner_std.Refiner)
module D = P (Refiner_ds.Refiner)

let () =
  let n = ref 0 in
  List.iter2 (fun s d ->
      if s <> d then incr n;
      Printf.printf "%s\n  %s\n" s (if s = d then "ds: same" else "ds: " ^ d)) S.lines D.lines;
  Printf.printf "%d of %d lines differ\n" !n (List.length S.lines)
