(* term_std's sequent encoding, damaged: what num_hyps, nth_hyp and
   explode_sequent (refiner/term_gen/term_man_gen.ml) say about it.
   mk_sequent_term never builds a damaged encoding, but a term read from
   a damaged file is built by mk_term with any operator, so the refusals
   are reachable; no unit test reached them (bisect at a45cd0437:
   match_context's three and explode_sequent's two).  In term_std the
   sequent  s{<H['z]>; x: a >- c}  is
     sequent{sa; context[H]{z; H. hyp{a; x. concl{c}}; xnil}}
   Each case replaces one part of that encoding and prints, for each of
   the three functions, its answer or the refusal.
   Pinned as found: the three do not check the same things.  nth_hyp 2
   answers on a body that ends in no concl (it stops at the hypothesis
   it was asked for), and num_hyps answers on a concl with two subterms;
   explode_sequent refuses both. *)
open Term_sig
open Refiner_std.Refiner
open Term
open TermMan
let v = Lm_symbol.add
let op s = Opname.make_opname [ s ]
let mk s = mk_simple_term (op s) []
let good = mk_sequent_term { sequent_args = mk "sa"; sequent_hyps = SeqHyp.of_list [ Context (v "H", [], [ mk "z" ]); Hypothesis (v "x", mk "a") ]; sequent_concl = mk "c" }
let parts t = let { term_op = o; term_terms = bts } = dest_term t in o, List.map dest_bterm bts
let rebuild o bts = mk_term o (List.map (fun { bvars; bterm } -> mk_bterm bvars bterm) bts)
(* the sequent with its body replaced by [f body] *)
let with_body f =
  match parts good with
  | so, [ args; body ] -> rebuild so [ args; { body with bterm = f body.bterm } ]
  | _ -> failwith "unexpected encoding"
(* the context node's operator and subterms, replaced *)
let with_context f = with_body (fun ctx -> let o, bts = parts ctx in let o, bts = f o bts in rebuild o bts)
let rec at_concl f t =
  let o, bts = parts t in
  if Opname.eq (dest_op o).op_name (Opname.mk_opname "concl" Opname.xperv) then f o bts
  else rebuild o (List.map (fun bt -> if is_var_term bt.bterm then bt else { bt with bterm = at_concl f bt.bterm }) bts)
let show_hyps hs = String.concat "; " (List.map (function Hypothesis (x, _) -> Lm_symbol.string_of_symbol x ^ ": _" | Context (h, _, _) -> "<" ^ Lm_symbol.string_of_symbol h ^ ">") (SeqHyp.to_list hs))
let answer f = try f () with RefineError.RefineError (n, RefineError.TermMatchError (_, s)) -> "refused (" ^ n ^ ": " ^ s ^ ")" | e -> Printexc.to_string e
let case name t =
  Printf.printf "%s:\n  num_hyps: %s\n  nth_hyp 2: %s\n  explode_sequent: %s\n" name
    (answer (fun () -> string_of_int (num_hyps t)))
    (answer (fun () -> ignore (nth_hyp t 2); "a hypothesis"))
    (answer (fun () -> show_hyps (explode_sequent t).sequent_hyps))
let () =
  case "well formed" good;
  case "a context with no variable parameter" (with_context (fun o bts -> mk_op (dest_op o).op_name [], bts));
  case "a context with one subterm" (with_context (fun o bts -> o, [ List.hd bts ]));
  case "a context whose body binds no variable" (with_context (fun o bts ->
      o, List.mapi (fun i bt -> if i = List.length bts - 2 then { bt with bvars = [] } else bt) bts));
  case "a body that ends in no concl" (at_concl (fun _ _ -> mk "c") good);
  case "a concl with two subterms" (at_concl (fun o bts -> rebuild o (bts @ bts)) good)
