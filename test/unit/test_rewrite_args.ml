(* A rewrite compiled with an argument (spec_ints): the length of a context,
   as rules such as thin 'H take it.  Every other unit test passes
   empty_args_spec.  The rule
     sequent[sa]{ <H>; x: 'A<|H|>; <J<|H|>> >- 'C<|H;J|> }
       --> sequent[sb]{ <H>; <J<|H|>> >- 'C<|H;J|> }
   is compiled with H as an int argument and applied, in term_std and
   term_ds, to random sequents of 0-5 hypotheses with each argument k from
   -5 to 6.  The argument places x (Rewrite_match_redex, arg_ints): k > 0
   makes x hypothesis k; k <= 0 leaves -k hypotheses after x.  The model:
   the rule applies when that hypothesis exists, and neither the later
   hypotheses nor the conclusion mention x (J and C do not depend on it);
   the result is the sequent without it.  The generator is a fixed linear
   congruential sequence, not Random. *)
open Term_sig

let state = ref 2468
let next () = state := (!state * 1103515245 + 12345) land 0x7fffffff; !state lsr 8
let pick n = next () mod n

(* Hypothesis i is v<i>: c or v<i>: f{'v<j>} for an earlier j; the
   conclusion is c or g{'v<j>}. *)
type seq = { hyps : int option list; concl : int option }
let gen () =
  let n = pick 6 in
  let hyps = List.init n (fun i -> if i > 0 && pick 2 = 0 then Some (pick i) else None) in
  { hyps; concl = (if n > 0 && pick 3 > 0 then Some (pick n) else None) }

let show_seq names hyps concl =
  "{ " ^ String.concat "; " (List.map2 (fun v h -> v ^ ": " ^ h) names hyps) ^ " >- " ^ concl ^ " }"
let mshow d = show_seq (List.mapi (fun i _ -> Printf.sprintf "v%d" i) d.hyps)
    (List.map (function None -> "c" | Some j -> Printf.sprintf "f{'v%d}" j) d.hyps)
    (match d.concl with None -> "c" | Some j -> Printf.sprintf "g{'v%d}" j)

(* The model: the index of x, then the check that nothing later mentions it. *)
let model d k =
  let n = List.length d.hyps in
  let p = if k > 0 then k - 1 else n + k in
  if p < 0 || p >= n then None
  else
    let later = List.filteri (fun i _ -> i > p) d.hyps in
    if List.mem (Some p) later || d.concl = Some p then None
    else
      let keep = List.filteri (fun i _ -> i <> p) (List.mapi (fun i h -> i, h) d.hyps) in
      Some (show_seq (List.map (fun (i, _) -> Printf.sprintf "v%d" i) keep)
              (List.map (function (_, None) -> "c" | (_, Some j) -> Printf.sprintf "f{'v%d}" j) keep)
              (match d.concl with None -> "c" | Some j -> Printf.sprintf "g{'v%d}" j))

module Rw (R : Refiner_sig.RefinerSig) = struct
  open R.Term
  open R.TermMan
  let op s = Opname.make_opname [ s ]
  let v = Lm_symbol.add
  let sq a hyps concl =
    mk_sequent_term { sequent_args = mk_simple_term (op a) []; sequent_hyps = R.Term.SeqHyp.of_list hyps; sequent_concl = concl }
  let so x cs = mk_so_var_term (v x) (List.map v cs) []
  let rule =
    let redex = sq "sa" [ Context (v "H", [], []); Hypothesis (v "x", so "A" [ "H" ]); Context (v "J", [ v "H" ], []) ] (so "C" [ "H"; "J" ]) in
    let contractum = sq "sb" [ Context (v "H", [], []); Context (v "J", [ v "H" ], []) ] (so "C" [ "H"; "J" ]) in
    R.Rewrite.term_rewrite Rewrite_sig.Strict { Rewrite_sig.spec_ints = [| v "H" |]; spec_addrs = [||] } [ redex ] [ contractum ]
  let build d =
    let c = mk_simple_term (op "c") [] in
    sq "sa" (List.mapi (fun i h ->
        Hypothesis (v (Printf.sprintf "v%d" i), match h with None -> c | Some j -> mk_simple_term (op "f") [ mk_var_term (v (Printf.sprintf "v%d" j)) ])) d.hyps)
      (match d.concl with None -> c | Some j -> mk_simple_term (op "g") [ mk_var_term (v (Printf.sprintf "v%d" j)) ])
  let rec show t =
    if is_var_term t then "'" ^ Lm_symbol.string_of_symbol (dest_var t)
    else
      let { term_op; term_terms } = dest_term t in
      let name = String.concat "!" (Opname.dest_opname (dest_op term_op).op_name) in
      if term_terms = [] then name else name ^ "{" ^ String.concat "; " (List.map (fun b -> show (dest_bterm b).bterm) term_terms) ^ "}"
  let show_sequent t =
    let s = explode_sequent t in
    let hyps = List.map (function Hypothesis (x, a) -> Lm_symbol.string_of_symbol x, show a | Context (x, _, _) -> "<" ^ Lm_symbol.string_of_symbol x ^ ">", "") (R.Term.SeqHyp.to_list s.sequent_hyps) in
    show_seq (List.map fst hyps) (List.map snd hyps) (show s.sequent_concl)
  let apply d k =
    try Some (String.concat " | " (List.map show_sequent
                (R.Rewrite.apply_rewrite rule ({ Rewrite_sig.arg_ints = [| k |]; arg_addrs = [||] }, Lm_symbol.SymbolSet.empty) (build d) [])))
    with _ -> None
end

module Std = Rw (Refiner_std.Refiner)
module Ds = Rw (Refiner_ds.Refiner)

let () =
  let n = 200 in
  let tried = ref 0 and agree = ref 0 and modeled = ref 0 and rewrote = ref 0 and first = ref None and firstm = ref None in
  for _ = 1 to n do
    let d = gen () in
    for k = -5 to 6 do
      incr tried;
      let s = Std.apply d k and t = Ds.apply d k in
      if s = t then incr agree else if !first = None then first := Some (mshow d, k);
      if t <> None then incr rewrote;
      if t = model d k then incr modeled
      else if !firstm = None then firstm := Some (mshow d, k, (match model d k with None -> "refused" | Some s -> s), (match t with None -> "refused" | Some s -> s))
    done
  done;
  Printf.printf "%d sequents, arguments -5..6: %d cases, rewrote %d\n" n !tried !rewrote;
  Printf.printf "std and ds agree on %d of %d\n" !agree !tried;
  (match !first with None -> () | Some (d, k) -> Printf.printf "  first difference: %s with %d\n" d k);
  Printf.printf "the model agrees on %d of %d\n" !modeled !tried;
  match !firstm with None -> () | Some (d, k, m, g) -> Printf.printf "  first difference: %s with %d: model %s, got %s\n" d k m g
