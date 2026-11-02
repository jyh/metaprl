(* Three redex shapes no other unit test compiled (2026-11-02 profile of
   refiner/rewrite): a variable bound in the redex and used in it
   (Rewrite_util.svar_index), a free first-order variable
   (rstack_freefo_index), and a context in two sequents of one redex
   (rstack_c_index).  Each rule is applied, in term_std and term_ds, to 300
   generated terms and compared with a model:
     lam{x. 'x} --> id            rewrites exactly the identity function
                                  (not lam{u. 'z}, z free);
     f{'x} --> g{'x}              exactly when the argument is a variable,
                                  which g keeps;
     pair{sequent[s]{ <H> >- 'A<|H|> }; sequent[s]{ <H> >- 'B<|H|> }}
       --> pair{sequent[s]{ <H> >- 'B<|H|> }; sequent[s]{ <H> >- 'A<|H|> }}
                                  exactly when the two sequents have the
                                  same hypotheses, and swaps the
                                  conclusions.
   The generator is a fixed linear congruential sequence, not Random. *)
open Term_sig

let state = ref 8642
let next () = state := (!state * 1103515245 + 12345) land 0x7fffffff; !state lsr 8
let pick n = next () mod n

(* Small closed terms over c, g{_}, and the variables in scope. *)
type d = V of string | C | G of d | Lam of string * d
let rec gen env depth =
  match pick (if depth = 0 then 2 else 4) with
  | 0 -> C
  | 1 -> if env = [] then C else V (List.nth env (pick (List.length env)))
  | 2 -> G (gen env (depth - 1))
  | _ -> let x = Printf.sprintf "y%d" depth in Lam (x, gen (x :: env) (depth - 1))
let rec show = function
  | V v -> "'" ^ v | C -> "c" | G a -> "g{" ^ show a ^ "}" | Lam (x, a) -> "lam{" ^ x ^ ". " ^ show a ^ "}"

module Rw (R : Refiner_sig.RefinerSig) = struct
  open R.Term
  open R.TermMan
  let op s = Opname.make_opname [ s ]
  let v = Lm_symbol.add
  let rec build = function
    | V x -> mk_var_term (v x)
    | C -> mk_simple_term (op "c") []
    | G a -> mk_simple_term (op "g") [ build a ]
    | Lam (x, a) -> mk_term (mk_op (op "lam") []) [ mk_bterm [ v x ] (build a) ]
  let sq hyps concl = mk_sequent_term { sequent_args = mk_simple_term (op "s") []; sequent_hyps = R.Term.SeqHyp.of_list hyps; sequent_concl = concl }
  let hyps hs = List.map (fun (x, a) -> Hypothesis (v x, build a)) hs
  let rec show_term t =
    if is_var_term t then "'" ^ Lm_symbol.string_of_symbol (dest_var t)
    else if is_sequent_term t then
      let s = explode_sequent t in
      "sequent{ " ^ String.concat "; " (List.map (function Hypothesis (x, a) -> Lm_symbol.string_of_symbol x ^ ": " ^ show_term a | Context (x, _, _) -> "<" ^ Lm_symbol.string_of_symbol x ^ ">")
                                           (R.Term.SeqHyp.to_list s.sequent_hyps)) ^ " >- " ^ show_term s.sequent_concl ^ " }"
    else
      let { term_op; term_terms } = dest_term t in
      let name = String.concat "!" (Opname.dest_opname (dest_op term_op).op_name) in
      if term_terms = [] then name
      else name ^ "{" ^ String.concat "; " (List.map (fun b -> let { bvars; bterm } = dest_bterm b in
                                                 (if bvars = [] then "" else String.concat "," (List.map Lm_symbol.string_of_symbol bvars) ^ ". ") ^ show_term bterm) term_terms) ^ "}"
  let rule redex contractum = R.Rewrite.term_rewrite Rewrite_sig.Strict R.Rewrite.empty_args_spec [ redex ] [ contractum ]
  let apply rw t = try Some (String.concat " | " (List.map show_term (R.Rewrite.apply_rewrite rw R.Rewrite.empty_args t []))) with _ -> None
  let so x cs = mk_so_var_term (v x) (List.map v cs) []
  let f_of a = mk_simple_term (op "f") [ build a ]
  let pair_of h1 c1 h2 c2 = mk_simple_term (op "pair") [ sq (hyps h1) (build c1); sq (hyps h2) (build c2) ]
  let ctx = Context (v "H", [], [])
  let identity = rule (build (Lam ("x", V "x"))) (mk_simple_term (op "id") [])
  let free = rule (mk_simple_term (op "f") [ mk_var_term (v "x") ]) (mk_simple_term (op "g") [ mk_var_term (v "x") ])
  let pair = rule (mk_simple_term (op "pair") [ sq [ ctx ] (so "A" [ "H" ]); sq [ ctx ] (so "B" [ "H" ]) ])
      (mk_simple_term (op "pair") [ sq [ ctx ] (so "B" [ "H" ]); sq [ ctx ] (so "A" [ "H" ]) ])
end

module Std = Rw (Refiner_std.Refiner)
module Ds = Rw (Refiner_ds.Refiner)

let run name n mk =
  let agree = ref 0 and model = ref 0 and rewrote = ref 0 and first = ref None in
  for _ = 1 to n do
    let what, s, d, want = mk () in
    if s = d then incr agree;
    if d <> None then incr rewrote;
    if d = want && s = want then incr model
    else if !first = None then first := Some (what, (match want with None -> "refused" | Some w -> w), (match d with None -> "refused" | Some w -> w))
  done;
  Printf.printf "%s\n  std and ds agree on %d of %d; the model on %d (it rewrites %d)\n" name !agree n !model !rewrote;
  match !first with None -> () | Some (w, m, g) -> Printf.printf "    first difference, %s: model %s, got %s\n" w m g

let () =
  run "lam{x. 'x} --> id" 300 (fun () ->
      let t = match pick 3 with 0 -> Lam ("u", V "u") | 1 -> Lam ("u", V "z") | _ -> Lam ("u", gen [ "u" ] 2) in
      show t, Std.apply Std.identity (Std.build t), Ds.apply Ds.identity (Ds.build t),
      (match t with Lam (x, V y) when x = y -> Some "id" | _ -> None));
  run "f{'x} --> g{'x} (x free)" 300 (fun () ->
      let a = if pick 2 = 0 then V [| "p"; "q" |].(pick 2) else gen [] 2 in
      "f{" ^ show a ^ "}", Std.apply Std.free (Std.f_of a), Ds.apply Ds.free (Ds.f_of a),
      (match a with V x -> Some ("g{'" ^ x ^ "}") | _ -> None));
  let hs () = List.init (pick 3) (fun i -> Printf.sprintf "h%d" i, if pick 2 = 0 then C else G C) in
  run "pair of sequents sharing <H>" 300 (fun () ->
      let h1 = hs () in
      let h2 = if pick 2 = 0 then h1 else hs () in
      let c1 = gen (List.map fst h1) 1 and c2 = gen (List.map fst h2) 1 in
      let s_t = Std.pair_of h1 c1 h2 c2 and d_t = Ds.pair_of h1 c1 h2 c2 in
      let seq hs c = "sequent{ " ^ String.concat "; " (List.map (fun (x, a) -> x ^ ": " ^ show a) hs) ^ " >- " ^ show c ^ " }" in
      "pair{" ^ seq h1 c1 ^ "; " ^ seq h2 c2 ^ "}", Std.apply Std.pair s_t, Ds.apply Ds.pair d_t,
      (if h1 = h2 then Some ("pair{" ^ seq h1 c2 ^ "; " ^ seq h1 c1 ^ "}") else None))
