(* Term_copy2_weak's other half (test_term_copy2_weak covers the global
   convert / revert): the p_* functions over an explicit table (p_create),
   weaken / compare on indices, and the meta-term and msequent copies, none
   entered by a unit test (the 11-02 reflib coverage page). Over 500 terms
   from the same generator as test_term_copy2_weak, in one table:
     - p_convert of the std term is the ds term built from the description,
       p_revert of the ds term is the std term, and p_revert (p_convert t) = t;
     - p_add_src then p_retrieve_src / p_retrieve_dst give back the std term
       and the ds term; p_add_dst of the ds term gives an index that
       compares equal (weaken, compare) to the std term's;
     - a second term's index compares unequal unless the terms are the same;
     - a meta-term (MetaImplies of two theorems) and an msequent (a goal and
       two assumptions) through p_convert_meta / p_revert_meta and
       p_convert_msequent / p_revert_msequent, and their add / retrieve /
       weaken / compare.
   Shown structurally, as in test_term_copy2_weak. *)
open Lm_symbol
open Term_sig

(* A 31-bit linear congruential generator (glibc's constants). *)
let state = ref 12345
let next () = state := (!state * 1103515245 + 12345) land 0x7fffffff; !state lsr 8
let pick n = next () mod n

(* A term description, built in each implementation by the functor below. *)
type desc =
  | Var of string
  | SOVar of string * string list * desc list
  | Op of string * desc list
  | Bind of string * desc
  | Seq of string * hyp list * desc
and hyp = Hyp of string * desc | Ctx of string * string list * desc list

let conts () = List.filter (fun _ -> pick 2 = 0) [ "H"; "S" ]

let rec gen depth env n =
  let leaf () =
    match pick 3 with
    | 0 when env <> [] -> Var (List.nth env (pick (List.length env)))
    | 1 -> Var "z"
    | _ -> Op ("c", [])
  in
  if depth <= 0 then leaf ()
  else
    match pick 7 with
    | 0 | 1 -> leaf ()
    | 2 -> SOVar ((if pick 2 = 0 then "A" else "B"), conts (), List.init (pick 3) (fun _ -> gen (depth - 1) env n))
    | 3 -> Op ("f", List.init (1 + pick 2) (fun _ -> gen (depth - 1) env n))
    | 4 -> let x = Printf.sprintf "x%d" n in Bind (x, gen (depth - 1) (x :: env) (n + 1))
    | _ ->
        let rec hyps i env acc =
          if i = 0 then List.rev acc, env
          else if pick 3 = 0 then
            let k = Printf.sprintf "K%d" (n + i) in
            hyps (i - 1) (k :: env) (Ctx (k, conts (), List.init (pick 3) (fun _ -> gen (depth - 2) env n)) :: acc)
          else
            let v = Printf.sprintf "v%d" (n + i) in
            hyps (i - 1) (v :: env) (Hyp (v, gen (depth - 2) env n) :: acc)
        in
        let hs, env' = hyps (pick 4) env [] in
        Seq ((if pick 2 = 0 then "sa" else "sb"), hs, gen (depth - 1) env' (n + 10))

module B (R : Refiner_sig.RefinerSig) = struct
  open R.Term
  open R.TermMan
  let op s = Opname.make_opname [ s ]
  let rec build = function
    | Var v -> mk_var_term (add v)
    | SOVar (v, cs, ts) -> mk_so_var_term (add v) (List.map add cs) (List.map build ts)
    | Op (o, ts) -> mk_simple_term (op o) (List.map build ts)
    | Bind (x, t) -> mk_term (mk_op (op "lam") []) [ mk_bterm [ add x ] (build t) ]
    | Seq (a, hs, c) ->
        mk_sequent_term
          { sequent_args = mk_simple_term (op a) [];
            sequent_hyps = R.Term.SeqHyp.of_list (List.map (function
                | Hyp (v, t) -> Hypothesis (add v, build t)
                | Ctx (k, cs, ts) -> Context (add k, List.map add cs, List.map build ts)) hs);
            sequent_concl = build c }

  let rec show t =
    if is_sequent_term t then
      let s = explode_sequent t in
      "sequent[" ^ show s.sequent_args ^ "]{ " ^ String.concat "; " (List.map (function
          | Hypothesis (v, a) -> string_of_symbol v ^ ": " ^ show a
          | Context (v, cs, args) ->
              "<" ^ string_of_symbol v ^ "<|" ^ String.concat ";" (List.map string_of_symbol cs) ^ "|>["
              ^ String.concat "; " (List.map show args) ^ "]>")
          (R.Term.SeqHyp.to_list s.sequent_hyps)) ^ " >- " ^ show s.sequent_concl ^ " }"
    else if is_var_term t then "'" ^ string_of_symbol (dest_var t)
    else if is_so_var_term t then
      let v, cs, args = dest_so_var t in
      string_of_symbol v ^ "<|" ^ String.concat ";" (List.map string_of_symbol cs) ^ "|>["
      ^ String.concat "; " (List.map show args) ^ "]"
    else
      let { term_op; term_terms } = dest_term t in
      let name = String.concat "!" (Opname.dest_opname (dest_op term_op).op_name) in
      if term_terms = [] then name
      else name ^ "{" ^ String.concat "; " (List.map (fun b ->
          let { bvars; bterm } = dest_bterm b in
          (if bvars = [] then "" else String.concat "," (List.map string_of_symbol bvars) ^ ". ") ^ show bterm)
          term_terms) ^ "}"
end

module S = B (Refiner_std.Refiner)
module D = B (Refiner_ds.Refiner)
module C = Term_copy2_weak.TermCopy2Weak (Refiner_std.Refiner) (Refiner_ds.Refiner)
module SR = Refiner_std.Refiner.Refine
module DR = Refiner_ds.Refiner.Refine

let rec smeta = function
  | MetaTheorem t -> S.show t
  | MetaImplies (a, b) -> "(" ^ smeta a ^ " --> " ^ smeta b ^ ")"
  | MetaFunction (v, a, b) -> "(" ^ S.show v ^ " : " ^ smeta a ^ " --> " ^ smeta b ^ ")"
  | MetaIff (a, b) -> "(" ^ smeta a ^ " <--> " ^ smeta b ^ ")"
  | MetaLabeled (l, a) -> l ^ ":" ^ smeta a
let rec dmeta = function
  | MetaTheorem t -> D.show t
  | MetaImplies (a, b) -> "(" ^ dmeta a ^ " --> " ^ dmeta b ^ ")"
  | MetaFunction (v, a, b) -> "(" ^ D.show v ^ " : " ^ dmeta a ^ " --> " ^ dmeta b ^ ")"
  | MetaIff (a, b) -> "(" ^ dmeta a ^ " <--> " ^ dmeta b ^ ")"
  | MetaLabeled (l, a) -> l ^ ":" ^ dmeta a
let smseq m = let g, hs = SR.dest_msequent m in S.show g ^ " | " ^ String.concat ", " (List.map S.show hs)
let dmseq m = let g, hs = DR.dest_msequent m in D.show g ^ " | " ^ String.concat ", " (List.map D.show hs)

let () =
  let n = 500 in
  let tbl = C.p_create 17 in
  let names = [ "p_convert std = ds"; "p_revert ds = std"; "p_revert (p_convert t) = t";
                "p_add_src, p_retrieve_src = std"; "p_add_src, p_retrieve_dst = ds";
                "p_add_dst index compares equal"; "another term compares as equality";
                "meta: convert, revert, round trip"; "meta: add/retrieve both sides, compare";
                "msequent: convert, revert, round trip"; "msequent: add/retrieve both sides, compare" ] in
  let k = List.length names in
  let ok = Array.make k 0 and first = Array.make k None in
  let note i b d = if b then ok.(i) <- ok.(i) + 1 else if first.(i) = None then first.(i) <- Some d in
  let safe f = try f () with e -> "raised " ^ Printexc.to_string e in
  let prev = ref None in
  for _ = 1 to n do
    let d = gen 4 [] 0 and d2 = gen 3 [] 0 in
    let s = S.build d and t = D.build d in
    note 0 (safe (fun () -> D.show (C.p_convert tbl s)) = D.show t) d;
    note 1 (safe (fun () -> S.show (C.p_revert tbl t)) = S.show s) d;
    note 2 (safe (fun () -> S.show (C.p_revert tbl (C.p_convert tbl s))) = S.show s) d;
    let i = C.p_add_src tbl s in
    note 3 (S.show (C.p_retrieve_src tbl i) = S.show s) d;
    note 4 (D.show (C.p_retrieve_dst tbl i) = D.show t) d;
    let j = C.p_add_dst tbl t in
    note 5 (C.compare (C.weaken i) (C.weaken j)) d;
    (match !prev with
     | Some (d', i') -> note 6 (C.compare (C.weaken i) (C.weaken i') = (S.show (S.build d') = S.show s)) d
     | None -> ());
    prev := Some (d, i);
    let s2 = S.build d2 and t2 = D.build d2 in
    let sm = MetaImplies (MetaTheorem s, MetaTheorem s2)
    and dm = MetaImplies (MetaTheorem t, MetaTheorem t2) in
    note 7 (safe (fun () -> dmeta (C.p_convert_meta tbl sm)) = dmeta dm
            && safe (fun () -> smeta (C.p_revert_meta tbl dm)) = smeta sm
            && safe (fun () -> smeta (C.p_revert_meta tbl (C.p_convert_meta tbl sm))) = smeta sm) d;
    let mi = C.p_add_meta_src tbl sm and mj = C.p_add_meta_dst tbl dm in
    note 8 (smeta (C.p_retrieve_meta_src tbl mi) = smeta sm && dmeta (C.p_retrieve_meta_dst tbl mi) = dmeta dm
            && C.compare_meta (C.weaken_meta mi) (C.weaken_meta mj)) d;
    let sq = SR.mk_msequent s [ s2; s ] and dq = DR.mk_msequent t [ t2; t ] in
    note 9 (safe (fun () -> dmseq (C.p_convert_msequent tbl sq)) = dmseq dq
            && safe (fun () -> smseq (C.p_revert_msequent tbl dq)) = smseq sq
            && safe (fun () -> smseq (C.p_revert_msequent tbl (C.p_convert_msequent tbl sq))) = smseq sq) d;
    let qi = C.p_add_msequent_src tbl sq and qj = C.p_add_msequent_dst tbl dq in
    note 10 (smseq (C.p_retrieve_msequent_src tbl qi) = smseq sq && dmseq (C.p_retrieve_msequent_dst tbl qi) = dmseq dq
             && C.compare_msequent (C.weaken_msequent qi) (C.weaken_msequent qj)) d
  done;
  List.iteri (fun i name ->
      Printf.printf "%-44s %d of %d\n" name ok.(i) (if i = 6 then n - 1 else n);
      match first.(i) with
      | None -> ()
      | Some d -> Printf.printf "  first that does not: %s\n" (S.show (S.build d))) names
