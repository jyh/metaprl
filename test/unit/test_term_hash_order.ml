(* Term_hash_code.hash_term ("hashing operations that respect
   alpha-equivalence"; the filter's grammar and cache digests use it) and
   Term_order.TermOrder.compare_terms, on the configured refiner, over
   test_term_differential's terms and alpha-renamed copies of them:
     - hash_term t = hash_term (a renamed copy of t);
     - how many distinct terms (by alpha_equal) share a hash (reported,
       not a law);
     - compare_terms: 0 on t and t, sign(compare a b) = -sign(compare b a),
       transitivity on triples, and whether compare = 0 coincides with
       alpha_equal (on t and its renamed copy, and on random pairs).
   The generator is a fixed linear congruential sequence, not Random. *)
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

(* The same description with every bound name renamed (alpha-variant). *)
let rec rename = function
  | Var v -> Var v
  | SOVar (v, cs, ts) -> SOVar (v, cs, List.map rename ts)
  | Op (o, ts) -> Op (o, List.map rename ts)
  | Bind (x, t) -> Bind (x ^ "'", rename (subst x (x ^ "'") t))
  | Seq (a, hs, c) ->
      let rec go acc c = function
        | [] -> Seq (a, List.rev acc, rename c)
        | Hyp (v, t) :: hs ->
            let v' = v ^ "'" in
            go (Hyp (v', rename t) :: acc) (subst v v' c) (List.map (subst_hyp v v') hs)
        | Ctx (k, cs, ts) :: hs -> go (Ctx (k, cs, List.map rename ts) :: acc) c hs
      in
      go [] c hs
and subst x y = function
  | Var v -> Var (if v = x then y else v)
  | SOVar (v, cs, ts) -> SOVar (v, cs, List.map (subst x y) ts)
  | Op (o, ts) -> Op (o, List.map (subst x y) ts)
  | Bind (z, t) -> if z = x then Bind (z, t) else Bind (z, subst x y t)
  | Seq (a, hs, c) ->
      let rec go acc = function
        | [] -> Seq (a, List.rev acc, subst x y c)
        | Hyp (v, t) :: hs when v = x -> Seq (a, List.rev_append acc (Hyp (v, subst x y t) :: hs), c)
        | Hyp (v, t) :: hs -> go (Hyp (v, subst x y t) :: acc) hs
        | Ctx (k, cs, ts) :: hs -> go (Ctx (k, cs, List.map (subst x y) ts) :: acc) hs
      in
      go [] hs
and subst_hyp x y = function
  | Hyp (v, t) -> Hyp (v, subst x y t)
  | Ctx (k, cs, ts) -> Ctx (k, cs, List.map (subst x y) ts)

module Check (R : Refiner_sig.RefinerSig) = struct
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

  (* As show, but bound variables print by binding position, so that
     alpha-equivalent terms print the same. *)
  let rec cshow env t =
    let name v = try "#" ^ string_of_int (List.assoc v env) with Not_found -> string_of_symbol v in
    let bind env v = (v, List.length env) :: env in
    if is_sequent_term t then
      let s = explode_sequent t in
      let e = ref env in
      let hs = List.map (function
          | Hypothesis (v, a) -> let a = cshow !e a in e := bind !e v; "#" ^ string_of_int (List.length !e - 1) ^ ": " ^ a
          | Context (v, cs, args) ->
              let r = "<" ^ string_of_symbol v ^ "<|" ^ String.concat ";" (List.map string_of_symbol cs) ^ "|>["
                      ^ String.concat "; " (List.map (cshow !e) args) ^ "]>" in
              e := bind !e v; r)
          (R.Term.SeqHyp.to_list s.sequent_hyps) in
      "sequent[" ^ cshow env s.sequent_args ^ "]{ " ^ String.concat "; " hs ^ " >- " ^ cshow !e s.sequent_concl ^ " }"
    else if is_var_term t then "'" ^ name (dest_var t)
    else if is_so_var_term t then
      let v, cs, args = dest_so_var t in
      string_of_symbol v ^ "<|" ^ String.concat ";" (List.map string_of_symbol cs) ^ "|>["
      ^ String.concat "; " (List.map (cshow env) args) ^ "]"
    else
      let { term_op; term_terms } = dest_term t in
      let opn = String.concat "!" (Opname.dest_opname (dest_op term_op).op_name) in
      if term_terms = [] then opn
      else opn ^ "{" ^ String.concat "; " (List.map (fun b ->
          let { bvars; bterm } = dest_bterm b in
          let env' = List.fold_left bind env bvars in
          (if bvars = [] then "" else String.concat "," (List.map name bvars |> List.map (fun _ -> "_")) ^ ". ") ^ cshow env' bterm)
          term_terms) ^ "}"

  let safe f = try f () with _ -> "(raises)"
end

module C = Check (Refiner.Refiner)
module O = Term_order.TermOrder (Refiner.Refiner)

let () =
  let n = 1000 in
  let ds = Array.init n (fun _ -> gen 4 [] 0) in
  let ts = Array.map C.build ds and rs = Array.map (fun d -> C.build (rename d)) ds in
  let count f = Array.fold_left (fun a b -> if b then a + 1 else a) 0 (Array.init n f) in
  let first f = let r = ref None in Array.iteri (fun i _ -> if !r = None && not (f i) then r := Some i) ts; !r in
  let alpha a b = Refiner.Refiner.TermSubst.alpha_equal a b in
  let hash = Term_hash_code.hash_term in
  let line name f =
    Printf.printf "%-52s %4d of %d\n" name (count f) n;
    match first f with None -> () | Some i -> Printf.printf "  first difference, term %d: %s\n" i (C.show ts.(i)) in
  line "renamed copy is alpha_equal (the premise)" (fun i -> alpha ts.(i) rs.(i));
  line "hash_term t = hash_term (renamed t)" (fun i -> hash ts.(i) = hash rs.(i));
  let sign x = Stdlib.compare x 0 in
  line "compare_terms t t = 0" (fun i -> O.compare_terms ts.(i) ts.(i) = 0);
  line "compare_terms t (renamed t) = 0" (fun i -> O.compare_terms ts.(i) rs.(i) = 0);
  let j i = (i * 7 + 3) mod n and k i = (i * 13 + 5) mod n in
  line "sign (compare a b) = - sign (compare b a)" (fun i -> sign (O.compare_terms ts.(i) ts.(j i)) = - sign (O.compare_terms ts.(j i) ts.(i)));
  line "compare a b = 0 exactly when alpha_equal a b" (fun i -> (O.compare_terms ts.(i) ts.(j i) = 0) = alpha ts.(i) ts.(j i));
  line "transitive on (a, b, c)" (fun i ->
      let a = ts.(i) and b = ts.(j i) and c = ts.(k i) in
      let ab = O.compare_terms a b and bc = O.compare_terms b c and ac = O.compare_terms a c in
      not (ab <= 0 && bc <= 0) || ac <= 0);
  (* distinct terms sharing a hash: a measure, not a law *)
  let tbl = Hashtbl.create 1024 in
  Array.iter (fun t -> let h = hash t in
      let l = try Hashtbl.find tbl h with Not_found -> [] in
      if not (List.exists (alpha t) l) then Hashtbl.replace tbl h (t :: l)) ts;
  let distinct = Hashtbl.fold (fun _ l a -> a + List.length l) tbl 0 in
  let shared = Hashtbl.fold (fun _ l a -> if List.length l > 1 then a + List.length l else a) tbl 0 in
  Printf.printf "distinct terms %d, in %d hash values; %d share a hash value with another\n" distinct (Hashtbl.length tbl) shared
