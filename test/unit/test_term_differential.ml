(* metaprl has two term implementations, term_std and term_ds (the one the
   refiner uses).  On 2026-10-29 a TERMS = std proof census lost 90 proofs
   to four term_std defects (#56, #57, #58), each of which showed only as a
   disagreement with term_ds, and each was found from one failing proof.
   This test looks for such disagreements directly: it builds the same
   pseudo-random terms in both implementations (sequents with hypotheses
   and context hypotheses, second-order variables with contexts lists and
   arguments, binders), and for each term compares
     - the term itself, printed structurally;
     - subterm_addresses, and term_subterm at each address;
     - find_subterm for variables, and term_subterm at each address found;
     - free_vars_set;
     - alpha_equal against a copy whose bound variables are renamed;
     - the number of terms TermOp.iter_down visits;
     - TermSubst.subst of g{'x0; A['x0]} for the free variable 'z (bound
       variables named x0 would capture it, so this exercises renaming),
       compared up to the names of bound variables: term_std renames a
       binder named x0 even where 'z does not occur, term_ds does not.
   It prints, per check, how many terms agree, and the first term on which
   a check disagrees.
   Then, on the same terms with every second 'z renamed 'y, it compares
   std, ds and a model (the substitution done on the description) for
     - TermSubst.subst of 'y,'z by 'z,'y (simultaneous, not one after the
       other: a sequential mutant agrees on 1510 of 2000);
     - TermSubst.subst of 'z,'z by g{c},'w (the first is used: a mutant
       using the last agrees on 904);
     - TermSubst.match_terms of the term with an instance of it, split by
       whether the term holds a sequent (a mutant that drops 'y's binding
       agrees on 959 of 969 and 551 of 1031).
   term_ds's match_terms raises Invalid_argument on any sequent, by its
   own code; term_std matches them.  Last, a few match_terms cases random
   instances never reach, printed for both: ds matches the bound variable
   of lam x.f{'x} against c in lam y.f{c}, where std refuses.  The output
   records that as it is (a candidate defect, not yet changed).  The two
   parts share the term sequence, so the first part's lines are unchanged.
   The generator is a fixed linear congruential sequence, not Random, so
   the terms are the same on every OCaml. *)
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

(* The same description with every second free 'z renamed 'y, so terms
   have two free first-order variables ('y and 'z are never bound). *)
let yz d =
  let k = ref 0 in
  let rec go = function
    | Var "z" -> incr k; if !k mod 2 = 0 then Var "y" else Var "z"
    | Var v -> Var v
    | SOVar (v, cs, ts) -> SOVar (v, cs, List.map go ts)
    | Op (o, ts) -> Op (o, List.map go ts)
    | Bind (x, t) -> Bind (x, go t)
    | Seq (a, hs, c) ->
        let hs = List.map (function Hyp (v, t) -> Hyp (v, go t) | Ctx (k, cs, ts) -> Ctx (k, cs, List.map go ts)) hs in
        Seq (a, hs, go c)
  in
  go d

(* Replace the free first-order variables of a description (models). *)
let rec replace f = function
  | Var v -> (match f v with Some d -> d | None -> Var v)
  | SOVar (v, cs, ts) -> SOVar (v, cs, List.map (replace f) ts)
  | Op (o, ts) -> Op (o, List.map (replace f) ts)
  | Bind (x, t) -> Bind (x, replace f t)
  | Seq (a, hs, c) ->
      Seq (a, List.map (function
          | Hyp (v, t) -> Hyp (v, replace f t)
          | Ctx (k, cs, ts) -> Ctx (k, cs, List.map (replace f) ts)) hs, replace f c)

let rec occurs v = function
  | Var w -> v = w
  | SOVar (_, _, ts) | Op (_, ts) -> List.exists (occurs v) ts
  | Bind (_, t) -> occurs v t
  | Seq (_, hs, c) ->
      occurs v c || List.exists (function Hyp (_, t) -> occurs v t | Ctx (_, _, ts) -> List.exists (occurs v) ts) hs

let rec has_seq = function
  | Var _ -> false
  | SOVar (_, _, ts) | Op (_, ts) -> List.exists has_seq ts
  | Bind (_, t) -> has_seq t
  | Seq _ -> true

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
  let at t a = safe (fun () -> show (R.TermAddr.term_subterm t a))
  let checks d =
    let t = build d in
    let c0 = safe (fun () -> show t) in
    let c1 = safe (fun () -> String.concat " | " (List.map (at t) (R.TermAddr.subterm_addresses t))) in
    let c2 = safe (fun () -> String.concat " | " (List.map (at t)
          (R.TermAddr.find_subterm t (fun s _ -> is_var_term s || is_so_var_term s)))) in
    let c3 = safe (fun () -> String.concat " " (List.sort Stdlib.compare (List.map string_of_symbol
          (SymbolSet.elements (R.TermSubst.free_vars_set t))))) in
    let c4 = safe (fun () -> string_of_bool (R.TermSubst.alpha_equal t (build (rename d)))) in
    let c5 = safe (fun () -> let n = ref 0 in R.TermOp.iter_down (fun _ -> incr n) t; string_of_int !n) in
    let c6 = safe (fun () -> cshow [] (R.TermSubst.subst t [ add "z" ] [ build (Op ("g", [ Var "x0"; SOVar ("A", [], [ Var "x0" ]) ])) ])) in
    [ c0; c1; c2; c3; c4; c5; c6 ]

  (* Substitution of several variables at once, and matching.  Each returns
     the result and the model's answer, printed the same way. *)
  let g = Op ("g", [ Op ("c", []) ])
  let showsubst s =
    String.concat ", " (List.sort Stdlib.compare (List.map (fun (v, t) -> string_of_symbol v ^ ":=" ^ cshow [] t) s))
  let more d =
    let d = yz d in
    let t = build d in
    let swap v = match v with "y" -> Some (Var "z") | "z" -> Some (Var "y") | _ -> None in
    let c7 = safe (fun () -> cshow [] (R.TermSubst.subst t [ add "y"; add "z" ] [ mk_var_term (add "z"); mk_var_term (add "y") ])),
             safe (fun () -> cshow [] (build (replace swap d))) in
    let first v = match v with "z" -> Some g | _ -> None in
    let c8 = safe (fun () -> cshow [] (R.TermSubst.subst t [ add "z"; add "z" ] [ build g; build (Var "w") ])),
             safe (fun () -> cshow [] (build (replace first d))) in
    let inst v = match v with "y" -> Some g | "z" -> Some (Var "w") | _ -> None in
    let c9 = safe (fun () -> showsubst (R.TermSubst.match_terms [] t (build (replace inst d)))),
             safe (fun () -> showsubst (List.filter_map (fun v -> if occurs v d then Option.map (fun e -> add v, build e) (inst v) else None) [ "y"; "z" ])) in
    [ c7; c8; c9 ]

  (* Matching cases the random terms never reach: in an instance built by
     substitution, a bound variable always meets a bound variable. *)
  let hand =
    let c = Op ("c", []) in
    [ "lam x.f{'x} with lam y.f{'y}", Bind ("x", Op ("f", [ Var "x" ])), Bind ("y", Op ("f", [ Var "y" ]));
      "lam x.f{'x} with lam y.f{c}", Bind ("x", Op ("f", [ Var "x" ])), Bind ("y", Op ("f", [ c ]));
      "f{'y; 'y} with f{c; c}", Op ("f", [ Var "y"; Var "y" ]), Op ("f", [ c; c ]);
      "f{'y; 'y} with f{c; 'w}", Op ("f", [ Var "y"; Var "y" ]), Op ("f", [ c; Var "w" ]);
      "lam x.f{'y} with lam x.f{'x}", Bind ("x", Op ("f", [ Var "y" ])), Bind ("x", Op ("f", [ Var "x" ]));
      "f{'y} with f{'y}", Op ("f", [ Var "y" ]), Op ("f", [ Var "y" ]) ]
    |> List.map (fun (name, p, i) -> name, safe (fun () -> "[" ^ showsubst (R.TermSubst.match_terms [] (build p) (build i)) ^ "]"))

end

module Std = Check (Refiner_std.Refiner)
module Ds = Check (Refiner_ds.Refiner)

let seqs = ref 0 and ctxs = ref 0 and hyps = ref 0 and sovars = ref 0 and conts_lists = ref 0 and binds = ref 0
let rec count = function
  | Var _ -> ()
  | SOVar (_, cs, ts) -> incr sovars; if cs <> [] then incr conts_lists; List.iter count ts
  | Op (_, ts) -> List.iter count ts
  | Bind (_, t) -> incr binds; count t
  | Seq (_, hs, c) ->
      incr seqs;
      List.iter (function
          | Hyp (_, t) -> incr hyps; count t
          | Ctx (_, cs, ts) -> incr ctxs; if cs <> [] then incr conts_lists; List.iter count ts) hs;
      count c

let names2 = [ "subst 'y,'z := 'z,'y at once"; "subst 'z,'z := g{c},'w (the first is used)";
                "match_terms with an instance (no sequent)"; "match_terms with an instance (a sequent)" ]
let names = [ "the term"; "subterm_addresses"; "find_subterm"; "free_vars_set"; "alpha_equal to a renamed copy"; "TermOp.iter_down visits"; "subst of g{'x0; A['x0]} for 'z" ]

let () =
  let n = 2000 in
  let agree = Array.make (List.length names) 0 and first = Array.make (List.length names) None in
  let total2 = Array.make (List.length names2) 0 in
  let agree2 = Array.init (List.length names2) (fun _ -> Array.make 3 0)
  and first2 = Array.init (List.length names2) (fun _ -> Array.make 3 None) in
  for i = 1 to n do
    let d = gen 4 [] 0 in
    count d;
    List.iteri (fun k (s, t) ->
        if s = t then agree.(k) <- agree.(k) + 1
        else if first.(k) = None then first.(k) <- Some (i, s, t))
      (List.combine (Std.checks d) (Ds.checks d));
    let k_of k = if k = 2 && has_seq (yz d) then 3 else k in
    List.iteri (fun k ((s, sm), (t, tm)) ->
        let k = k_of k in
        total2.(k) <- total2.(k) + 1;
        let note i x y = if x = y then agree2.(k).(i) <- agree2.(k).(i) + 1
          else if first2.(k).(i) = None then first2.(k).(i) <- Some (x, y) in
        note 0 s t; note 1 s sm; note 2 t tm)
      (List.combine (Std.more d) (Ds.more d))
  done;
  Printf.printf "%d terms: %d sequents, %d hypotheses, %d context hypotheses, %d second-order variables, %d contexts lists, %d binders\n"
    n !seqs !hyps !ctxs !sovars !conts_lists !binds;
  List.iteri (fun k name ->
      Printf.printf "%-30s %d of %d terms agree\n" name agree.(k) n;
      match first.(k) with
      | None -> ()
      | Some (i, s, t) -> Printf.printf "  first difference, term %d:\n    std %s\n    ds  %s\n" i s t)
    names;
  Printf.printf "On the same terms with every second 'z renamed 'y (std = ds, std = model, ds = model):\n";
  List.iteri (fun k name ->
      let a = agree2.(k) in
      Printf.printf "%-48s of %4d: %4d %4d %4d\n" name total2.(k) a.(0) a.(1) a.(2);
      Array.iteri (fun i f -> match f with
          | None -> ()
          | Some (x, y) ->
              Printf.printf "  first difference, %s:\n    %s\n    %s\n" (List.nth [ "std vs ds"; "std vs model"; "ds vs model" ] i) x y)
        first2.(k))
    names2;
  Printf.printf "match_terms on hand-made cases (std / ds):\n";
  List.iter2 (fun (name, a) (_, b) -> Printf.printf "  %-30s %s / %s\n" name a b) Std.hand Ds.hand
