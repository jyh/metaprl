(* The rewriter's separate redex interface (refiner/rewrite): compile_redex,
   compile_redices, extract_redex_types, test_redex_applicability and
   apply_redex.  The filter's generated code and Term_match_table.lookup_rwi
   (every display form) use them; test_rewrite_differential reaches only
   term_rewrite and apply_rewrite.  On random patterns over f{_;_}, g{_},
   c, h[@n:n]{_} with variables 'a 'b and the number variable n, each
   applied to random closed terms, against first-order matching as the
   model, in term_std and in term_ds:
     - extract_redex_types lists each variable once, in the order it
       first occurs (left to right), 'a/'b as terms and n as a number;
     - apply_redex raises exactly when the model does not match, and
       otherwise returns, in that order, the subterm or number bound to
       each variable;
     - test_redex_applicability raises exactly when apply_redex does;
     - compile_redices [p; q] matched against t with [u] binds the
       variables of both, a variable shared by p and q to equal values,
       and lists q's variables before p's (the argument redices are
       compiled before the goal);
   and, through the default refiner, Term_match_table.lookup_rwi returns
   apply_redex's items for the pattern lookup chooses.  It prints each
   count with how many cases it was tried on, and the first difference.
   The generator is a fixed linear congruential sequence, not Random. *)

let state = ref 77
let next () = state := (!state * 1103515245 + 12345) land 0x7fffffff; !state lsr 8
let pick n = next () mod n

(* Patterns and closed terms.  N is a number variable, K a number. *)
type num = N | K of int
type p = PV of string | F of p * p | G of p | C | H of num * p

let rec show = function
  | PV v -> "'" ^ v | C -> "c" | G a -> "g{" ^ show a ^ "}"
  | F (a, b) -> "f{" ^ show a ^ "; " ^ show b ^ "}"
  | H (N, a) -> "h[n:n]{" ^ show a ^ "}" | H (K k, a) -> Printf.sprintf "h[%d:n]{%s}" k (show a)

let rec gpat d =
  if d = 0 || pick 3 = 0 then (if pick 3 > 0 then PV [| "a"; "b" |].(pick 2) else C)
  else match pick 5 with
    | 0 | 1 -> F (gpat (d - 1), gpat (d - 1))
    | 2 -> G (gpat (d - 1))
    | 3 -> H ((if pick 2 = 0 then N else K (pick 3)), gpat (d - 1))
    | _ -> C
let rec gterm d =
  if d = 0 || pick 3 = 0 then C
  else match pick 4 with
    | 0 | 1 -> F (gterm (d - 1), gterm (d - 1))
    | 2 -> G (gterm (d - 1))
    | _ -> H (K (pick 3), gterm (d - 1))

(* The value bound to a variable: a closed term, or a number. *)
type value = T of p | I of int

(* First-order matching; every variable is bound once. *)
let rec m s p t =
  let bind v x = match List.assoc_opt v s with None -> Some ((v, x) :: s) | Some y -> if x = y then Some s else None in
  match p, t with
  | PV v, _ -> bind v (T t)
  | C, C -> Some s
  | G a, G b -> m s a b
  | F (a1, a2), F (b1, b2) -> (match m s a1 b1 with None -> None | Some s -> m s a2 b2)
  | H (N, a), H (K k, b) -> (match bind "n" (I k) with None -> None | Some s -> m s a b)
  | H (K j, a), H (K k, b) when j = k -> m s a b
  | _ -> None

(* The variables of a pattern list, in the order they first occur. *)
let vars ps =
  let rec go acc = function
    | PV v -> if List.mem v acc then acc else acc @ [ v ]
    | C -> acc
    | G a -> go acc a
    | F (a, b) -> go (go acc a) b
    | H (N, a) -> go (if List.mem "n" acc then acc else acc @ [ "n" ]) a
    | H (K _, a) -> go acc a
  in
  List.fold_left go [] ps

let tried = Array.make 5 0 and ok = Array.make 5 0 and first = Array.make 5 None
let note k b what = tried.(k) <- tried.(k) + 1; if b then ok.(k) <- ok.(k) + 1 else if first.(k) = None then first.(k) <- Some what

module Check (R : Refiner_sig.RefinerSig) = struct
  open R.Term
  open R.TermMan
  open R.TermSubst
  let op s = Opname.make_opname [ s ]
  let rec build = function
    | PV v -> mk_so_var_term (Lm_symbol.add v) [] []
    | C -> mk_simple_term (op "c") []
    | G a -> mk_simple_term (op "g") [ build a ]
    | F (a, b) -> mk_simple_term (op "f") [ build a; build b ]
    | H (n, a) ->
        let prm = match n with N -> Term_sig.MNumber (Lm_symbol.add "n") | K k -> Term_sig.Number (Lm_num.num_of_int k) in
        mk_term (mk_op (op "h") [ make_param prm ]) [ mk_simple_bterm (build a) ]

  let compile ps = R.Rewrite.compile_redices Rewrite_sig.Relaxed R.Rewrite.empty_args_spec (List.map build ps)

  (* The model's items, in the order of vs. *)
  let same_item v item =
    match v, item with
    | T t, Rewrite_sig.RewriteTerm u -> alpha_equal (build t) u
    | I k, Rewrite_sig.RewriteNum (Rewrite_sig.RewriteParam n) -> Lm_num.eq_num n (Lm_num.num_of_int k)
    | _ -> false
  let same_items s vs items =
    List.length vs = List.length items && List.for_all2 (fun v it -> same_item (List.assoc v s) it) vs items

  let types_ok vs redex =
    let want = List.map (fun v -> (if v = "n" then Rewrite_sig.RewriteNumType else Rewrite_sig.RewriteTermType), v) vs in
    List.map (fun (ty, v) -> ty, Lm_symbol.to_string v) (R.Rewrite.extract_redex_types redex) = want

  let run name =
    let n = 500 in
    let matched = ref 0 and matched2 = ref 0 in
    for _ = 1 to n do
      let p = gpat 3 in
      let t = if pick 2 = 0 then gterm 3 else (* an instance: fill p's variables *)
          let k = pick 3 and a = gterm 2 and b = gterm 2 in
          let rec inst = function
            | PV "a" -> a | PV _ -> b | C -> C | G x -> G (inst x) | F (x, y) -> F (inst x, inst y)
            | H (N, x) -> H (K k, inst x) | H (K j, x) -> H (K j, inst x) in
          inst p in
      let what = Printf.sprintf "%s: pattern %s, term %s" name (show p) (show t) in
      let vs = vars [ p ] in
      let redex = R.Rewrite.compile_redex Rewrite_sig.Relaxed R.Rewrite.empty_args_spec (build p) in
      note 0 (types_ok vs redex) what;
      let got = try Some (R.Rewrite.apply_redex redex R.Rewrite.empty_rw_args (build t) []) with _ -> None in
      (match m [] p t, got with
       | None, None -> note 1 true what
       | Some s, Some items -> incr matched; note 1 (same_items s vs items) what
       | _ -> note 1 false what);
      let applies = try R.Rewrite.test_redex_applicability redex R.Rewrite.empty_rw_args (build t) []; true with _ -> false in
      note 2 (applies = (got <> None)) what;
      (* two redices sharing their variables *)
      let q = gpat 2 and u = if pick 2 = 0 then t else gterm 3 in
      let what2 = Printf.sprintf "%s: redices [%s; %s], terms %s, [%s]" name (show p) (show q) (show t) (show u) in
      (* compile_so_redex compiles the argument redices before the goal
         (rewrite_compile_redex.ml:635-637), so their variables come first. *)
      let vs2 = vars [ q; p ] in
      let redex2 = compile [ p; q ] in
      note 0 (types_ok vs2 redex2) what2;
      let got2 = try Some (R.Rewrite.apply_redex redex2 R.Rewrite.empty_rw_args (build t) [ build u ]) with _ -> None in
      (match (match m [] p t with None -> None | Some s -> m s q u), got2 with
       | None, None -> note 3 true what2
       | Some s, Some items -> incr matched2; note 3 (same_items s vs2 items) what2
       | _ -> note 3 false what2)
    done;
    Printf.printf "%s: %d patterns (%d matched), %d pairs of redices (%d matched)\n" name n !matched n !matched2
end

module Std = Check (Refiner_std.Refiner)
module Ds = Check (Refiner_ds.Refiner)
module Def = Check (Refiner.Refiner)

(* lookup_rwi: the items are apply_redex's for the chosen pattern. *)
let check_lookup_rwi () =
  let n = 300 in
  let found = ref 0 in
  for _ = 1 to n do
    let pats = List.init (1 + pick 4) (fun _ -> gpat 3) in
    let indexed = List.mapi (fun k p -> k, p) pats in
    let tbl = List.fold_left (fun tb (k, p) -> Term_match_table.add_item tb (Def.build p) k) Term_match_table.empty_table indexed in
    let t = gterm 3 in
    let what = Printf.sprintf "lookup_rwi: patterns [%s], term %s" (String.concat "; " (List.map show pats)) (show t) in
    let want = List.filter (fun (_, p) -> m [] p t <> None) indexed in
    match (try Ok (Term_match_table.lookup_rwi tbl Term_match_table.select_all (Def.build t)) with e -> Error e) with
    | Ok None -> note 4 (want = []) what
    | Ok (Some (items, k)) ->
        incr found;
        (match List.assoc_opt k indexed with
         | None -> note 4 false what
         | Some p ->
             (match m [] p t with
              | None -> note 4 false what
              | Some s -> note 4 (Def.same_items s (vars [ p ]) items) what))
    | Error _ -> note 4 false what
  done;
  Printf.printf "lookup_rwi: %d tables (%d found a pattern)\n" n !found

let () =
  Std.run "term_std";
  Ds.run "term_ds";
  check_lookup_rwi ();
  List.iteri (fun k name ->
      Printf.printf "%-48s %4d of %4d\n" name ok.(k) tried.(k);
      match first.(k) with None -> () | Some w -> Printf.printf "  first difference: %s\n" w)
    [ "extract_redex_types: first-occurrence order"; "apply_redex = the model's bindings, or raises";
      "test_redex_applicability raises iff apply_redex"; "compile_redices: two redices, shared variables";
      "lookup_rwi = apply_redex of the chosen pattern" ]
