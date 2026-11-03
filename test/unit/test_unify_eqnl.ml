(* Unify_mm's equation lists (refiner/reflib/unify_mm), which no unit test
   reached (2026-11-02 census): eqnlist_empty, eqnlist_append_eqn,
   eqnlist_append_var_eqn, eqnlist_append_eqns, eqnlist2ttlist,
   new_eqns_var, unifiable_eqnl, unify_eqnl, unify_eqnl_eqnl.  Against the
   same textbook Robinson unifier test_unify_mm uses, on 1500 systems of
   1-3 equations (a term and a random mutation of it, over 'a 'b 'c 'd,
   f{_; _}, g{_}, c and lam{x._}), first with no constants, then with 'a
   a constant:
     - the builders give the list a list model gives (append_eqn and
       append_var_eqn put the new equation first, append_eqns puts its list
       in front);
     - unifiable_eqnl agrees with the model, and unify_eqnl raises exactly
       when the model finds no unifier;
     - unify_eqnl's substitution unifies every equation, and is most
       general (each side equals the model's mgu applied to it, up to a
       renaming of the free variables, all equations at once);
     - unify_eqnl_eqnl's solved form has a variable on every left side, and
       used as a substitution (applied until nothing changes) it unifies
       every equation;
     - new_eqns_var gives a variable free in no equation, and the variable
       itself when it already is.
   The generator is a fixed linear congruential sequence. *)
open Lm_symbol
open Refiner.Refiner
open Term
open TermType

let state = ref 5353
let next () = state := (!state * 1103515245 + 12345) land 0x7fffffff; !state lsr 8
let pick n = next () mod n

type d = V of string | F of d * d | G of d | C | Lam of d   (* Lam binds x *)
                | X                                         (* the bound x *)

let vars = [| "a"; "b"; "c"; "d" |]
let rec gen depth inlam =
  if depth = 0 || pick 4 = 0 then
    (match pick 4 with 0 -> C | 1 when inlam -> X | _ -> V vars.(pick 4))
  else
    match pick 4 with
    | 0 -> G (gen (depth - 1) inlam)
    | 1 when not inlam -> Lam (gen (depth - 1) true)
    | _ -> F (gen (depth - 1) inlam, gen (depth - 1) inlam)

let rec mutate inlam d =
  if pick 5 = 0 then gen 2 inlam
  else
    match d with
    | F (a, b) -> F (mutate inlam a, mutate inlam b)
    | G a -> G (mutate inlam a)
    | Lam a -> Lam (mutate true a)
    | d -> d

(* The model: Robinson unification on d, with the occurs check.  Variables
   in consts may not be bound.  A variable may not be bound to a term
   that mentions the bound x (it would escape its binder). *)
exception No
let rec walk s = function V v when List.mem_assoc v s -> walk s (List.assoc v s) | d -> d
let rec resolve s d =
  match walk s d with
  | F (a, b) -> F (resolve s a, resolve s b)
  | G a -> G (resolve s a)
  | Lam a -> Lam (resolve s a)
  | d -> d
let rec occurs v = function V w -> v = w | F (a, b) -> occurs v a || occurs v b | G a | Lam a -> occurs v a | _ -> false
let rec has_x = function X -> true | F (a, b) -> has_x a || has_x b | G a -> has_x a | _ -> false
let rec unify consts s a b =
  match walk s a, walk s b with
  | V v, V w when v = w -> s
  | V v, t when not (List.mem v consts) -> bind consts s v t
  | t, V v when not (List.mem v consts) -> bind consts s v t
  | F (a1, b1), F (a2, b2) -> unify consts (unify consts s a1 a2) b1 b2
  | G a, G b -> unify consts s a b
  | Lam a, Lam b -> unify consts s a b
  | C, C | X, X -> s
  | _ -> raise No
and bind _ s v t =
  let t' = resolve s t in
  if occurs v t' || has_x t' then raise No else (v, t) :: s

let mgu consts a b = try Some (unify consts [] a b) with No -> None

(* Build a d as a MetaPRL term. *)
let op s = Opname.make_opname [ s ]
let x = Lm_symbol.add "x"
let rec build = function
  | V v -> mk_var_term (Lm_symbol.add v)
  | X -> mk_var_term x
  | C -> mk_simple_term (op "c") []
  | G a -> mk_simple_term (op "g") [ build a ]
  | F (a, b) -> mk_simple_term (op "f") [ build a; build b ]
  | Lam a -> mk_term (mk_op (op "lam") []) [ mk_bterm [ x ] (build a) ]

(* Equal up to a bijective renaming of the free variables (bound ones are
   paired by position). *)
let rename_equal t1 t2 =
  let fwd = Hashtbl.create 8 and bwd = Hashtbl.create 8 in
  let rec go bound t1 t2 =
    if is_var_term t1 && is_var_term t2 then
      let v1 = dest_var t1 and v2 = dest_var t2 in
      match List.assoc_opt v1 bound with
      | Some w -> Lm_symbol.eq w v2
      | None ->
          not (List.exists (fun (_, w) -> Lm_symbol.eq w v2) bound)
          && (match Hashtbl.find_opt fwd v1, Hashtbl.find_opt bwd v2 with
              | None, None -> Hashtbl.add fwd v1 v2; Hashtbl.add bwd v2 v1; true
              | Some w2, Some w1 -> Lm_symbol.eq w2 v2 && Lm_symbol.eq w1 v1
              | _ -> false)
    else if is_var_term t1 || is_var_term t2 then false
    else
      let d1 = dest_term t1 and d2 = dest_term t2 in
      Opname.eq (dest_op d1.term_op).op_name (dest_op d2.term_op).op_name
      && List.length d1.term_terms = List.length d2.term_terms
      && List.for_all2 (fun b1 b2 ->
          let b1 = dest_bterm b1 and b2 = dest_bterm b2 in
          List.length b1.bvars = List.length b2.bvars
          && go (List.combine b1.bvars b2.bvars @ bound) b1.bterm b2.bterm)
        d1.term_terms d2.term_terms
  in
  go [] t1 t2

let lop = Opname.make_opname [ "L" ]
let tuple ts = mk_simple_term lop ts
(* apply a substitution given as equations var = term until nothing changes *)
let rec fix sub t n =
  let t' = TermSubst.apply_subst sub t in
  if n = 0 || TermSubst.alpha_equal t t' then t' else fix sub t' (n - 1)

let run consts =
  let n = 1500 in
  let cs = SymbolSet.of_list (List.map Lm_symbol.add consts) in
  let c = Array.make 8 0 and tried = Array.make 8 0 in
  let note k ok = tried.(k) <- tried.(k) + 1; if ok then c.(k) <- c.(k) + 1 in
  let unif = ref 0 in
  for _ = 1 to n do
    let ds = List.init (1 + pick 3) (fun _ -> let a = gen 3 false in a, mutate false a) in
    let eqs = List.map (fun (a, b) -> build a, build b) ds in
    (* the builders, against a list model *)
    let (t1, t2) = List.hd eqs in
    let l = Unify_mm.eqnlist_append_eqn Unify_mm.eqnlist_empty t1 t2 in
    let l = Unify_mm.eqnlist_append_var_eqn (Lm_symbol.add "e") t2 l in
    let l = Unify_mm.eqnlist_append_eqns l (List.tl eqs) in
    let model = List.tl eqs @ [ mk_var_term (Lm_symbol.add "e"), t2; t1, t2 ] in
    let got = Unify_mm.eqnlist2ttlist l in
    note 0 (List.length got = List.length model
            && List.for_all2 (fun (a, b) (a', b') -> TermSubst.alpha_equal a a' && TermSubst.alpha_equal b b') got model);
    let el = Unify_mm.eqnlist_append_eqns Unify_mm.eqnlist_empty eqs in
    (* the model: one unifier for all equations *)
    let m = try Some (List.fold_left (fun s (a, b) -> unify consts s a b) [] ds) with No -> None in
    if m <> None then incr unif;
    note 1 ((try Unify_mm.unifiable_eqnl el cs with _ -> false) = (m <> None));
    let u = try Some (Unify_mm.unify_eqnl el cs) with _ -> None in
    note 2 ((u <> None) = (m <> None));
    (match u, m with
     | Some s, Some ms ->
         note 3 (List.for_all (fun (a, b) -> TermSubst.alpha_equal (TermSubst.apply_subst s a) (TermSubst.apply_subst s b)) eqs);
         note 4 (rename_equal (tuple (List.map (fun (a, _) -> TermSubst.apply_subst s a) eqs))
                   (tuple (List.map (fun (a, _) -> build (resolve ms a)) ds)))
     | _ -> ());
    (match (try Some (Unify_mm.unify_eqnl_eqnl el cs) with _ -> None), m with
     | Some sol, Some _ ->
         let sl = Unify_mm.eqnlist2ttlist sol in
         let vars_ok = List.for_all (fun (a, _) -> is_var_term a) sl in
         let sub = List.filter_map (fun (a, b) -> if is_var_term a then Some (dest_var a, b) else None) sl in
         note 5 (vars_ok && List.for_all (fun (a, b) -> TermSubst.alpha_equal (fix sub a 20) (fix sub b 20)) eqs)
     | None, None -> note 5 true
     | _ -> note 5 false);
    (* new_eqns_var *)
    let fv = List.fold_left (fun s (a, b) -> SymbolSet.union s (SymbolSet.union (TermSubst.free_vars_set a) (TermSubst.free_vars_set b))) SymbolSet.empty eqs in
    let va = Unify_mm.new_eqns_var el (Lm_symbol.add "a") and vq = Unify_mm.new_eqns_var el (Lm_symbol.add "q") in
    note 6 (not (SymbolSet.mem fv va) && Lm_symbol.eq vq (Lm_symbol.add "q"))
  done;
  Printf.printf "constants {%s}: %d systems, %d unifiable by the model\n" (String.concat "," consts) n !unif;
  List.iteri (fun k name -> Printf.printf "  %-46s %d of %d\n" name c.(k) tried.(k))
    [ "the builders = the list model"; "unifiable_eqnl agrees with the model"; "unify_eqnl raises exactly when no unifier";
      "unify_eqnl's substitution unifies every equation"; "most general (model mgu up to renaming)";
      "unify_eqnl_eqnl: variables on the left, unifies"; "new_eqns_var fresh, or the variable itself" ]

let () = run []; run [ "a" ]
