(* Unify_mm (refiner/reflib) is the first-order unifier JProver and the
   type-inference tactics call.  This test checks it against a textbook
   Robinson unifier (with the occurs check) on pseudo-random problems over
   the variables 'a 'b 'c 'd, the operators f{_; _}, g{_} and c, and a
   binder lam{x._}:
     - unifiable agrees with the model on whether a unifier exists;
     - unify raises exactly when there is none;
     - when unify returns a substitution s, s(t1) and s(t2) are
       alpha-equal (it is a unifier);
     - s(t1) equals the model's mgu applied to t1 up to a renaming of
       the free variables (it is a most general one);
   each first with no constants, then with 'a declared a constant (the
   SymbolSet argument: a variable that may not be bound).
   Unify_mm.unifiable is documented as the faster form of the same test,
   but until it was fixed its shortcut for a problem whose side is a
   variable ('d against f{..'d..}) had no occurs check, so it answered true
   where unify raises Cycle (1968 and 1977 of 2000 agreed).
   A problem is a pair (t1, t2) where t2 is t1 with some subterms
   replaced at random, so that about half are unifiable.  The generator is
   a fixed linear congruential sequence, so the problems are the same on
   every OCaml. *)
open Lm_symbol
open Refiner.Refiner
open Term
open TermType

let state = ref 4242
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

let rec show = function
  | V v -> "'" ^ v | X -> "'x" | C -> "c" | G a -> "g{" ^ show a ^ "}"
  | F (a, b) -> "f{" ^ show a ^ "; " ^ show b ^ "}" | Lam a -> "lam{x." ^ show a ^ "}"

let names = [ "unifiable agrees with the model"; "unify raises exactly when no unifier";
              "unify's substitution unifies"; "most general (model mgu up to renaming)" ]

let run consts =
  let n = 2000 in
  let cs = SymbolSet.of_list (List.map Lm_symbol.add consts) in
  let agree = Array.make 4 0 and tried = Array.make 4 0 and first = Array.make 4 None in
  let unif = ref 0 in
  let note k ok what = tried.(k) <- tried.(k) + 1; if ok then agree.(k) <- agree.(k) + 1 else if first.(k) = None then first.(k) <- Some what in
  for _ = 1 to n do
    let a = gen 4 false in
    let b = mutate false a in
    let t1 = build a and t2 = build b in
    let what = show a ^ "  =  " ^ show b in
    let m = mgu consts a b in
    if m <> None then incr unif;
    let u = try Some (Unify_mm.unify t1 t2 cs) with _ -> None in
    note 0 ((try Unify_mm.unifiable t1 t2 cs with _ -> false) = (m <> None)) what;
    note 1 ((u <> None) = (m <> None)) what;
    (match u with
     | None -> ()
     | Some s ->
         let s1 = TermSubst.apply_subst s t1 and s2 = TermSubst.apply_subst s t2 in
         note 2 (TermSubst.alpha_equal s1 s2) what;
         (match m with
          | Some ms -> note 3 (rename_equal s1 (build (resolve ms a))) what
          | None -> ()))
  done;
  Printf.printf "constants {%s}: %d problems, %d unifiable by the model\n" (String.concat "," consts) n !unif;
  List.iteri (fun k name ->
      Printf.printf "  %-42s %d of %d\n" name agree.(k) tried.(k);
      match first.(k) with None -> () | Some w -> Printf.printf "    first difference: %s\n" w)
    names

let () = run []; run [ "a" ]
