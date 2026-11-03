(* TermSubst.opparam_eq and Term_ty (refiner/term_gen/term_ty_gen), which no
   unit test reached (2026-11-02 profile).  In term_std and term_ds:
     - opparam_eq on 4000 pairs of operator parameters, each side BUILT
       SEPARATELY from a description (operators f, g; 0-3 parameters of
       every kind -- number, string, token, variable, the meta kinds,
       quote, level, shape, and a nested operator, object id or parameter
       list -- and 0-2 arities), against the model: equal exactly when the
       two descriptions are equal.  A third of the pairs share a
       description and a third change exactly one parameter (at any depth),
       so both answers are exercised near the boundary;
     - Term_ty: eq_ty compares operator name, parameters (a token by
       alpha_equal of its term), bound terms and type, and ignores the
       term; eq is alpha_equal of the terms and eq_ty.  On 4000 pairs of
       type descriptions (a quarter differ only in the term, a quarter in
       one parameter or the type), against that model;
     - term_of_ty gives back its term itself, and string_of_ty_param
       prints each of the eight kinds.
   The generator is a fixed linear congruential sequence, not Random. *)
open Term_sig
open Term_ty_sig

let state = ref 7171
let next () = state := (!state * 1103515245 + 12345) land 0x7fffffff; !state lsr 8
let pick n = next () mod n
let pk a = a.(pick (Array.length a))

(* a parameter's description; level variables are kept sorted and distinct *)
type pd =
  | DN of int | DS of string | DT of string | DV of string | DMN of string | DMS of string
  | DMT of string | DMSh of string | DMOp of string | DQ | DL of int * (string * int) list
  | DSh of string * int list * int list | DOp of opd | DOb of pd list | DPL of pd list
and opd = { o_name : string; o_params : pd list; o_ar : int list }

let names = [| "a"; "b" |]
let rec gpd depth =
  match pick (if depth = 0 then 12 else 15) with
  | 0 -> DN (pick 3) | 1 -> DS (pk names) | 2 -> DT (pk names) | 3 -> DV (pk names)
  | 4 -> DMN (pk names) | 5 -> DMS (pk names) | 6 -> DMT (pk names) | 7 -> DMSh (pk names)
  | 8 -> DMOp (pk names) | 9 -> DQ
  | 10 -> DL (pick 2, List.filter (fun _ -> pick 2 = 0) [ "k", 0; "m", 1 ])
  | 11 -> DSh (pk [| "f"; "g" |], List.init (pick 3) (fun _ -> pick 3), List.init (pick 3) (fun _ -> pick 2))
  | 12 -> DOp (gop (depth - 1))
  | 13 -> DOb (List.init (pick 3) (fun _ -> gpd (depth - 1)))
  | _ -> DPL (List.init (pick 3) (fun _ -> gpd (depth - 1)))
and gop depth = { o_name = pk [| "f"; "g" |]; o_params = List.init (pick 4) (fun _ -> gpd depth); o_ar = List.init (pick 3) (fun _ -> pick 2) }

(* a type's description: params (0 number .. 6 quote, or a token), bound terms, type, term *)
type tyd = { t_name : string; t_params : int list; t_bterms : (string list * string) list; t_type : string; t_term : string }
let gty () =
  { t_name = pk [| "f"; "g" |];
    t_params = List.init (pick 3) (fun _ -> pick 9);
    t_bterms = List.init (pick 3) (fun _ -> List.init (pick 2) (fun _ -> pk [| "x"; "y" |]), pk [| "c"; "d" |]);
    t_type = pk [| "c"; "d" |]; t_term = pk [| "c"; "d" |] }

(* change one parameter, at any depth (the result may happen to equal the original) *)
let rec perturb o =
  match o.o_params with
  | [] -> { o with o_ar = List.init (pick 3) (fun _ -> pick 2) }
  | ps ->
      let i = pick (List.length ps) in
      let ch = function
        | DOp o' when pick 3 > 0 -> DOp (perturb o')
        | (DOb (_ :: _ as l) | DPL (_ :: _ as l)) as d when pick 3 > 0 ->
            let l' = (perturb { o_name = "f"; o_params = l; o_ar = [] }).o_params in
            (match d with DOb _ -> DOb l' | _ -> DPL l')
        | _ -> gpd 1 in
      { o with o_params = List.mapi (fun j p -> if j = i then ch p else p) ps }
let op_pairs n = List.init n (fun _ -> let a = gop 2 in match pick 3 with 0 -> a, a | 1 -> a, perturb a | _ -> a, gop 2)
let ty_perturb a =
  match a.t_params with
  | [] -> { a with t_type = (if a.t_type = "c" then "d" else "c") }
  | ps -> let i = pick (List.length ps) in { a with t_params = List.mapi (fun j k -> if j = i then pick 9 else k) ps }

module S (R : Refiner_sig.RefinerSig) = struct
  open R.Term
  open R.TermMan
  let op s = Opname.make_opname [ s ]
  let sym = Lm_symbol.add
  let shape_kinds = [| ShapeNumber; ShapeString; ShapeToken |]
  let rec mk_p d =
    make_param (match d with
      | DN i -> Number (Lm_num.num_of_int i) | DS s -> String s | DT t -> Token (op t) | DV v -> Var (sym v)
      | DMN v -> MNumber (sym v) | DMS v -> MString (sym v) | DMT v -> MToken (sym v) | DMSh v -> MShape (sym v)
      | DMOp v -> MOperator (sym v) | DQ -> Quote
      | DL (c, vs) -> MLevel (mk_level c (List.map (fun (v, o) -> mk_level_var (sym v) o) vs))
      | DSh (o, ks, ar) -> Shape { shape_opname = op o; shape_params = List.map (fun k -> shape_kinds.(k)) ks; shape_arities = ar }
      | DOp o -> Operator (mk_opp o)
      | DOb l -> ObId (List.map mk_p l) | DPL l -> ParamList (List.map mk_p l))
  and mk_opp o = { opparam_name = op o.o_name; opparam_params = List.map mk_p o.o_params; opparam_arities = o.o_ar }

  let simple s = mk_simple_term (op s) []
  let tys = [| TyNumber; TyString; TyShape; TyOperator; TyLevel; TyVar; TyQuote |]
  let mk_ty d =
    { ty_term = simple d.t_term; ty_opname = op d.t_name;
      ty_params = List.map (fun k -> if k < 7 then tys.(k) else TyToken (simple (if k = 7 then "ta" else "tb"))) d.t_params;
      ty_bterms = List.map (fun (vs, t) -> { ty_bvars = List.map (fun v -> mk_var_term (sym v)) vs; ty_bterm = simple t }) d.t_bterms;
      ty_type = simple d.t_type }

  let opparam_eq = R.TermSubst.opparam_eq
  let ty_eq = R.TermTy.eq
  let ty_eq_ty = R.TermTy.eq_ty
  let run name ops tys_ =
    let n_op = List.length ops and n_ty = List.length tys_ in
    let k = ref 0 and first = ref "" and nexn = ref 0 in
    List.iter (fun (a, b) ->
        let got = (try opparam_eq (mk_opp a) (mk_opp b) with _ -> incr nexn; not (a = b)) in
        if got = (a = b) then incr k else if !first = "" then first := Printf.sprintf " (first: same description %b)" (a = b)) ops;
    Printf.printf "%-46s %4d of %d%s\n" (name ^ ": opparam_eq = the model") !k n_op !first;
    Printf.printf "%-46s %4d\n" (name ^ ": opparam_eq raised") !nexn;
    let k1 = ref 0 and k2 = ref 0 in
    List.iter (fun (a, b) ->
        let ta = mk_ty a and tb = mk_ty b in
        let m_ty = { a with t_term = "" } = { b with t_term = "" } in
        if (try ty_eq_ty ta tb with _ -> not m_ty) = m_ty then incr k1;
        if (try ty_eq ta tb with _ -> not (a = b)) = (a = b) then incr k2) tys_;
    Printf.printf "%-46s %4d of %d\n" (name ^ ": eq_ty = the model (term ignored)") !k1 n_ty;
    Printf.printf "%-46s %4d of %d\n" (name ^ ": eq = the model") !k2 n_ty;
    let t = mk_ty (List.hd tys_ |> fst) in
    Printf.printf "%-46s %b\n" (name ^ ": term_of_ty gives its term (==)") (R.TermTy.term_of_ty t == t.ty_term);
    Printf.printf "%s: %s\n" name
      (String.concat " " (List.map R.TermTy.string_of_ty_param (Array.to_list tys @ [ TyToken (simple "ta") ])))
end

module Std = S (Refiner_std.Refiner)
module Ds = S (Refiner_ds.Refiner)

let () =
  let ops = op_pairs 4000 in
  (* a quarter of the type pairs differ only in the term, which eq_ty ignores and eq does not;
     a quarter change one parameter (or the type) *)
  let tys_ = List.init 4000 (fun _ -> let a = gty () in
                              match pick 4 with 0 -> a, a
                                              | 1 -> a, { a with t_term = (if a.t_term = "c" then "d" else "c") }
                                              | 2 -> a, ty_perturb a
                                              | _ -> a, gty ()) in
  let same l = List.length (List.filter (fun (a, b) -> a = b) l) in
  let has_nest = function DOp _ | DOb _ | DPL _ -> true | _ -> false in
  Printf.printf "%d operator pairs (%d share a description; %d with a nested operator, object id or list)\n"
    (List.length ops) (same ops) (List.length (List.filter (fun (a, _) -> List.exists has_nest a.o_params) ops));
  Printf.printf "%d type pairs (%d share a description; %d differ only in the term)\n" (List.length tys_) (same tys_)
    (List.length (List.filter (fun (a, b) -> a <> b && { a with t_term = "" } = { b with t_term = "" }) tys_));
  Std.run "std" ops tys_;
  Ds.run "ds" ops tys_
