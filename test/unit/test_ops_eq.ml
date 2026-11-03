(* Term.ops_eq and make_object_id (refiner/term_std, refiner/term_ds), which
   no unit test reached (2026-11-02 profile).  ops_eq says whether two
   operators are the same: the same name and the same parameters -- the
   test for an operator that alpha_equal applies.  In term_std and term_ds:
     - on 3000 pairs of operators, each side built separately from a
       description (names f, g; 0-3 parameters: numbers 0, 3, 120000 and
       300000, strings, tokens,
       variables, meta-numbers, quotes, a nested operator, a parameter
       list), against the model: equal exactly when the descriptions name
       the same values.  A number is built either directly or as a product
       v/3 * 3 (Lm_num keeps a product with an operand of 2^15 or more as a
       big integer, so 40000 * 3 and 120000 are one value in two forms), and
       the model ignores which;
     - ops_eq agrees with alpha_equal of the two operators applied to no
       subterms;
     - make_object_id and dest_object_id give the parameters back.
   The generator is a fixed linear congruential sequence, not Random. *)
let state = ref 2727
let next () = state := (!state * 1103515245 + 12345) land 0x7fffffff; !state lsr 8
let pick n = next () mod n
let pk a = a.(pick (Array.length a))

(* DN (value, as_product) *)
type pd = DN of int * bool | DS of string | DT of string | DV of string | DMN of string | DQ | DOp of od | DPL of pd list
and od = { name : string; params : pd list }

let values = [| 0; 3; 120000; 300000 |]
let rec gpd d =
  match pick (if d = 0 then 6 else 8) with
  | 0 -> DN (pk values, pick 2 = 0) | 1 -> DS (pk [| "a"; "b" |]) | 2 -> DT (pk [| "a"; "b" |])
  | 3 -> DV (pk [| "a"; "b" |]) | 4 -> DMN (pk [| "a"; "b" |]) | 5 -> DQ
  | 6 -> DOp (god (d - 1)) | _ -> DPL (List.init (pick 3) (fun _ -> gpd (d - 1)))
and god d = { name = pk [| "f"; "g" |]; params = List.init (pick 4) (fun _ -> gpd d) }

(* the model's view: a number by its value only *)
let rec norm = function
  | DN (v, _) -> DN (v, false) | DOp o -> DOp (normo o) | DPL l -> DPL (List.map norm l) | p -> p
and normo o = { o with params = List.map norm o.params }
let rec flip = function
  | DN (v, b) -> DN (v, if pick 2 = 0 then not b else b) | DOp o -> DOp (flipo o) | DPL l -> DPL (List.map flip l) | p -> p
and flipo o = { o with params = List.map flip o.params }
let perturb o =
  match o.params with
  | [] -> { o with name = (if o.name = "f" then "g" else "f") }
  | ps -> let i = pick (List.length ps) in { o with params = List.mapi (fun j p -> if j = i then gpd 1 else p) ps }

let has_both o =
  let rec nums = function DN (v, b) -> [ v, b ] | DOp o -> List.concat_map nums o.params | DPL l -> List.concat_map nums l | _ -> [] in
  List.exists (fun (v, b) -> v >= 120000 && b) (List.concat_map nums o.params)

module S (R : Refiner_sig.RefinerSig) = struct
  open R.Term
  let op s = Opname.make_opname [ s ]
  let sym = Lm_symbol.add
  let number v as_product =
    if as_product then Lm_num.mult_num (Lm_num.num_of_int (v / 3)) (Lm_num.num_of_int 3) else Lm_num.num_of_int v
  let rec mk_p = function
    | DN (v, b) -> make_param (Term_sig.Number (number v b)) | DS s -> make_param (Term_sig.String s)
    | DT t -> make_param (Term_sig.Token (op t)) | DV v -> make_param (Term_sig.Var (sym v))
    | DMN v -> make_param (Term_sig.MNumber (sym v)) | DQ -> make_param Term_sig.Quote
    | DOp o -> make_param (Term_sig.Operator { Term_sig.opparam_name = op o.name; opparam_params = List.map mk_p o.params; opparam_arities = [] })
    | DPL l -> make_param (Term_sig.ParamList (List.map mk_p l))
  let mk o = mk_op (op o.name) (List.map mk_p o.params)

  let run name pairs =
    let n = List.length pairs in
    let model = ref 0 and alpha = ref 0 and first = ref "" in
    List.iter (fun (a, b) ->
        let oa = mk a and ob = mk b in
        let m = normo a = normo b in
        let got = ops_eq oa ob in
        if got = m then incr model
        else if !first = "" then first := Printf.sprintf " (first: model %b, a number in two forms %b)" m (has_both a || has_both b);
        if got = R.TermSubst.alpha_equal (mk_term oa []) (mk_term ob []) then incr alpha) pairs;
    Printf.printf "%-44s %4d of %d%s\n" (name ^ ": ops_eq = the model") !model n !first;
    Printf.printf "%-44s %4d of %d\n" (name ^ ": ops_eq agrees with alpha_equal") !alpha n;
    let a = number 120000 true and b = number 120000 false in
    Printf.printf "%-44s eq_num %b, ops_eq %b, alpha_equal %b\n" (name ^ ": f[40000*3] and f[120000]") (Lm_num.eq_num a b)
      (ops_eq (mk_op (op "f") [ make_param (Term_sig.Number a) ]) (mk_op (op "f") [ make_param (Term_sig.Number b) ]))
      (R.TermSubst.alpha_equal (mk_term (mk_op (op "f") [ make_param (Term_sig.Number a) ]) [])
         (mk_term (mk_op (op "f") [ make_param (Term_sig.Number b) ]) []));
    let ps = List.map mk_p [ DN (3, false); DS "a"; DQ ] in
    Printf.printf "%-44s %b\n" (name ^ ": dest_object_id (make_object_id ps) == ps") (dest_object_id (make_object_id ps) == ps)
end

module Std = S (Refiner_std.Refiner)
module Ds = S (Refiner_ds.Refiner)

let () =
  let pairs = List.init 3000 (fun _ ->
      let a = god 2 in
      match pick 3 with 0 -> a, flipo a | 1 -> a, perturb a | _ -> a, god 2) in
  Printf.printf "3000 pairs (%d name the same values; %d of those build a number >= 120000 as a product on one side)\n"
    (List.length (List.filter (fun (a, b) -> normo a = normo b) pairs))
    (List.length (List.filter (fun (a, b) -> normo a = normo b && (has_both a || has_both b)) pairs));
  Std.run "std" pairs;
  Ds.run "ds" pairs
