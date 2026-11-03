(* Meta terms, the statements of rules (refiner/term_gen/term_meta_gen),
   which no unit test reached (2026-11-02 profile).  On 400 generated meta
   terms (implications, functions, iffs, labels over small terms with
   binders), in term_std and term_ds:
     - unzip_mimplies (zip_mimplies hs c) gives back hs and c;
     - unzip_mfunction (zip_mfunction vs c) gives back the variables (or
       none), their types and c;
     - meta_alpha_equal holds between a meta term and its copy with every
       bound variable renamed, and not between two meta terms whose parts
       differ;
     - meta_term_of_term (term_of_meta_term m) is m (meta_alpha_equal);
     - free_vars_mterm is the union of its parts' free variables and the
       variables of its meta-functions (a rule's arguments count as free,
       term_meta_gen.ml's MetaFunction case);
     - decode_free_var (encode_free_var v) is v, and the encoding is an
       encoded free variable while an ordinary variable is not.
   And, by hand, what meta_alpha_equal does with labels and a
   meta-function's variable.  Terms are compared with alpha_equal.  The generator is a fixed linear
   congruential sequence, not Random. *)
open Term_sig

let state = ref 6060
let next () = state := (!state * 1103515245 + 12345) land 0x7fffffff; !state lsr 8
let pick n = next () mod n

type d = Var of string | Op of string * d list | Bind of string * d
let rec gen env depth =
  match pick (if depth = 0 then 2 else 4) with
  | 0 -> if env = [] || pick 2 = 0 then Var [| "z"; "w" |].(pick 2) else Var (List.nth env (pick (List.length env)))
  | 1 -> Op ("c", [])
  | 2 -> Op ([| "f"; "g" |].(pick 2), List.init (1 + pick 2) (fun _ -> gen env (depth - 1)))
  | _ -> let x = Printf.sprintf "x%d" depth in Bind (x, gen (x :: env) (depth - 1))
let rec rename = function
  | Var v -> Var v | Op (o, ts) -> Op (o, List.map rename ts)
  | Bind (x, t) -> let x' = x ^ "r" in Bind (x', rename (subst x x' t))
and subst x y = function
  | Var v -> Var (if v = x then y else v) | Op (o, ts) -> Op (o, List.map (subst x y) ts)
  | Bind (z, t) -> if z = x then Bind (z, t) else Bind (z, subst x y t)
let rec free env = function
  | Var v -> if List.mem v env then [] else [ v ] | Op (_, ts) -> List.concat_map (free env) ts
  | Bind (x, t) -> free (x :: env) t

type m = Th of d | Imp of m * m | Fun of string * d * m | Iff of m * m | Lab of string * m
let rec gm depth =
  match pick (if depth = 0 then 1 else 5) with
  | 0 -> Th (gen [] 2)
  | 1 -> Imp (gm (depth - 1), gm (depth - 1))
  | 2 -> Fun ([| "a"; "b" |].(pick 2), gen [] 1, gm (depth - 1))
  | 3 -> Iff (gm (depth - 1), gm (depth - 1))
  | _ -> Lab ([| "wf"; "main" |].(pick 2), gm (depth - 1))
let rec mrename = function
  | Th t -> Th (rename t) | Imp (a, b) -> Imp (mrename a, mrename b)
  | Fun (v, t, m) -> Fun (v, rename t, mrename m) | Iff (a, b) -> Iff (mrename a, mrename b) | Lab (l, m) -> Lab (l, mrename m)
let rec parts = function
  | Th t -> [ t ] | Imp (a, b) | Iff (a, b) -> parts a @ parts b | Fun (_, t, m) -> t :: parts m | Lab (_, m) -> parts m

module M (R : Refiner_sig.RefinerSig) = struct
  open R.Term
  open R.TermMan
  open R.TermSubst
  module Me = R.TermMeta
  let op s = Opname.make_opname [ s ]
  let rec build = function
    | Var v -> mk_var_term (Lm_symbol.add v)
    | Op (o, ts) -> mk_simple_term (op o) (List.map build ts)
    | Bind (x, t) -> mk_term (mk_op (op "lam") []) [ mk_bterm [ Lm_symbol.add x ] (build t) ]
  let rec mbuild = function
    | Th t -> MetaTheorem (build t)
    | Imp (a, b) -> MetaImplies (mbuild a, mbuild b)
    | Fun (v, t, m) -> MetaFunction (mk_var_term (Lm_symbol.add v), MetaTheorem (build t), mbuild m)
    | Iff (a, b) -> MetaIff (mbuild a, mbuild b)
    | Lab (l, m) -> MetaLabeled (l, mbuild m)
  let ok f = try f () with _ -> false
  let checks (hs, c) (fs, fc) mt other =
    let hs' = List.map build hs and c' = build c in
    let zip = ok (fun () -> let hs2, c2 = Me.unzip_mimplies (Me.zip_mimplies hs' c') in
                   List.length hs2 = List.length hs' && List.for_all2 alpha_equal hs2 hs' && alpha_equal c2 c') in
    let fn = ok (fun () ->
        let vs = List.map (fun (v, t) -> Option.map (fun v -> mk_var_term (Lm_symbol.add v)) v, build t) fs in
        let l, c2 = Me.unzip_mfunction (Me.zip_mfunction vs (build fc)) in
        List.length l = List.length vs && alpha_equal c2 (build fc)
        && List.for_all2 (fun (_, v2, t2) (v, t) ->
            alpha_equal t2 t && (match v, v2 with None, None -> true | Some a, Some b -> alpha_equal a b | _ -> false)) l vs) in
    let m = mbuild mt in
    let alpha = ok (fun () -> Me.meta_alpha_equal m (mbuild (mrename mt))) in
    let differ = ok (fun () -> Me.meta_alpha_equal m (mbuild other) = (mt = other)) in
    let back = ok (fun () -> Me.meta_alpha_equal (Me.meta_term_of_term (Me.term_of_meta_term m)) m) in
    let fv = ok (fun () ->
        let want = List.sort_uniq compare (List.concat_map (free []) (parts mt)) in
        let got = List.sort compare (List.map Lm_symbol.string_of_symbol (Lm_symbol.SymbolSet.elements (Me.free_vars_mterm m))) in
        (* a meta-function's variable (the rule's argument) is counted free *)
        let rec fun_vars = function Fun (v, _, m) -> v :: fun_vars m | Imp (a, b) | Iff (a, b) -> fun_vars a @ fun_vars b | Lab (_, m) -> fun_vars m | Th _ -> [] in
        got = List.sort_uniq compare (want @ fun_vars mt)) in
    let enc = ok (fun () ->
        let v = Lm_symbol.add "q" in
        let e = Me.encode_free_var v in
        Me.is_encoded_free_var e && Lm_symbol.eq (Me.decode_free_var e) v && not (Me.is_encoded_free_var (mk_var_term v))) in
    [ zip; fn; alpha; differ; back; fv; enc ]
end

module Std = M (Refiner_std.Refiner)
module Ds = M (Refiner_ds.Refiner)

let names = [ "unzip_mimplies (zip_mimplies hs c)"; "unzip_mfunction (zip_mfunction vs c)";
              "meta_alpha_equal to a renamed copy"; "meta_alpha_equal iff the same";
              "meta_term_of_term (term_of_meta_term m)"; "free_vars_mterm = parts' + arguments";
              "decode (encode v) = v" ]

let () =
  let n = 400 in
  let tot_s = Array.make 7 0 and tot_d = Array.make 7 0 in
  for _ = 1 to n do
    let hs = List.init (pick 4) (fun _ -> gen [] 2) and c = gen [] 2 in
    let fs = List.init (pick 4) (fun i -> (if pick 2 = 0 then Some (Printf.sprintf "y%d" i) else None), gen [] 1) and fc = gen [] 2 in
    let mt = gm 3 and other = gm 3 in
    List.iteri (fun i b -> if b then tot_s.(i) <- tot_s.(i) + 1) (Std.checks (hs, c) (fs, fc) mt other);
    List.iteri (fun i b -> if b then tot_d.(i) <- tot_d.(i) + 1) (Ds.checks (hs, c) (fs, fc) mt other)
  done;
  Printf.printf "%d cases (std, ds)\n" n;
  List.iteri (fun i name -> Printf.printf "%-44s %4d %4d\n" name tot_s.(i) tot_d.(i)) names
;;
(* meta_alpha_equal ignores labels and a meta-function's variable, as it
   stands (term_meta_gen.ml, meta_alpha_equal): recorded, not endorsed. *)
let () =
  let cases = [
    "wf[T] vs main[T]", Lab ("wf", Th (Op ("c", []))), Lab ("main", Th (Op ("c", [])));
    "T vs wf[T]", Th (Op ("c", [])), Lab ("wf", Th (Op ("c", [])));
    "(a:c -> 'a) vs (b:c -> 'b)", Fun ("a", Op ("c", []), Th (Var "a")), Fun ("b", Op ("c", []), Th (Var "b"));
    "(a:c -> 'b) vs (b:c -> 'b)", Fun ("a", Op ("c", []), Th (Var "b")), Fun ("b", Op ("c", []), Th (Var "b")) ] in
  List.iter (fun (name, a, b) ->
      let r eq ma mb = try string_of_bool (eq (ma a) (mb b)) with _ -> "raises" in
      Printf.printf "meta_alpha_equal %-30s std %s, ds %s\n" name
        (r Refiner_std.Refiner.TermMeta.meta_alpha_equal Std.mbuild Std.mbuild)
        (r Refiner_ds.Refiner.TermMeta.meta_alpha_equal Ds.mbuild Ds.mbuild)) cases
