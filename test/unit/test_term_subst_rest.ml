(* TermSubst functions no unit test reached (2026-11-02 census over master
   and every open branch): alpha_equal_vars, alpha_equal_fun,
   dest_bterm_and_rename, equal_operators, equal_params, free_vars_terms,
   is_some_var_free_list.  On 1500 pseudo-random terms (sequents, contexts,
   second-order variables, binders, parameters) whose free first-order
   variable is 'z, in term_std and term_ds, each against an oracle that
   does not use it:
     - alpha_equal_vars t1 [z] t2 [v] is alpha_equal of lam{z. t1} and
       lam{v. t2}, for t2 = t1, t1 with 'z renamed 'p, or another term;
     - alpha_equal_fun (alpha_equal) t [z] t' [s] holds exactly when t' is
       alpha_equal to subst t [z] [s], for t' = that substitution with s or
       with another term, or t itself;
     - dest_bterm_and_rename avoid bt gives bound variables outside avoid,
       and the bound term rebuilt from them is alpha_equal to bt;
     - equal_operators and equal_params agree with alpha_equal of the
       operator applied to no subterms;
     - free_vars_terms is the union of free_vars_set, and
       is_some_var_free_list vs ts says whether some v is free in some t.
   The generator is a fixed linear congruential sequence, not Random. *)
open Term_sig
let state = ref 4949
let next () = state := (!state * 1103515245 + 12345) land 0x7fffffff; !state lsr 8
let pick n = next () mod n

type prm = PM of string | PS of string | PN of int | PL of prm list | PO of string
type desc =
  | Var of string
  | SOVar of string * string list * desc list
  | Op of string * prm list * desc list
  | Bind of string * desc
  | Seq of string * hyp list * desc
and hyp = Hyp of string * desc | Ctx of string * string list * desc list

(* names carry no digits: Lm_symbol.add splits trailing digits off a name *)
let letters n = String.init 2 (fun i -> Char.chr (97 + (if i = 0 then n / 26 else n) mod 26))
let conts () = List.filter (fun _ -> pick 2 = 0) [ "H"; "S" ]
let rec gprm d =
  match pick (if d = 0 then 4 else 5) with
  | 0 -> PM [| "m"; "n" |].(pick 2) | 1 -> PS [| "s"; "t" |].(pick 2) | 2 -> PN (pick 3) | 3 -> PO [| "m"; "q" |].(pick 2)
  | _ -> PL (List.init (pick 3) (fun _ -> gprm (d - 1)))
let rec gen depth env n =
  let leaf () =
    match pick 3 with
    | 0 when env <> [] -> Var (List.nth env (pick (List.length env)))
    | 1 -> Var "z"
    | _ -> Op ("c", List.init (pick 2) (fun _ -> gprm 1), [])
  in
  if depth <= 0 then leaf ()
  else
    match pick 7 with
    | 0 | 1 -> leaf ()
    | 2 -> SOVar ((if pick 2 = 0 then "A" else "B"), conts (), List.init (pick 3) (fun _ -> gen (depth - 1) env n))
    | 3 -> Op ("f", List.init (pick 3) (fun _ -> gprm 1), List.init (1 + pick 2) (fun _ -> gen (depth - 1) env n))
    | 4 -> let x = "x" ^ letters n in Bind (x, gen (depth - 1) (x :: env) (n + 1))
    | _ ->
        let rec hyps i env acc =
          if i = 0 then List.rev acc, env
          else if pick 3 = 0 then
            let k = "K" ^ letters (n + i) in
            hyps (i - 1) (k :: env) (Ctx (k, conts (), List.init (pick 3) (fun _ -> gen (depth - 2) env n)) :: acc)
          else
            let v = "v" ^ letters (n + i) in
            hyps (i - 1) (v :: env) (Hyp (v, gen (depth - 2) env n) :: acc)
        in
        let hs, env' = hyps (pick 4) env [] in
        Seq ((if pick 2 = 0 then "sa" else "sb"), hs, gen (depth - 1) env' (n + 10))

(* the models: names collected from the description *)
let rec rename = function
  | Var "z" -> Var "p" | Var v -> Var v
  | SOVar (v, cs, ts) -> SOVar (v, cs, List.map rename ts) | Op (o, ps, ts) -> Op (o, ps, List.map rename ts)
  | Bind (x, t) -> Bind (x, rename t)
  | Seq (a, hs, c) -> Seq (a, List.map (function Hyp (v, t) -> Hyp (v, rename t) | Ctx (k, cs, ts) -> Ctx (k, cs, List.map rename ts)) hs, rename c)

module S (R : Refiner_sig.RefinerSig) = struct
  open R.Term
  open R.TermMan
  open R.TermSubst
  open Lm_symbol
  let op s = Opname.make_opname [ s ]
  let rec mk_p = function
    | PM v -> make_param (Term_sig.MNumber (add v)) | PS v -> make_param (Term_sig.MString (add v))
    | PN i -> make_param (Term_sig.Number (Lm_num.num_of_int i)) | PL l -> make_param (Term_sig.ParamList (List.map mk_p l))
    | PO v -> make_param (Term_sig.Operator { Term_sig.opparam_name = op "o"; opparam_params = [ make_param (Term_sig.MNumber (add v)) ]; opparam_arities = [] })
  let rec build = function
    | Var v -> mk_var_term (add v)
    | SOVar (v, cs, ts) -> mk_so_var_term (add v) (List.map add cs) (List.map build ts)
    | Op (o, ps, ts) -> mk_term (mk_op (op o) (List.map mk_p ps)) (List.map (fun t -> mk_simple_bterm (build t)) ts)
    | Bind (x, t) -> mk_term (mk_op (op "lam") []) [ mk_bterm [ add x ] (build t) ]
    | Seq (a, hs, c) ->
        mk_sequent_term
          { sequent_args = mk_simple_term (op a) [];
            sequent_hyps = R.Term.SeqHyp.of_list (List.map (function
                | Hyp (v, t) -> Hypothesis (add v, build t)
                | Ctx (k, cs, ts) -> Context (add k, List.map add cs, List.map build ts)) hs);
            sequent_concl = build c }
  let lam v t = mk_term (mk_op (op "lam") []) [ mk_bterm [ add v ] t ]
  let safe f = try f () with _ -> false
  let run name terms others =
    let n = List.length terms in
    let c = Array.make 8 0 in
    let chk i b = if b then c.(i) <- c.(i) + 1 in
    List.iteri (fun k d ->
        let t1 = build d and o = build (List.nth others k) in
        (* 0: alpha_equal_vars *)
        let cases = [ t1, "z"; build (rename d), "p"; o, "p"; t1, "p" ] in
        chk 0 (List.for_all (fun (t2, v) ->
            safe (fun () -> alpha_equal_vars t1 [ add "z" ] t2 [ add v]) = alpha_equal (lam "z" t1) (lam v t2)) cases);
        (* 1: alpha_equal_fun *)
        let s = mk_simple_term (op "s") [] and s' = mk_simple_term (op "r") [] in
        let sub = subst t1 [ add "z" ] [ s ] in
        let f a b = alpha_equal a b in
        chk 1 (List.for_all (fun (t', item) ->
            safe (fun () -> alpha_equal_fun f t1 [ add "z" ] t' [ item ]) = alpha_equal t' (subst t1 [ add "z" ] [ item ]))
            [ sub, s; sub, s'; t1, s; subst t1 [ add "z" ] [ s' ], s ]);
        (* 2: dest_bterm_and_rename *)
        let avoid = SymbolSet.add (SymbolSet.add (free_vars_set t1) (add "q")) (add "z") in
        let bt = mk_bterm [ add "q"; add "z" ] t1 in
        chk 2 (safe (fun () ->
            let { bvars = vs; bterm = b } = dest_bterm_and_rename avoid bt in
            List.for_all (fun v -> not (SymbolSet.mem avoid v)) vs
            && alpha_equal (mk_term (mk_op (op "lam") []) [ mk_bterm vs b ]) (mk_term (mk_op (op "lam") []) [ bt ])));
        (* 3, 4: free_vars_terms, is_some_var_free_list *)
        let ts = [ t1; o ] in
        chk 3 (SymbolSet.equal (free_vars_terms ts) (SymbolSet.union (free_vars_set t1) (free_vars_set o)));
        chk 4 (List.for_all (fun vs ->
            is_some_var_free_list vs ts = List.exists (fun v -> List.exists (fun t -> SymbolSet.mem (free_vars_set t) v) ts) vs)
            [ [ add "z" ]; [ add "p"; add "z" ]; [ add "p" ]; [] ])) terms;
    let names = [| "alpha_equal_vars = alpha_equal under lam"; "alpha_equal_fun = alpha_equal to subst";
                   "dest_bterm_and_rename avoids, keeps the term"; "free_vars_terms = union";
                   "is_some_var_free_list = exists" |] in
    Array.iteri (fun i nm -> Printf.printf "%-50s %4d of %d\n" (name ^ ": " ^ nm) c.(i) n) names;
    (* equal_operators / equal_params against alpha_equal on the bare operator *)
    let ops = List.map (fun d -> match d with Op (o, ps, _) -> Some (o, ps) | _ -> None) (terms @ others) |> List.filter_map Fun.id in
    let arr = Array.of_list ops in
    let m = Array.length arr in
    let agree = ref 0 and pairs = ref 0 and eqs = ref 0 in
    for i = 0 to m - 1 do
      let j = (i * 7 + 3) mod m in
      List.iter (fun (a, b) ->
          incr pairs;
          let oa = mk_op (op (fst a)) (List.map mk_p (snd a)) and ob = mk_op (op (fst b)) (List.map mk_p (snd b)) in
          let truth = alpha_equal (mk_term oa []) (mk_term ob []) in
          if truth then incr eqs;
          let ps_eq = List.length (snd a) = List.length (snd b)
                      && List.for_all2 (fun x y -> equal_params (mk_p x) (mk_p y)) (snd a) (snd b) in
          if equal_operators oa ob = truth && (fst a <> fst b || ps_eq = truth) then incr agree)
        [ arr.(i), arr.(i); arr.(i), arr.(j) ]
    done;
    Printf.printf "%-50s %4d of %d (%d equal)\n" (name ^ ": equal_operators, equal_params = alpha_equal") !agree !pairs !eqs
end

module Std = S (Refiner_std.Refiner)
module Ds = S (Refiner_ds.Refiner)

let () =
  let terms = List.init 1500 (fun _ -> gen 4 [] 0) and others = List.init 1500 (fun _ -> gen 4 [] 0) in
  let rec has_z = function
    | Var v -> v = "z" | SOVar (_, _, ts) | Op (_, _, ts) -> List.exists has_z ts | Bind (_, t) -> has_z t
    | Seq (_, hs, c) -> has_z c || List.exists (function Hyp (_, t) -> has_z t | Ctx (_, _, ts) -> List.exists has_z ts) hs in
  Printf.printf "1500 terms (%d with a free 'z), 1500 others\n" (List.length (List.filter has_z terms));
  Std.run "std" terms others;
  Ds.run "ds" terms others
