(* The variable-info functions of term_man (refiner/term_gen/term_man_gen
   and term_ds/term_man_ds) whose list forms no unit test reached
   (2026-11-02): param_vars_info(_list), so_vars_info(_list),
   context_vars_info(_list) and all_vars_terms.  On 1500 pseudo-random terms
   (sequents with hypotheses and context hypotheses, second-order variables
   with contexts and arguments, binders, operators with parameters: meta
   numbers and strings, numbers, parameter lists, operator parameters) and
   1500 lists of 1-3 of them:
     - param_vars_info is the set of meta-variables named by the
       parameters, looking inside parameter lists and not inside operator
       parameters (the code's two cases);
     - so_vars_info names exactly the second-order variables, and
       context_vars_info exactly the context hypotheses, each marked as a
       sequent context;
     - each _list form is the fold of the single form over the list, and
       all_vars_terms is the union of all_vars;
     - term_std and term_ds give the same tables and sets.
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
let rec pnames acc = function PM v | PS v -> v :: acc | PN _ | PO _ -> acc | PL l -> List.fold_left pnames acc l
let rec fold f acc d =
  let acc = f acc d in
  match d with
  | Var _ -> acc | SOVar (_, _, ts) | Op (_, _, ts) -> List.fold_left (fold f) acc ts | Bind (_, t) -> fold f acc t
  | Seq (_, hs, c) -> fold f (List.fold_left (fun acc -> function Hyp (_, t) -> fold f acc t | Ctx (_, _, ts) -> List.fold_left (fold f) acc ts) acc hs) c
let uniq l = List.sort_uniq compare l
let m_params d = uniq (fold (fun acc -> function Op (_, ps, _) -> List.fold_left pnames acc ps | _ -> acc) [] d)
let m_so d = uniq (fold (fun acc -> function SOVar (v, _, _) -> v :: acc | _ -> acc) [] d)
let m_ctx d = uniq (fold (fun acc -> function Seq (_, hs, _) -> List.fold_left (fun acc -> function Ctx (k, _, _) -> k :: acc | _ -> acc) acc hs | _ -> acc) [] d)

module S (R : Refiner_sig.RefinerSig) = struct
  open R.Term
  open R.TermMan
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
  let set s = List.sort Stdlib.compare (List.map to_string (SymbolSet.elements s))
  let keys tb = List.sort Stdlib.compare (SymbolTable.fold (fun acc v _ -> to_string v :: acc) [] tb)
  let ctab tb = List.sort Stdlib.compare (SymbolTable.fold (fun acc v (b, x, y) -> Printf.sprintf "%s:%b/%d/%d" (to_string v) b x y :: acc) [] tb)
  let stab tb = List.sort Stdlib.compare (SymbolTable.fold (fun acc v (x, y) -> Printf.sprintf "%s:%d/%d" (to_string v) x y :: acc) [] tb)
  let flags tb = SymbolTable.fold (fun acc _ (b, _, _) -> acc && b) true tb

  (* per term and per list: what is printed for the std/ds comparison, and which checks hold *)
  let one d =
    let t = build d in
    let p = param_vars_info SymbolSet.empty t and so = so_vars_info SymbolTable.empty t and cx = context_vars_info SymbolTable.empty t in
    String.concat " | " [ String.concat "," (set p); String.concat "," (stab so); String.concat "," (ctab cx) ],
    [| set p = m_params d; keys so = m_so d; keys cx = m_ctx d && flags cx |]
  let many ds =
    let ts = List.map build ds in
    let p = param_vars_info_list SymbolSet.empty ts and so = so_vars_info_list SymbolTable.empty ts
    and cx = context_vars_info_list SymbolTable.empty ts and av = all_vars_terms ts in
    String.concat " | " [ String.concat "," (set p); String.concat "," (stab so); String.concat "," (ctab cx); String.concat "," (set av) ],
    [| set p = set (List.fold_left param_vars_info SymbolSet.empty ts);
       stab so = stab (List.fold_left so_vars_info SymbolTable.empty ts);
       ctab cx = ctab (List.fold_left context_vars_info SymbolTable.empty ts);
       set av = set (List.fold_left (fun s t -> SymbolSet.union s (all_vars t)) SymbolSet.empty ts) |]
end

module Std = S (Refiner_std.Refiner)
module Ds = S (Refiner_ds.Refiner)

let () =
  let terms = List.init 1500 (fun _ -> gen 4 [] 0) in
  let lists = List.init 1500 (fun _ -> List.init (1 + pick 3) (fun _ -> gen 3 [] 0)) in
  let count p = List.length (List.filter p terms) in
  Printf.printf "1500 terms: %d with parameter meta-variables, %d with an SO variable, %d with a context hypothesis; 1500 lists of 1-3\n"
    (count (fun d -> m_params d <> [])) (count (fun d -> m_so d <> [])) (count (fun d -> m_ctx d <> []));
  let r1s = List.map Std.one terms and r1d = List.map Ds.one terms and r2s = List.map Std.many lists and r2d = List.map Ds.many lists in
  let agree a b = List.fold_left2 (fun k (x, _) (y, _) -> if x = y then k + 1 else k) 0 a b in
  Printf.printf "%-48s %4d of 1500\n" "std and ds give the same info (terms)" (agree r1s r1d);
  Printf.printf "%-48s %4d of 1500\n" "std and ds give the same info (lists)" (agree r2s r2d);
  let names1 = [| "param_vars_info = the model"; "so_vars_info names the SO variables"; "context_vars_info names the contexts" |] in
  let names2 = [| "param_vars_info_list = fold"; "so_vars_info_list = fold"; "context_vars_info_list = fold"; "all_vars_terms = union of all_vars" |] in
  List.iter (fun (impl, r1, r2) ->
      Array.iteri (fun i nm -> Printf.printf "%-48s %4d of 1500\n" (impl ^ ": " ^ nm) (List.length (List.filter (fun (_, a) -> a.(i)) r1))) names1;
      Array.iteri (fun i nm -> Printf.printf "%-48s %4d of 1500\n" (impl ^ ": " ^ nm) (List.length (List.filter (fun (_, a) -> a.(i)) r2))) names2)
    [ "std", r1s, r2s; "ds", r1d, r2d ]
