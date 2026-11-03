(* Term_base projections and simple terms, and the Term_addr functions no
   unit test reached (2026-11-02 census over master and every open branch).
   In term_std and term_ds, on 1500 pseudo-random terms (sequents,
   contexts, second-order variables, binders, parameters):
     - opname_of_term, subterms_of_term and subterm_arities of an operator
       term are its name, the bodies of its bound terms and their binder
       counts, as described;
     - mk_any_term op ts has subterms ts, all with no binders;
       dest_simple_term and dest_simple_term_opname undo mk_simple_term,
       is_simple_term_opname holds for its own name only, and a term with a
       parameter or a bound subterm is not simple; dest_simple_bterm undoes
       mk_simple_bterm and is_simple_bterm refuses a binder;
     - at every address subterm_addresses lists, apply_fun_arg_at_addr f
       gives what apply_fun_at_addr gives with the term part of f, and the
       other part of f at term_subterm; the subterm at the address is then
       f of the old one (term_ds defines apply_fun_at_addr through
       apply_fun_arg_at_addr, so this is the check that does not share its
       code), and an identity f gives the term back;
       apply_var_fun_arg_at_addr likewise, and both pass f the same
       variable set; term_subterm at
       null_address is the term;
     - on a sequent, split_clause_address of a clause address gives the
       clause and the rest, and compose_address puts them back (the same
       subterm); any other address is refused.
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
module S (R : Refiner_sig.RefinerSig) = struct
  open R.Term
  open R.TermMan
  open R.TermSubst
  open R.TermAddr
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
  let safe f = try f () with _ -> false
  let refused f = try ignore (f ()); false with R.RefineError.RefineError _ -> true | _ -> false
  let run name terms =
    let n = List.length terms in
    let c = Array.make 6 0 in
    let chk i b = if b then c.(i) <- c.(i) + 1 in
    let naddr = ref 0 and nseq = ref 0 and nclause = ref 0 in
    List.iter (fun d ->
        let t = build d in
        (* 0: projections, against the description *)
        chk 0 (match d with
            | Op (o, _, ts) ->
                Opname.eq (opname_of_term t) (op o) && List.length (subterms_of_term t) = List.length ts
                && List.for_all2 alpha_equal (subterms_of_term t) (List.map build ts)
                && subterm_arities t = List.map (fun _ -> 0) ts
            | Bind (x, b) -> Opname.eq (opname_of_term t) (op "lam") && subterm_arities t = [ 1 ]
                             && (match subterms_of_term t with [ s ] -> alpha_equal (mk_term (mk_op (op "lam") []) [ mk_bterm [ add x ] s ]) t | _ -> false)
                             && ignore b = ()
            | _ -> true);
        let addrs = try subterm_addresses t with _ -> [] in
        naddr := !naddr + List.length addrs;
        (* 1: apply_fun_arg_at_addr = apply_fun_at_addr + f at term_subterm *)
        let wrap s = mk_simple_term (op "w") [ s ] in
        chk 1 (List.for_all (fun a -> safe (fun () ->
            let t', tag = apply_fun_arg_at_addr (fun s -> wrap s, Opname.string_of_opname (opname_of_term s)) a t in
            alpha_equal t' (apply_fun_at_addr wrap a t) && tag = Opname.string_of_opname (opname_of_term (term_subterm t a))
            (* term_ds builds apply_fun_at_addr from apply_fun_arg_at_addr, so also check against term_subterm *)
            && alpha_equal (term_subterm t' a) (wrap (term_subterm t a))
            && alpha_equal (fst (apply_fun_arg_at_addr (fun s -> s, ()) a t)) t)) addrs);
        (* 2: apply_var_fun_arg_at_addr, and the variable sets passed to f *)
        let vs0 = SymbolSet.add SymbolSet.empty (add "q") in
        chk 2 (List.for_all (fun a -> safe (fun () ->
            let seen1 = ref SymbolSet.empty and seen2 = ref SymbolSet.empty in
            let t1, k = apply_var_fun_arg_at_addr (fun vs s -> seen1 := vs; wrap s, SymbolSet.cardinal vs) a vs0 t in
            let t2 = apply_var_fun_at_addr (fun vs s -> seen2 := vs; wrap s) a vs0 t in
            alpha_equal t1 t2 && SymbolSet.equal !seen1 !seen2 && k = SymbolSet.cardinal !seen2
            && alpha_equal (term_subterm t1 a) (wrap (term_subterm t a)))) addrs);
        (* 3: null_address *)
        chk 3 (safe (fun () -> alpha_equal (term_subterm t null_address) t));
        (* 4: split_clause_address on sequents *)
        chk 4 (if is_sequent_term t then begin
            incr nseq;
            List.for_all (fun a -> safe (fun () ->
                match (try Some (split_clause_address a) with R.RefineError.RefineError _ -> None) with
                | Some (a1, a2) -> incr nclause; alpha_equal (term_subterm t (compose_address a1 a2)) (term_subterm t a)
                | None -> true)) addrs
          end else List.for_all (fun a -> refused (fun () -> split_clause_address a)) addrs)) terms;
    let names = [| "opname/subterms/arities = the description"; "apply_fun_arg_at_addr at every address";
                   "apply_var_fun_arg_at_addr, same variable set"; "term_subterm t null_address = t";
                   "split_clause_address (sequents; refused off them)" |] in
    Printf.printf "%s: %d addresses, %d sequents, %d clause addresses split\n" name !naddr !nseq !nclause;
    Array.iteri (fun i nm -> Printf.printf "%-52s %4d of %d\n" (name ^ ": " ^ nm) c.(i) n) names;
    (* simple terms and bound terms *)
    let a = mk_simple_term (op "c") [] and b = mk_var_term (add "x") in
    let o, ts = dest_simple_term (mk_simple_term (op "f") [ a; b ]) in
    let any = mk_any_term (mk_op (op "g") [ make_param (Number (Lm_num.num_of_int 1)) ]) [ a; b ] in
    let with_param = mk_term (mk_op (op "f") [ make_param (Number (Lm_num.num_of_int 1)) ]) [ mk_simple_bterm a ] in
    let with_binder = mk_term (mk_op (op "f") []) [ mk_bterm [ add "y" ] a ] in
    List.iter (fun (what, v) -> Printf.printf "%-52s %b\n" (name ^ ": " ^ what) v)
      [ "dest_simple_term (mk_simple_term f [c; x])", Opname.eq o (op "f") && List.length ts = 2 && List.for_all2 alpha_equal ts [ a; b ];
        "dest_simple_term_opname f", (match dest_simple_term_opname (op "f") (mk_simple_term (op "f") [ a ]) with [ s ] -> alpha_equal s a | _ -> false);
        "is_simple_term_opname f, own / other name", is_simple_term_opname (op "f") (mk_simple_term (op "f") [ a ]) && not (is_simple_term_opname (op "g") (mk_simple_term (op "f") [ a ]));
        "mk_any_term: subterms, arities 0", List.for_all2 alpha_equal (subterms_of_term any) [ a; b ] && subterm_arities any = [ 0; 0 ];
        "with a parameter: not simple, dest refused", not (is_simple_term_opname (op "f") with_param) && refused (fun () -> dest_simple_term with_param);
        "with a binder: not simple, dest refused", not (is_simple_term_opname (op "f") with_binder) && refused (fun () -> dest_simple_term with_binder);
        "dest_simple_bterm (mk_simple_bterm c)", is_simple_bterm (mk_simple_bterm a) && alpha_equal (dest_simple_bterm (mk_simple_bterm a)) a;
        "is_simple_bterm of a binder", not (is_simple_bterm (mk_bterm [ add "y" ] a)) ]
end

module Std = S (Refiner_std.Refiner)
module Ds = S (Refiner_ds.Refiner)

let () =
  let terms = List.init 1500 (fun _ -> gen 4 [] 0) in
  Printf.printf "1500 terms, %d with an operator or binder at the root (the projection check's population)\n"
    (List.length (List.filter (function Op _ | Bind _ -> true | _ -> false) terms));
  Std.run "std" terms;
  Ds.run "ds" terms
