(* Ml_term (refiner/reflib/ml_term), which the filter uses to store terms,
   meta terms, opnames and numbers in a compiled theory as one string, and
   Lib_term's conversion between a sequent and the plain term that encodes
   it.  No unit test reached either (2026-11-02 census).  With the refiner
   the system uses (Refiner.Refiner), on 300 pseudo-random batches of 0-4
   terms (sequents, contexts, second-order variables, binders,
   parameters), 0-3 meta terms built from them, 0-3 opnames and 0-3
   numbers (some of them big integers):
     - term_arrays_of_string (string_of_term_lists ...) gives back each
       list, in order, as arrays: terms alpha_equal, meta terms
       meta_alpha_equal, opnames Opname.eq, numbers eq_num;
     - a string without the header, and a short one, are refused with
       Invalid_argument;
     - sequent_term_of_ugly_term (ugly_term_of_sequent_term s) is s for
       every sequent among the terms, the encoding is not a sequent, and
       Lib_term.make_term (Lib_term.dest_term t) is t for every term.
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
end
module B = S (Refiner.Refiner)
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.TermMeta

let () =
  let batches = List.init 300 (fun _ ->
      let ts = List.init (pick 5) (fun _ -> gen 3 [] 0) in
      let mts = List.init (pick 4) (fun _ -> pick 3, gen 2 [] 0, gen 2 [] 0) in
      let ops = List.init (pick 4) (fun _ -> [| [ "a" ]; [ "b"; "Mod" ]; [ "c"; "d"; "Mod" ] |].(pick 3)) in
      let nums = List.init (pick 4) (fun _ -> match pick 3 with 0 -> `Small (pick 100) | 1 -> `Prod (40000, 3) | _ -> `Big 5) in
      ts, mts, ops, nums) in
  let num = function
    | `Small i -> Lm_num.num_of_int i
    | `Prod (a, b) -> Lm_num.mult_num (Lm_num.num_of_int a) (Lm_num.num_of_int b)
    | `Big k -> Lm_num.power_num (Lm_num.num_of_int 1000) (Lm_num.num_of_int k) in
  let meta (k, a, b) =
    let a = B.build a and b = B.build b in
    match k with 0 -> MetaTheorem a | 1 -> MetaImplies (MetaTheorem a, MetaTheorem b) | _ -> MetaLabeled ("l", MetaIff (MetaTheorem a, MetaTheorem b)) in
  let ok = ref 0 and nts = ref 0 and nseq = ref 0 and seq_ok = ref 0 and dm_ok = ref 0 in
  List.iter (fun (ts, mts, ops, nums) ->
      let ts = List.map B.build ts and mts = List.map meta mts and ops = List.map Opname.make_opname ops and nums = List.map num nums in
      let s = Ml_term.string_of_term_lists ts mts ops nums in
      let ta, ma, oa, na = Ml_term.term_arrays_of_string s in
      let eq f l a = List.length l = Array.length a && List.for_all2 f l (Array.to_list a) in
      if eq alpha_equal ts ta && eq meta_alpha_equal mts ma && eq Opname.eq ops oa && eq Lm_num.eq_num nums na then incr ok;
      List.iter (fun t ->
          incr nts;
          if alpha_equal (Lib_term.make_term (Lib_term.dest_term t)) t then incr dm_ok;
          if is_sequent_term t then begin
            incr nseq;
            let u = Lib_term.ugly_term_of_sequent_term t in
            if not (is_sequent_term u) && alpha_equal (Lib_term.sequent_term_of_ugly_term u) t then incr seq_ok
          end) ts) batches;
  Printf.printf "%-52s %d of %d\n" "term_arrays_of_string (string_of_term_lists ...)" !ok (List.length batches);
  let refused s = try ignore (Ml_term.term_arrays_of_string s); "accepted" with Invalid_argument m -> "Invalid_argument " ^ m | e -> Printexc.to_string e in
  Printf.printf "%-52s %s\n" "a string without the header" (refused (String.make 40 'x'));
  Printf.printf "%-52s %s\n" "a short string" (refused "MP");
  Printf.printf "%-52s %d of %d\n" "Lib_term.make_term (Lib_term.dest_term t) = t" !dm_ok !nts;
  Printf.printf "%-52s %d of %d\n" "sequent -> ugly -> sequent (ugly is no sequent)" !seq_ok !nseq
