(* The msequent accessors of Refine (refiner/refiner/refine.ml): the
   statement of a proof step, a goal with its assumptions.  No unit test
   reached msequent_num_assums, msequent_nth_assum, msequent_all_assums or
   msequent_alpha_equal (2026-11-02 census).  In term_std and term_ds, on
   1000 pseudo-random msequents (a goal and 0-4 assumptions, each a term
   with sequents, contexts, second-order variables, binders, parameters):
     - msequent_num_assums is the number of assumptions, msequent_all_assums
       the assumptions, and msequent_nth_assum i the i-th, counting from 1;
       0 and one past the end are refused;
     - mk_msequent / dest_msequent / msequent_goal round-trip;
     - msequent_alpha_equal holds against the msequent rebuilt from the
       same description, and fails when the goal differs, when one
       assumption differs, and when an assumption is dropped.
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
  open R.Refine
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
  let run name ms =
    let n = List.length ms in
    let c = Array.make 4 0 in
    let chk i b = if b then c.(i) <- c.(i) + 1 in
    let other = mk_simple_term (op "other") [] in
    List.iter (fun (g, hs) ->
        let goal = build g and assums = List.map build hs in
        let m = mk_msequent goal assums in
        let k = List.length assums in
        chk 0 (msequent_num_assums m = k
               && List.for_all2 alpha_equal (msequent_all_assums m) assums
               && List.for_all (fun i -> try alpha_equal (msequent_nth_assum m i) (List.nth assums (i - 1)) with _ -> false) (List.init k (fun i -> i + 1))
               && (try ignore (msequent_nth_assum m 0); false with _ -> true)
               && (try ignore (msequent_nth_assum m (k + 1)); false with _ -> true));
        chk 1 (let g', a' = dest_msequent m in alpha_equal g' goal && alpha_equal (msequent_goal m) goal && List.for_all2 alpha_equal a' assums);
        let m' = mk_msequent (build g) (List.map build hs) in
        chk 2 (msequent_alpha_equal m m' && msequent_alpha_equal m m);
        chk 3 (not (msequent_alpha_equal m (mk_msequent other assums))
               && (k = 0 || not (msequent_alpha_equal m (mk_msequent goal (other :: List.tl assums))))
               && (k = 0 || not (msequent_alpha_equal m (mk_msequent goal (List.tl assums)))))) ms;
    List.iteri (fun i nm -> Printf.printf "%-52s %4d of %d\n" (name ^ ": " ^ nm) c.(i) n)
      [ "num/all/nth assums (1-based; 0 and k+1 refused)"; "mk/dest_msequent, msequent_goal round trip";
        "msequent_alpha_equal: same description"; "msequent_alpha_equal: goal, an assumption, length" ]
end

module Std = S (Refiner_std.Refiner)
module Ds = S (Refiner_ds.Refiner)

let () =
  let ms = List.init 1000 (fun _ -> gen 3 [] 0, List.init (pick 5) (fun _ -> gen 3 [] 0)) in
  Printf.printf "1000 msequents (%d with no assumption)\n" (List.length (List.filter (fun (_, hs) -> hs = []) ms));
  Std.run "std" ms;
  Ds.run "ds" ms
