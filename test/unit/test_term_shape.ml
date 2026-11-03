(* Term shapes (refiner/term_gen/term_shape_gen): canonical_term_of_shape,
   opparam_of_term, shape_of_opparam and canonical_term_of_opparam, which
   no unit test reached (2026-11-02 profile).  On 500 generated terms --
   operators f, g, h with 0-2 parameters of each kind and 0-3 subterms of
   0-2 binders, plus variables and sequents -- in term_std and term_ds:
     - shape_of_term (canonical_term_of_shape s) is s (eq), for s the
       shape of the term;
     - shape_of_opparam (opparam_of_term t) is the shape of t, and so is
       the shape of canonical_term_of_opparam of it (operator terms);
     - shape_compare is 0 exactly when eq holds, and antisymmetric, on all
       pairs;
     - the two implementations print every shape the same.
   The generator is a fixed linear congruential sequence, not Random. *)
open Term_sig

let state = ref 5150
let next () = state := (!state * 1103515245 + 12345) land 0x7fffffff; !state lsr 8
let pick n = next () mod n

type prm = PN of int | PS of string | PT of string | PV of string | PMN of string | PMS of string | PL of int * (string * int) list
type d = Var of string | Op of string * prm list * (string list * d) list | Seq of d list * d

let gprm () =
  match pick 7 with
  | 0 -> PN (pick 3) | 1 -> PS [| "x"; "y" |].(pick 2) | 2 -> PT [| "ta"; "tb" |].(pick 2) | 3 -> PV "v"
  | 4 -> PMN "n" | 5 -> PMS "s"
  | _ -> PL (pick 2, if pick 2 = 0 then [ "k", pick 2 ] else [])
let rec gen depth =
  match pick (if depth = 0 then 2 else 5) with
  | 0 -> Var [| "a"; "b" |].(pick 2)
  | 1 -> Op ([| "f"; "g"; "h" |].(pick 3), List.init (pick 3) (fun _ -> gprm ()), [])
  | 2 | 3 -> Op ([| "f"; "g"; "h" |].(pick 3), List.init (pick 3) (fun _ -> gprm ()),
                List.init (pick 4) (fun _ -> List.init (pick 3) (fun i -> Printf.sprintf "x%d" i), gen (depth - 1)))
  | _ -> Seq (List.init (pick 3) (fun _ -> gen (depth - 1)), gen (depth - 1))

module S (R : Refiner_sig.RefinerSig) = struct
  open R.Term
  open R.TermMan
  module Sh = R.TermShape
  let op s = Opname.make_opname [ s ]
  let mk_prm = function
    | PN i -> make_param (Number (Lm_num.num_of_int i)) | PS s -> make_param (String s)
    | PT t -> make_param (Token (op t)) | PV v -> make_param (Var (Lm_symbol.add v))
    | PMN v -> make_param (MNumber (Lm_symbol.add v)) | PMS v -> make_param (MString (Lm_symbol.add v))
    | PL (c, vs) -> make_param (MLevel (mk_level c (List.map (fun (v, o) -> mk_level_var (Lm_symbol.add v) o) vs)))
  let rec build = function
    | Var v -> mk_var_term (Lm_symbol.add v)
    | Op (o, ps, bts) -> mk_term (mk_op (op o) (List.map mk_prm ps)) (List.map (fun (vs, t) -> mk_bterm (List.map Lm_symbol.add vs) (build t)) bts)
    | Seq (hs, c) ->
        mk_sequent_term { sequent_args = mk_simple_term (op "sa") [];
                          sequent_hyps = R.Term.SeqHyp.of_list (List.mapi (fun i h -> Hypothesis (Lm_symbol.add (Printf.sprintf "h%d" i), build h)) hs);
                          sequent_concl = build c }
  let safe f = try f () with e -> "EXN " ^ Printexc.to_string e
  (* each check: its printed value (compared across implementations) and whether it holds *)
  let checks d =
    let t = build d in
    let s = Sh.shape_of_term t in
    let canon = (try Sh.eq (Sh.shape_of_term (Sh.canonical_term_of_shape s)) s with _ -> false) in
    let opp =
      match d with
      | Op _ ->
          (try
             let o = Sh.opparam_of_term t in
             Sh.eq (Sh.shape_of_opparam o) s && Sh.eq (Sh.shape_of_term (Sh.canonical_term_of_opparam o)) s
           with _ -> false)
      | _ -> true in
    safe (fun () -> Sh.string_of_shape s), canon, opp, s
end

module Std = S (Refiner_std.Refiner)
module Ds = S (Refiner_ds.Refiner)

let () =
  let n = 500 in
  let ds = List.init n (fun _ -> gen 2) in
  let res_s = List.map Std.checks ds and res_d = List.map Ds.checks ds in
  let count f l = List.length (List.filter f l) in
  let ops = count (function Op _ -> true | _ -> false) ds in
  Printf.printf "%d terms (%d with an operator at the root)\n" n ops;
  Printf.printf "%-52s %4d of %d\n" "std and ds print the shape the same" (List.fold_left2 (fun k (a, _, _, _) (b, _, _, _) -> if a = b then k + 1 else k) 0 res_s res_d) n;
  let pr name res compare_ eq =
    Printf.printf "%-52s %4d of %d\n" (name ^ ": canonical term has the shape") (count (fun (_, c, _, _) -> c) res) n;
    Printf.printf "%-52s %4d of %d\n" (name ^ ": opparam round trip") (count (fun (_, _, o, _) -> o) res) n;
    let shapes = Array.of_list (List.map (fun (_, _, _, s) -> s) res) in
    let pairs = ref 0 and ok = ref 0 in
    Array.iter (fun a -> Array.iter (fun b ->
        incr pairs;
        let c = compare_ a b in
        if (c = 0) = eq a b && compare 0 c = compare (compare_ b a) 0 then incr ok) shapes) shapes;
    Printf.printf "%-52s %6d of %d\n" (name ^ ": shape_compare 0 iff eq, antisymmetric") !ok !pairs
  in
  pr "std" res_s Std.Sh.shape_compare Std.Sh.eq;
  pr "ds" res_d Ds.Sh.shape_compare Ds.Sh.eq
