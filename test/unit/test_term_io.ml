(* Stored proofs come back through term I/O: the ASCII proof files (.prla)
   are read with Ascii_io.  This test writes 2,000 pseudo-random terms
   (sequents with hypotheses and context hypotheses, second-order variables
   with contexts lists and arguments, binders) with AsciiIO.write_term,
   reads each back with read_table and get_term, and checks that the term
   read is alpha-equal to the term written, and prints the same.  It then
   does what the filter does when it saves a proof file
   (filter/base/filter_cache.ml): each term is written with the table read
   back from the previous term's file, so that names are reused, and read
   back.  The generator is a fixed linear
   congruential sequence, so the terms are the same on every OCaml. *)
open Lm_symbol
open Term_sig

(* A 31-bit linear congruential generator (glibc's constants). *)
let state = ref 12345
let next () = state := (!state * 1103515245 + 12345) land 0x7fffffff; !state lsr 8
let pick n = next () mod n

(* A term description, built in each implementation by the functor below. *)
type desc =
  | Var of string
  | SOVar of string * string list * desc list
  | Op of string * desc list
  | Bind of string * desc
  | Seq of string * hyp list * desc
and hyp = Hyp of string * desc | Ctx of string * string list * desc list

let conts () = List.filter (fun _ -> pick 2 = 0) [ "H"; "S" ]

let rec gen depth env n =
  let leaf () =
    match pick 3 with
    | 0 when env <> [] -> Var (List.nth env (pick (List.length env)))
    | 1 -> Var "z"
    | _ -> Op ("c", [])
  in
  if depth <= 0 then leaf ()
  else
    match pick 7 with
    | 0 | 1 -> leaf ()
    | 2 -> SOVar ((if pick 2 = 0 then "A" else "B"), conts (), List.init (pick 3) (fun _ -> gen (depth - 1) env n))
    | 3 -> Op ("f", List.init (1 + pick 2) (fun _ -> gen (depth - 1) env n))
    | 4 -> let x = Printf.sprintf "x%d" n in Bind (x, gen (depth - 1) (x :: env) (n + 1))
    | _ ->
        let rec hyps i env acc =
          if i = 0 then List.rev acc, env
          else if pick 3 = 0 then
            let k = Printf.sprintf "K%d" (n + i) in
            hyps (i - 1) (k :: env) (Ctx (k, conts (), List.init (pick 3) (fun _ -> gen (depth - 2) env n)) :: acc)
          else
            let v = Printf.sprintf "v%d" (n + i) in
            hyps (i - 1) (v :: env) (Hyp (v, gen (depth - 2) env n) :: acc)
        in
        let hs, env' = hyps (pick 4) env [] in
        Seq ((if pick 2 = 0 then "sa" else "sb"), hs, gen (depth - 1) env' (n + 10))

(* The same description with every bound name renamed (alpha-variant). *)
let rec rename = function
  | Var v -> Var v
  | SOVar (v, cs, ts) -> SOVar (v, cs, List.map rename ts)
  | Op (o, ts) -> Op (o, List.map rename ts)
  | Bind (x, t) -> Bind (x ^ "'", rename (subst x (x ^ "'") t))
  | Seq (a, hs, c) ->
      let rec go acc c = function
        | [] -> Seq (a, List.rev acc, rename c)
        | Hyp (v, t) :: hs ->
            let v' = v ^ "'" in
            go (Hyp (v', rename t) :: acc) (subst v v' c) (List.map (subst_hyp v v') hs)
        | Ctx (k, cs, ts) :: hs -> go (Ctx (k, cs, List.map rename ts) :: acc) c hs
      in
      go [] c hs
and subst x y = function
  | Var v -> Var (if v = x then y else v)
  | SOVar (v, cs, ts) -> SOVar (v, cs, List.map (subst x y) ts)
  | Op (o, ts) -> Op (o, List.map (subst x y) ts)
  | Bind (z, t) -> if z = x then Bind (z, t) else Bind (z, subst x y t)
  | Seq (a, hs, c) ->
      let rec go acc = function
        | [] -> Seq (a, List.rev acc, subst x y c)
        | Hyp (v, t) :: hs when v = x -> Seq (a, List.rev_append acc (Hyp (v, subst x y t) :: hs), c)
        | Hyp (v, t) :: hs -> go (Hyp (v, subst x y t) :: acc) hs
        | Ctx (k, cs, ts) :: hs -> go (Ctx (k, cs, List.map (subst x y) ts) :: acc) hs
      in
      go [] hs
and subst_hyp x y = function
  | Hyp (v, t) -> Hyp (v, subst x y t)
  | Ctx (k, cs, ts) -> Ctx (k, cs, List.map (subst x y) ts)

module Io (R : Refiner_sig.RefinerSig with type TermType.term = Refiner.Refiner.TermType.term) = struct
  open R.Term
  open R.TermMan
  let op s = Opname.make_opname [ s ]
  let rec build = function
    | Var v -> mk_var_term (add v)
    | SOVar (v, cs, ts) -> mk_so_var_term (add v) (List.map add cs) (List.map build ts)
    | Op (o, ts) -> mk_simple_term (op o) (List.map build ts)
    | Bind (x, t) -> mk_term (mk_op (op "lam") []) [ mk_bterm [ add x ] (build t) ]
    | Seq (a, hs, c) ->
        mk_sequent_term
          { sequent_args = mk_simple_term (op a) [];
            sequent_hyps = R.Term.SeqHyp.of_list (List.map (function
                | Hyp (v, t) -> Hypothesis (add v, build t)
                | Ctx (k, cs, ts) -> Context (add k, List.map add cs, List.map build ts)) hs);
            sequent_concl = build c }

  let rec show t =
    if is_sequent_term t then
      let s = explode_sequent t in
      "sequent[" ^ show s.sequent_args ^ "]{ " ^ String.concat "; " (List.map (function
          | Hypothesis (v, a) -> string_of_symbol v ^ ": " ^ show a
          | Context (v, cs, args) ->
              "<" ^ string_of_symbol v ^ "<|" ^ String.concat ";" (List.map string_of_symbol cs) ^ "|>["
              ^ String.concat "; " (List.map show args) ^ "]>")
          (R.Term.SeqHyp.to_list s.sequent_hyps)) ^ " >- " ^ show s.sequent_concl ^ " }"
    else if is_var_term t then "'" ^ string_of_symbol (dest_var t)
    else if is_so_var_term t then
      let v, cs, args = dest_so_var t in
      string_of_symbol v ^ "<|" ^ String.concat ";" (List.map string_of_symbol cs) ^ "|>["
      ^ String.concat "; " (List.map show args) ^ "]"
    else
      let { term_op; term_terms } = dest_term t in
      let name = String.concat "!" (Opname.dest_opname (dest_op term_op).op_name) in
      if term_terms = [] then name
      else name ^ "{" ^ String.concat "; " (List.map (fun b ->
          let { bvars; bterm } = dest_bterm b in
          (if bvars = [] then "" else String.concat "," (List.map string_of_symbol bvars) ^ ". ") ^ show bterm)
          term_terms) ^ "}"

end

module T = Io (Refiner.Refiner)
module A = Ascii_io.AsciiIO

let roundtrip ?(table = A.initialize ()) terms =
  let file = Filename.temp_file "metaprl_io" ".prla" in
  let oc = open_out_bin file in
  List.iter (A.write_term oc table) terms;
  close_out oc;
  let ic = open_in_bin file in
  let table = A.read_table ic in
  close_in ic;
  Sys.remove file;
  table

let () =
  let n = 2000 in
  let alpha = ref 0 and same = ref 0 and raised = ref 0 and first = ref None in
  let all = ref [] in
  for i = 1 to n do
    let t = T.build (gen 4 [] 0) in
    all := t :: !all;
    match A.get_term (roundtrip [ t ]) with
    | t' ->
        if Refiner.Refiner.TermSubst.alpha_equal t t' then incr alpha
        else if !first = None then first := Some (i, T.show t, T.show t');
        if T.show t = T.show t' then incr same
    | exception e -> incr raised; if !first = None then first := Some (i, T.show t, Printexc.to_string e)
  done;
  Printf.printf "one term per file: %d of %d read back alpha-equal, %d print the same, %d raise\n" !alpha n !same !raised;
  (match !first with
   | None -> ()
   | Some (i, a, b) -> Printf.printf "  first difference, term %d:\n    wrote %s\n    read  %s\n" i a b);
  (* As the filter saves a file: write with the table of the previous version. *)
  let alpha = ref 0 and raised = ref 0 and first = ref None in
  let table = ref (A.initialize ()) in
  List.iteri (fun i t ->
      match roundtrip ~table:!table [ t ] with
      | tbl ->
          (match A.get_term tbl with
           | t' -> if Refiner.Refiner.TermSubst.alpha_equal t t' then incr alpha
                   else if !first = None then first := Some (i + 1, T.show t, T.show t')
           | exception e -> incr raised; if !first = None then first := Some (i + 1, T.show t, Printexc.to_string e));
          table := tbl
      | exception e -> incr raised; if !first = None then first := Some (i + 1, T.show t, Printexc.to_string e))
    (List.rev !all);
  Printf.printf "each written with the previous file's table: %d of %d read back alpha-equal, %d raise\n" !alpha n !raised;
  match !first with
  | None -> ()
  | Some (i, a, b) -> Printf.printf "  first difference, term %d:\n    wrote %s\n    read  %s\n" i a b
