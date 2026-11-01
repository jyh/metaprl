(* Term_copy2_weak (refiner/reflib) copies terms between two term
   implementations through their hash-consing tables; the proof cache of
   the filter and Term_io's normaliser use it.  This test copies the same
   2,000 pseudo-random terms (sequents with hypotheses and contexts,
   second-order variables with contexts and arguments, binders) between
   term_std and term_ds, and checks, printed structurally:
     - convert of the std term is the ds term built from the same
       description, and revert of the ds term is the std term;
     - revert (convert t) is t;
     - two copies of one term convert to ONE term (physically equal), with
       a full major GC between the two converts, the first result kept
       alive, and the first convert the term's first conversion.
       Weak_memo remakes a collected entry under its stored descriptor
       (3811510d7), so a header that names it still matches.
       Before that fix this check read 1,038 of 2,000 (measured 2026-11-01
       by building this test against the earlier weak_memo.ml); the terms
       that split carry binders (lam or sequent hypotheses).
   The generator is the fixed linear congruential sequence of
   test_term_differential.ml. *)
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

module B (R : Refiner_sig.RefinerSig) = struct
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

module S = B (Refiner_std.Refiner)
module D = B (Refiner_ds.Refiner)
module C = Term_copy2_weak.TermCopy2Weak (Refiner_std.Refiner) (Refiner_ds.Refiner)

let () =
  let n = 2000 in
  let names = [ "convert std = ds"; "revert ds = std"; "revert (convert t) = t";
                "two copies convert to one term" ] in
  let ok = Array.make 4 0 and first = Array.make 4 None in
  let note k b d = if b then ok.(k) <- ok.(k) + 1 else if first.(k) = None then first.(k) <- Some d in
  for _ = 1 to n do
    let d = gen 4 [] 0 in
    let s = S.build d and t = D.build d in
    (* First, before any other convert of this term: the split needs the
       term's first conversion (measured: as the third it never splits). *)
    let s' = S.build d in
    let r1 = C.convert s in
    Gc.full_major ();
    let r2 = C.convert s' in
    note 3 (r1 == r2) d;
    let safe f = try f () with e -> "raised " ^ Printexc.to_string e in
    note 0 (safe (fun () -> D.show (C.convert s)) = D.show t) d;
    note 1 (safe (fun () -> S.show (C.revert t)) = S.show s) d;
    note 2 (safe (fun () -> S.show (C.revert (C.convert s))) = S.show s) d;
    ignore (Sys.opaque_identity (s', r1, r2))
  done;
  List.iteri (fun k name ->
      Printf.printf "%-36s %d of %d\n" name ok.(k) n;
      match first.(k) with
      | None -> ()
      | Some d -> Printf.printf "  first that does not: %s\n" (S.show (S.build d))) names
