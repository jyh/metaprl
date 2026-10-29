(* The rewriter (refiner/rewrite) is shared by term_std and term_ds and
   runs over each implementation's terms.  This test compiles the same
   rewrite rules in both implementations (each must compile in both), applies each to 400 instances of
   its redex (built from pseudo-random subterms) and to 400 pseudo-random
   terms, and compares the contracta, or that both refuse.  The rules
   cover an operator, a binder with a second-order body, a sequent with
   contexts and a hypothesis, and the hyps_length rule whose redex led to
   #58.  The generator is a fixed linear congruential sequence, so the
   terms are the same on every OCaml. *)
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

module Rw (R : Refiner_sig.RefinerSig) = struct
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

  let rewrite redex contractum =
    try Ok (R.Rewrite.term_rewrite Rewrite_sig.Strict R.Rewrite.empty_args_spec [ build redex ] [ build contractum ])
    with e -> Error (Printexc.to_string e)
  let apply rw d =
    match rw with
    | Error _ -> "(rule does not compile)"
    | Ok rw ->
        (try String.concat " | " (List.map show (R.Rewrite.apply_rewrite rw R.Rewrite.empty_args (build d) []))
         with _ -> "(refused)")
end

module Std = Rw (Refiner_std.Refiner)
module Ds = Rw (Refiner_ds.Refiner)

let mv v = SOVar (v, [], [])
let rand_hyps prefix env =
  let rec go i env acc =
    if i = 0 then List.rev acc, env
    else if pick 3 = 0 then
      let k = Printf.sprintf "%sK%d" prefix i in go (i - 1) (k :: env) (Ctx (k, [], List.init (pick 2) (fun _ -> gen 1 env 0)) :: acc)
    else
      let v = Printf.sprintf "%sv%d" prefix i in go (i - 1) (v :: env) (Hyp (v, gen 1 env 0) :: acc)
  in
  go (pick 3) env []

(* name, redex, contractum, an instance of the redex *)
let rules = [
  "f{'a; 'b} --> f{'b; 'a}",
  Op ("f", [ mv "a"; mv "b" ]), Op ("f", [ mv "b"; mv "a" ]),
  (fun () -> Op ("f", [ gen 3 [] 0; gen 3 [] 0 ]));

  "app{lam{x. 'b['x]}; 'a} --> 'b['a]",
  Op ("app", [ Bind ("x", SOVar ("b", [], [ Var "x" ])); mv "a" ]), SOVar ("b", [], [ mv "a" ]),
  (fun () -> Op ("app", [ Bind ("y", gen 3 [ "y" ] 0); gen 3 [] 0 ]));

  "sequent[sa]{ <J>; x: 'A<|J|> >- 'C<|J|>['x] } --> sequent[sb]{ same }",
  Seq ("sa", [ Ctx ("J", [], []); Hyp ("x", SOVar ("A", [ "J" ], [])) ], SOVar ("C", [ "J" ], [ Var "x" ])),
  Seq ("sb", [ Ctx ("J", [], []); Hyp ("x", SOVar ("A", [ "J" ], [])) ], SOVar ("C", [ "J" ], [ Var "x" ])),
  (fun () ->
     let j, env = rand_hyps "j" [] in
     Seq ("sa", j @ [ Hyp ("y", gen 2 env 0) ], gen 2 ("y" :: env) 0));

  "hyps_length{mk_vbind{<J> >- mk_core{hypconslist{<K> >- 'l}}}} --> ...squashlist...",
  Op ("hyps_length", [ Seq ("mk_vbind", [ Ctx ("J", [], []) ], Op ("mk_core", [ Seq ("hypconslist", [ Ctx ("K", [], []) ], mv "l") ])) ]),
  Op ("hyps_length", [ Seq ("mk_vbind", [ Ctx ("J", [], []) ], Op ("mk_core", [ Seq ("squashlist", [ Ctx ("K", [], []) ], mv "l") ])) ]),
  (fun () ->
     let j, _ = rand_hyps "j" [] in
     let k, _ = rand_hyps "k" [] in
     Op ("hyps_length", [ Seq ("mk_vbind", j, Op ("mk_core", [ Seq ("hypconslist", k, gen 2 [] 0) ])) ]));
]

let () =
  let n = 400 in
  List.iter (fun (name, redex, contractum, instance) ->
      let s_rw = Std.rewrite redex contractum and d_rw = Ds.rewrite redex contractum in
      let run what mk =
        let agree = ref 0 and applied = ref 0 and first = ref None in
        for i = 1 to n do
          let d = mk () in
          let s = Std.apply s_rw d and t = Ds.apply d_rw d in
          if t <> "(refused)" && t <> "(rule does not compile)" then incr applied;
          if s = t then incr agree else if !first = None then first := Some (i, s, t)
        done;
        Printf.printf "  %-22s %d of %d agree (term_ds rewrote %d)\n" what !agree n !applied;
        match !first with
        | None -> ()
        | Some (i, s, t) -> Printf.printf "    first difference, %d:\n      std %s\n      ds  %s\n" i s t
      in
      Printf.printf "%s\n" name;
      let status = function Ok _ -> "compiles" | Error e -> "DOES NOT COMPILE: " ^ e in
      Printf.printf "  std %s; ds %s\n" (status s_rw) (status d_rw);
      (match s_rw, d_rw with Ok _, Ok _ -> () | _ -> Printf.printf "  FAIL: the rule must compile in both, or this check tests nothing\n");
      run "instances of the redex" instance;
      run "random terms" (fun () -> gen 4 [] 0))
    rules
