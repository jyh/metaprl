(* Rewrite rules whose contractum carries parameters (refiner/rewrite:
   compile_so_contractum_param, build_contractum_params; the unit tests
   reached neither, 2026-11-02 profile).  Each rule is compiled with
   term_rewrite in term_std and term_ds and applied, with apply_rewrite, to
   300 instances of its redex and 300 near misses; the contractum is
   compared with a model (first-order matching, then instantiation) in
   both implementations.  The rules move a number, a string and a token
   parameter, swap two, put a constant parameter in the contractum, and
   require a repeated parameter variable to match equal values.  A rule
   whose contractum names a parameter variable the redex does not bind
   must not compile.  The generator is a fixed linear congruential
   sequence, not Random. *)

open Term_sig

let state = ref 4242
let next () = state := (!state * 1103515245 + 12345) land 0x7fffffff; !state lsr 8
let pick n = next () mod n

type prm = N of int | MN of string | S of string | MS of string | K of string | MK of string
type desc = V of string | T of string * prm list * desc list

let show_prm = function
  | N i -> string_of_int i ^ ":n"
  | MN v -> v ^ ":n" | S s -> "\"" ^ s ^ "\":s" | MS v -> v ^ ":s" | K t -> t ^ ":t" | MK v -> v ^ ":t"
let rec show = function
  | V v -> "'" ^ v
  | T (o, ps, ts) ->
      o ^ (if ps = [] then "" else "[" ^ String.concat ", " (List.map show_prm ps) ^ "]")
      ^ (if ts = [] then "" else "{" ^ String.concat "; " (List.map show ts) ^ "}")

(* The model: match, then instantiate.  Variables of either kind bind once. *)
type v = D of desc | P of prm
let rec mt s p t =
  let bind s k x = match List.assoc_opt k s with None -> Some ((k, x) :: s) | Some y -> if y = x then Some s else None in
  match p, t with
  | V v, _ -> bind s v (D t)
  | T (o, ps, ts), T (o', ps', ts') when o = o' && List.length ps = List.length ps' && List.length ts = List.length ts' ->
      let rec params s = function
        | [], [] -> Some s
        | MN v :: a, (N _ as x) :: b | MS v :: a, (S _ as x) :: b | MK v :: a, (K _ as x) :: b ->
            (match bind s v (P x) with None -> None | Some s -> params s (a, b))
        | x :: a, y :: b when x = y -> params s (a, b)
        | _ -> None in
      (match params s (ps, ps') with
       | None -> None
       | Some s -> List.fold_left2 (fun s a b -> match s with None -> None | Some s -> mt s a b) (Some s) ts ts')
  | _ -> None
let rec inst s = function
  | V v -> (match List.assoc v s with D d -> d | P _ -> failwith "inst")
  | T (o, ps, ts) ->
      T (o, List.map (function MN v | MS v | MK v -> (match List.assoc v s with P p -> p | D _ -> failwith "inst") | p -> p) ps,
         List.map (inst s) ts)

module Rw (R : Refiner_sig.RefinerSig) = struct
  open R.Term
  open R.TermMan
  let op s = Opname.make_opname [ s ]
  let mk_prm = function
    | N i -> make_param (Term_sig.Number (Lm_num.num_of_int i))
    | MN v -> make_param (Term_sig.MNumber (Lm_symbol.add v))
    | S s -> make_param (Term_sig.String s)
    | MS v -> make_param (Term_sig.MString (Lm_symbol.add v))
    | K t -> make_param (Term_sig.Token (op t))
    | MK v -> make_param (Term_sig.MToken (Lm_symbol.add v))
  let rec build = function
    | V v -> mk_so_var_term (Lm_symbol.add v) [] []
    | T (o, ps, ts) -> mk_term (mk_op (op o) (List.map mk_prm ps)) (List.map (fun t -> mk_simple_bterm (build t)) ts)
  let show_param p =
    match dest_param p with
    | Term_sig.Number n -> Lm_num.string_of_num n ^ ":n"
    | Term_sig.String s -> "\"" ^ s ^ "\":s"
    | Term_sig.Token t -> String.concat "!" (Opname.dest_opname t) ^ ":t"
    | Term_sig.MNumber v -> Lm_symbol.string_of_symbol v ^ ":n"
    | Term_sig.MString v -> Lm_symbol.string_of_symbol v ^ ":s"
    | Term_sig.MToken v -> Lm_symbol.string_of_symbol v ^ ":t"
    | _ -> "?param"
  let rec show_term t =
    if is_so_var_term t then let v, _, _ = dest_so_var t in "'" ^ Lm_symbol.string_of_symbol v
    else
      let { term_op; term_terms } = dest_term t in
      let { op_name; op_params } = dest_op term_op in
      String.concat "!" (Opname.dest_opname op_name)
      ^ (if op_params = [] then "" else "[" ^ String.concat ", " (List.map show_param op_params) ^ "]")
      ^ (if term_terms = [] then "" else "{" ^ String.concat "; " (List.map (fun b -> show_term (dest_bterm b).bterm) term_terms) ^ "}")
  let rewrite redex contractum =
    try Ok (R.Rewrite.term_rewrite Rewrite_sig.Strict R.Rewrite.empty_args_spec [ build redex ] [ build contractum ])
    with e -> Error (Printexc.to_string e)
  let apply rw d =
    match rw with
    | Error _ -> "(rule does not compile)"
    | Ok rw -> (try String.concat " | " (List.map show_term (R.Rewrite.apply_rewrite rw R.Rewrite.empty_args (build d) [])) with _ -> "(refused)")
end

module Std = Rw (Refiner_std.Refiner)
module Ds = Rw (Refiner_ds.Refiner)

let leaf () = if pick 2 = 0 then T ("c", [], []) else T ("g", [], [ T ("c", [], []) ])
let num () = N (pick 4)
let str () = S [| "x"; "y"; "zz" |].(pick 3)
let tok () = K [| "ta"; "tb" |].(pick 2)

(* name, redex, contractum, an instance, a near miss *)
let rules = [
  "h[n:n]{'a} --> k[n:n]{'a}",
  T ("h", [ MN "n" ], [ V "a" ]), T ("k", [ MN "n" ], [ V "a" ]),
  (fun () -> T ("h", [ num () ], [ leaf () ])),
  (fun () -> if pick 2 = 0 then T ("k", [ num () ], [ leaf () ]) else T ("h", [ str () ], [ leaf () ]));

  "p[n:n, x:s]{'a; 'b} --> q[x:s, n:n]{'b; 'a}",
  T ("p", [ MN "n"; MS "x" ], [ V "a"; V "b" ]), T ("q", [ MS "x"; MN "n" ], [ V "b"; V "a" ]),
  (fun () -> T ("p", [ num (); str () ], [ leaf (); leaf () ])),
  (fun () -> T ("p", [ str (); num () ], [ leaf (); leaf () ]));

  "tk[t:t]{'a} --> tk2[t:t, 7:n]{'a}",
  T ("tk", [ MK "t" ], [ V "a" ]), T ("tk2", [ MK "t"; N 7 ], [ V "a" ]),
  (fun () -> T ("tk", [ tok () ], [ leaf () ])),
  (fun () -> T ("tk", [ num () ], [ leaf () ]));

  "e{'a} --> h[5:n, \"five\":s]{'a}",
  T ("e", [], [ V "a" ]), T ("h", [ N 5; S "five" ], [ V "a" ]),
  (fun () -> T ("e", [], [ leaf () ])),
  (fun () -> T ("e2", [], [ leaf () ]));

  "h[n:n]{h[n:n]{'a}} --> m[n:n]{'a}",
  T ("h", [ MN "n" ], [ T ("h", [ MN "n" ], [ V "a" ]) ]), T ("m", [ MN "n" ], [ V "a" ]),
  (fun () -> let n = num () in T ("h", [ n ], [ T ("h", [ n ], [ leaf () ]) ])),
  (fun () -> T ("h", [ num () ], [ T ("h", [ num () ], [ leaf () ]) ]));
]

let () =
  let n = 300 in
  List.iter (fun (name, redex, contractum, instance, miss) ->
      let s_rw = Std.rewrite redex contractum and d_rw = Ds.rewrite redex contractum in
      Printf.printf "%s\n" name;
      let status = function Ok _ -> "compiles" | Error e -> "DOES NOT COMPILE: " ^ e in
      Printf.printf "  std %s; ds %s\n" (status s_rw) (status d_rw);
      let run what mk =
        let agree = ref 0 and applied = ref 0 and first = ref None in
        for _ = 1 to n do
          let d = mk () in
          let want = match mt [] redex d with None -> "(refused)" | Some s -> show (inst s contractum) in
          let s = Std.apply s_rw d and t = Ds.apply d_rw d in
          if want <> "(refused)" then incr applied;
          if s = want && t = want then incr agree
          else if !first = None then first := Some (show d, want, s, t)
        done;
        Printf.printf "  %-14s %d of %d agree with the model (it rewrites %d)\n" what !agree n !applied;
        match !first with
        | None -> ()
        | Some (d, w, s, t) -> Printf.printf "    first difference, %s:\n      model %s\n      std   %s\n      ds    %s\n" d w s t
      in
      run "instances" instance;
      run "near misses" miss)
    rules;
  (* A contractum parameter variable the redex does not bind. *)
  let bad = T ("h", [ MN "n" ], [ V "a" ]), T ("h", [ MN "m" ], [ V "a" ]) in
  let refuses = function Ok _ -> "COMPILES" | Error _ -> "refused" in
  Printf.printf "h[n:n]{'a} --> h[m:n]{'a} (m unbound): std %s, ds %s\n"
    (refuses (Std.rewrite (fst bad) (snd bad))) (refuses (Ds.rewrite (fst bad) (snd bad)))
