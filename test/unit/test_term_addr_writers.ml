(* TermAddr's writers in metaprl's two term implementations, term_std and
   term_ds (the readers, subterm_addresses / term_subterm / find_subterm,
   are in test_term_differential).  On test_term_differential's terms, at
   every address subterm_addresses gives, it compares std with ds, and
   checks a law in each:
     - replace_subterm by c (law: term_subterm of the result at that
       address is c);
     - apply_fun_at_addr wrapping the subterm in w{_} (law: the subterm at
       that address is w{ the old subterm });
     - apply_var_fun_at_addr: the bound variables it passes at that address;
     - apply_fun_higher and apply_var_fun_higher with a function that
       succeeds on variables only: the result, and the values collected
       (with the bound variables passed).
   It prints, per check, how many terms agree std = ds, how many hold the
   law in each (a term with no address, a leaf, is not counted), the first
   difference, and how much the terms exercise: addresses, addresses under
   a binder, variables apply_fun_higher collects.  A mutant that replaces
   at the root on half the terms in std reads 652 std = ds, 344 std law.  The generator is a fixed linear
   congruential sequence, not Random. *)
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

module Check (R : Refiner_sig.RefinerSig) = struct
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

  (* As show, but bound variables print by binding position, so that
     alpha-equivalent terms print the same. *)
  let rec cshow env t =
    let name v = try "#" ^ string_of_int (List.assoc v env) with Not_found -> string_of_symbol v in
    let bind env v = (v, List.length env) :: env in
    if is_sequent_term t then
      let s = explode_sequent t in
      let e = ref env in
      let hs = List.map (function
          | Hypothesis (v, a) -> let a = cshow !e a in e := bind !e v; "#" ^ string_of_int (List.length !e - 1) ^ ": " ^ a
          | Context (v, cs, args) ->
              let r = "<" ^ string_of_symbol v ^ "<|" ^ String.concat ";" (List.map string_of_symbol cs) ^ "|>["
                      ^ String.concat "; " (List.map (cshow !e) args) ^ "]>" in
              e := bind !e v; r)
          (R.Term.SeqHyp.to_list s.sequent_hyps) in
      "sequent[" ^ cshow env s.sequent_args ^ "]{ " ^ String.concat "; " hs ^ " >- " ^ cshow !e s.sequent_concl ^ " }"
    else if is_var_term t then "'" ^ name (dest_var t)
    else if is_so_var_term t then
      let v, cs, args = dest_so_var t in
      string_of_symbol v ^ "<|" ^ String.concat ";" (List.map string_of_symbol cs) ^ "|>["
      ^ String.concat "; " (List.map (cshow env) args) ^ "]"
    else
      let { term_op; term_terms } = dest_term t in
      let opn = String.concat "!" (Opname.dest_opname (dest_op term_op).op_name) in
      if term_terms = [] then opn
      else opn ^ "{" ^ String.concat "; " (List.map (fun b ->
          let { bvars; bterm } = dest_bterm b in
          let env' = List.fold_left bind env bvars in
          (if bvars = [] then "" else String.concat "," (List.map name bvars |> List.map (fun _ -> "_")) ^ ". ") ^ cshow env' bterm)
          term_terms) ^ "}"

  let safe f = try f () with _ -> "(raises)"
  let syms s = String.concat " " (List.sort Stdlib.compare (List.map string_of_symbol (SymbolSet.elements s)))
  let c = mk_simple_term (op "c") []
  let wrap s = mk_simple_term (op "w") [ s ]
  let higher_f s = if is_var_term s then wrap s, string_of_symbol (dest_var s) else raise (Failure "not a var")
  let higher_vf bvs s =
    if is_var_term s then wrap s, string_of_symbol (dest_var s) ^ "<" ^ syms bvs ^ ">" else raise (Failure "not a var")

  (* (name, the result printed, whether the law holds; None = no law) *)
  let checks d =
    let t = build d in
    let addrs = try R.TermAddr.subterm_addresses t with _ -> [] in
    let at f = List.map (fun a -> try f a with _ -> "(raises)", Some false) addrs in
    let join l =
      String.concat " | " (List.map fst l),
      (if List.for_all (fun (_, b) -> b = None) l then None
       else if List.for_all (fun (_, b) -> b <> Some false) l then Some true else Some false) in
    let eq a b = R.TermSubst.alpha_equal a b in
    [ "replace_subterm by c", join (at (fun a ->
          let r = R.TermAddr.replace_subterm t a c in
          cshow [] r, Some (eq (R.TermAddr.term_subterm r a) c)));
      "apply_fun_at_addr w{_}", join (at (fun a ->
          let r = R.TermAddr.apply_fun_at_addr wrap a t in
          cshow [] r, Some (eq (R.TermAddr.term_subterm r a) (wrap (R.TermAddr.term_subterm t a)))));
      "apply_var_fun_at_addr's bvars", join (at (fun a ->
          let seen = ref "" in
          ignore (R.TermAddr.apply_var_fun_at_addr (fun bvs s -> seen := syms bvs; s) a SymbolSet.empty t);
          !seen, None));
      "apply_fun_higher on variables", (safe (fun () ->
          let r, l = R.TermAddr.apply_fun_higher higher_f t in
          cshow [] r ^ " / " ^ String.concat "," l), None);
      "apply_var_fun_higher on variables", (safe (fun () ->
          let r, l = R.TermAddr.apply_var_fun_higher higher_vf SymbolSet.empty t in
          cshow [] r ^ " / " ^ String.concat "," l), None) ]
end

module Std = Check (Refiner_std.Refiner)
module Ds = Check (Refiner_ds.Refiner)

let () =
  let n = 1000 in
  let rows = ref [] in
  let get name = try List.assoc name !rows with Not_found -> let r = ref (0, 0, 0, None) in rows := !rows @ [ name, r ]; r in
  for i = 1 to n do
    let d = gen 4 [] 0 in
    List.iter2 (fun (name, (s, ls)) (_, (t, lt)) ->
        let r = get name in
        let a, b, c, f = !r in
        let law = function Some true -> 1 | _ -> 0 in
        r := (a + (if s = t then 1 else 0)), b + law ls, c + law lt, (if f = None && s <> t then Some (i, s, t) else f))
      (Std.checks d) (Ds.checks d)
  done;
  let nonempty_bvars = ref 0 and addrs = ref 0 and collected = ref 0 in
  state := 12345;
  for _ = 1 to n do
    let d = gen 4 [] 0 in
    let t = Std.build d in
    List.iter (fun a ->
        incr addrs;
        ignore (Refiner_std.Refiner.TermAddr.apply_var_fun_at_addr
                  (fun bvs s -> if not (SymbolSet.is_empty bvs) then incr nonempty_bvars; s) a SymbolSet.empty t))
      (try Refiner_std.Refiner.TermAddr.subterm_addresses t with _ -> []);
    (try collected := !collected + List.length (snd (Refiner_std.Refiner.TermAddr.apply_fun_higher Std.higher_f t)) with _ -> ())
  done;
  Printf.printf "%d terms\n%-36s %6s %8s %8s\n" n "check" "std=ds" "std law" "ds law";
  List.iter (fun (name, r) ->
      let a, b, c, f = !r in
      let lawful = b > 0 || c > 0 in
      Printf.printf "%-36s %6d %8s %8s\n" name a (if lawful then string_of_int b else "-") (if lawful then string_of_int c else "-");
      match f with None -> () | Some (i, s, t) -> Printf.printf "  first difference, term %d:\n    std %s\n    ds  %s\n" i s t)
    !rows;
  Printf.printf "coverage (std): %d addresses, %d with bound variables passed; apply_fun_higher collected %d variables\n"
    !addrs !nonempty_bvars !collected
