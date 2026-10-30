(* TermMan's sequent operations in metaprl's two term implementations,
   term_std and term_ds, and a model where one is cheap.  The terms are
   test_term_differential's (the same generator, so the same sequents),
   with a sequent forced at the top; for each top-level sequent it
   compares
     - num_hyps, declared_vars, and get_decl_number of each declared
       variable, with the model (the hypothesis list of the description:
       a context is not a declaration, and positions count contexts);
     - nth_hyp and nth_binding at each position, with the model (both
       raise at a context, as term_man_sig says);
     - hyps, concl, args, and get_hyp_number of each hypothesis's type;
     - replace_concl by c, and explode_sequent_and_rename against the
       sequent's own names, up to the names of bound variables;
     - all_vars, and all_vars less H and S (the names that occur only in
       contexts lists <|H;S|>), all_contexts, all_meta_variables, both sets of
       context_vars, so_vars_info, context_vars_info, is_fo_term.
   It prints, per check, how many sequents agree std = ds, std = model and
   ds = model (a dash where there is no model), and the first difference.
   Found, and recorded rather than changed here:
     - declared_vars lists the hypotheses newest first in both (a 2017
       comment in term_man_ds asks whether that is a mistake);
     - get_hyp_number of a type that two hypotheses share: term_std
       answers the first, term_ds the last;
     - all_vars ("all vars in the term, even the bound ones",
       term_man_sig): term_std leaves out the names in contexts lists,
       which term_ds includes; term_ds leaves out the variables a bound
       term binds (lam x0. ...), which term_std includes;
     - is_fo_term of a sequent: term_std true, term_ds false.
   The generator is a fixed linear congruential sequence, not Random. *)
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
  let table f t = String.concat " " (List.sort Stdlib.compare (SymbolTable.fold (fun acc k v -> (string_of_symbol k ^ "=" ^ f v) :: acc) [] t))
  let names_of hs = List.map (function Hyp (v, _) -> v | Ctx (k, _, _) -> k) hs

  (* (name, implementation's answer, model's answer if there is one) *)
  let checks d =
    let a, hs, c = match d with Seq (a, hs, c) -> a, hs, c | _ -> assert false in
    ignore a;
    let t = build d in
    let n = List.length hs in
    let positions = List.init n (fun i -> i + 1) in
    let each f = String.concat " | " (List.map (fun i -> safe (fun () -> f i)) positions) in
    let names = names_of hs in
    (* declarations are hypotheses only; positions count contexts too *)
    let decls = List.concat (List.mapi (fun i h -> match h with Hyp (v, _) -> [ v, i + 1 ] | Ctx _ -> []) hs) in
    [ "num_hyps", safe (fun () -> string_of_int (num_hyps t)), Some (string_of_int n);
      "declared_vars", safe (fun () -> String.concat " " (List.map string_of_symbol (declared_vars t))), Some (String.concat " " (List.map fst decls));
      "get_decl_number", safe (fun () -> String.concat " " (List.map (fun (v, _) -> string_of_int (get_decl_number t (add v))) decls)),
        Some (String.concat " " (List.map (fun (_, i) -> string_of_int i) decls));
      "nth_hyp", each (fun i -> show (nth_hyp t i)),
        Some (String.concat " | " (List.map (function Hyp (_, h) -> safe (fun () -> show (build h)) | Ctx _ -> "(raises)") hs));
      "nth_binding", each (fun i -> string_of_symbol (nth_binding t i)),
        Some (String.concat " | " (List.map (function Hyp (v, _) -> v | Ctx _ -> "(raises)") hs));
      "hyps", safe (fun () -> String.concat " | " (List.map show (hyps t))), None;
      "concl", safe (fun () -> show (concl t)), Some (safe (fun () -> show (build c)));
      "args", safe (fun () -> show (args t)), None;
      "get_hyp_number", each (fun i -> string_of_int (get_hyp_number t (nth_hyp t i))), None;
      "replace_concl by c", safe (fun () -> cshow [] (replace_concl t (build (Op ("c", []))))), None;
      "explode_sequent_and_rename", safe (fun () ->
          let s = explode_sequent_and_rename t (SymbolSet.of_list (List.map add names)) in
          cshow [] (mk_sequent_term s)), None;
      "all_vars", safe (fun () -> syms (all_vars t)), None;
      "all_vars without H, S", safe (fun () ->
          syms (SymbolSet.remove (SymbolSet.remove (all_vars t) (add "H")) (add "S"))), None;
      "all_contexts", safe (fun () -> syms (all_contexts t)), None;
      "all_meta_variables", safe (fun () -> syms (all_meta_variables t)), None;
      "context_vars", safe (fun () -> let a, b = context_vars t in syms a ^ " / " ^ syms b), None;
      "so_vars_info", safe (fun () -> table (fun (x, y) -> Printf.sprintf "%d,%d" x y) (so_vars_info SymbolTable.empty t)), None;
      "context_vars_info", safe (fun () -> table (fun (b, x, y) -> Printf.sprintf "%b,%d,%d" b x y) (context_vars_info SymbolTable.empty t)), None;
      "is_fo_term", safe (fun () -> string_of_bool (is_fo_term t)), None ]
end

module Std = Check (Refiner_std.Refiner)
module Ds = Check (Refiner_ds.Refiner)

(* A sequent at the top, with hypotheses drawn as gen draws them. *)
let rec gen_seq () =
  match gen 4 [] 0 with
  | Seq _ as d -> d
  | _ -> gen_seq ()

let () =
  let n = 1000 in
  let first = ref [] and counts = Hashtbl.create 32 and order = ref [] in
  let ctxs = ref 0 and hyps = ref 0 in
  for i = 1 to n do
    let d = gen_seq () in
    (match d with Seq (_, hs, _) -> List.iter (function Hyp _ -> incr hyps | Ctx _ -> incr ctxs) hs | _ -> ());
    List.iter2 (fun (name, s, m) (_, t, _) ->
        if not (List.mem name !order) then order := name :: !order;
        let a, b, c = try Hashtbl.find counts name with Not_found -> 0, 0, 0 in
        let ok x y = x = y in
        let a = if ok s t then a + 1 else a in
        let b, c = match m with
          | None -> -1, -1
          | Some m -> (if ok s m then b + 1 else b), (if ok t m then c + 1 else c) in
        Hashtbl.replace counts name (a, b, c);
        let note what x y = if x <> y && not (List.mem_assoc (name, what) !first) then first := ((name, what), (i, x, y)) :: !first in
        note "std vs ds" s t;
        Option.iter (fun m -> note "std vs model" s m; note "ds vs model" t m) m)
      (Std.checks d) (Ds.checks d)
  done;
  Printf.printf "%d sequents: %d hypotheses, %d context hypotheses\n" n !hyps !ctxs;
  Printf.printf "%-28s %6s %6s %6s\n" "check" "std=ds" "std=m" "ds=m";
  List.iter (fun name ->
      let a, b, c = Hashtbl.find counts name in
      let f x = if x < 0 then "-" else string_of_int x in
      Printf.printf "%-28s %6d %6s %6s\n" name a (f b) (f c);
      List.iter (fun what -> match List.assoc_opt (name, what) !first with
          | None -> ()
          | Some (i, x, y) -> Printf.printf "  first difference (%s), sequent %d:\n    %s\n    %s\n" what i x y)
        [ "std vs ds"; "std vs model"; "ds vs model" ])
    (List.rev !order)
