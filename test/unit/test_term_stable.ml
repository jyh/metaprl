(* Term_stable (refiner/reflib) is a table keyed by a term's shape:
   itt_squash's unsquash resource and kat's support_algebra look terms up
   in it.  Its table is reached through stable_resource_info's Imperative
   record.  This test inserts 300 generated terms (value i for the i-th)
   and looks up 1,000 generated terms (one in five of a shape never
   inserted), comparing slookup_all and slookup
   with a model: a list of (key, value), where the key is the shape
   computed here from the term's structure:
     - a variable, and a second-order variable with no arguments: "var";
     - a second-order variable with n arguments: "var" and n zeros;
     - a sequent: "sequent";
     - otherwise the opname, the kinds of its parameters and the number of
       binders of each subterm (not the parameters' values, not the
       subterms themselves).
   slookup_all must be the values whose key matches, newest first;
   slookup the newest, or Not_found. *)
open Refiner.Refiner.Term
open Refiner.Refiner.TermType
open Refiner.Refiner.TermMan
open Mp_resource

let state = ref 4242
let next () = state := (!state * 1103515245 + 12345) land 0x7fffffff; !state lsr 8
let pick n = next () mod n

let op s = Opname.make_opname [ s ]

(* A term, and its model key built alongside it. *)
let rec gen depth =
  let leaf () =
    match pick 5 with
    | 0 -> mk_var_term (Lm_symbol.add "z"), "var"
    | 1 -> mk_so_var_term (Lm_symbol.add "A") [] [], "var"
    | 2 -> mk_simple_term (op "c") [], "c||"
    | 3 ->
        let n = pick 3 in
        mk_term (mk_op (op "n") [ make_param (Number (Lm_num.num_of_int n)) ]) [], "n|N|"
    | _ ->
        (* one opname, two parameter kinds: two shapes *)
        if pick 2 = 0 then mk_term (mk_op (op "p") [ make_param (Number (Lm_num.num_of_int 1)) ]) [], "p|N|"
        else mk_term (mk_op (op "p") [ make_param (Token (op "k")) ]) [], "p|T|"
  in
  if depth <= 0 then leaf ()
  else
    match pick 7 with
    | 0 -> leaf ()
    | 1 ->
        let k = 1 + pick 2 in
        let args = List.init k (fun _ -> fst (gen (depth - 1))) in
        mk_so_var_term (Lm_symbol.add "A") [] args, "var" ^ String.make k '0'
    | 2 ->
        let k = 1 + pick 2 in
        let ts = List.init k (fun _ -> fst (gen (depth - 1))) in
        mk_simple_term (op "f") ts, "f||" ^ String.concat "," (List.map (fun _ -> "0") ts)
    | 3 ->
        let b = fst (gen (depth - 1)) in
        mk_term (mk_op (op "lam") []) [ mk_bterm [ Lm_symbol.add "x" ] b ], "lam||1"
    | 4 ->
        let s = if pick 2 = 0 then "a" else "b" in
        mk_term (mk_op (op "t") [ make_param (Token (op s)) ]) [ mk_simple_bterm (fst (gen (depth - 1))) ], "t|T|0"
    | 5 ->
        let b = fst (gen (depth - 1)) in
        mk_term (mk_op (op "lam") []) [ mk_bterm [ Lm_symbol.add "x"; Lm_symbol.add "y" ] b ], "lam||2"
    | _ ->
        let c = fst (gen (depth - 1)) in
        mk_sequent_term
          { sequent_args = mk_simple_term (op "sa") [];
            sequent_hyps = SeqHyp.of_list [ Hypothesis (Lm_symbol.add "v", fst (gen (depth - 1))) ];
            sequent_concl = c }, "sequent"

let () =
  let tbl =
    match Term_stable.stable_resource_info (fun t -> t) with
    | Imperative r ->
        let tbl = r.imp_create () in
        (fun (t, v) -> r.imp_add tbl (t, v)), (fun () -> r.imp_retr tbl)
    | _ -> failwith "stable_resource_info is not Imperative"
  in
  let add, retr = tbl in
  let model = ref [] in
  for i = 1 to 300 do
    let t, k = gen 3 in
    add (t, i);
    model := (k, i) :: !model
  done;
  let table = retr () in
  let keys = List.sort_uniq compare (List.map fst !model) in
  let all_ok = ref 0 and one_ok = ref 0 and hits = ref 0 and first = ref None in
  for _ = 1 to 1000 do
    (* one query in five is a shape never inserted (operator q) *)
    let t, k = if pick 5 = 0 then mk_simple_term (op "q") [ fst (gen 2) ], "q||0" else gen 3 in
    let want = List.filter_map (fun (k', v) -> if k' = k then Some v else None) !model in
    let got = Term_stable.slookup_all table t in
    if want <> [] then incr hits;
    if got = want then incr all_ok
    else if !first = None then first := Some k;
    let got1 = try Some (Term_stable.slookup table t) with Not_found -> None in
    let want1 = match want with v :: _ -> Some v | [] -> None in
    if got1 = want1 then incr one_ok
  done;
  Printf.printf "inserted 300 terms, %d distinct shapes\n" (List.length keys);
  Printf.printf "queries that find a shape            %d of 1000\n" !hits;
  Printf.printf "slookup_all = model (newest first)   %d of 1000\n" !all_ok;
  Printf.printf "slookup = newest or Not_found        %d of 1000\n" !one_ok;
  match !first with
  | None -> ()
  | Some k -> Printf.printf "  first that does not: shape %s\n" k
