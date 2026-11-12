(* Proof_term_boot, the conversion between a proof and its term form,
   for the node and attribute kinds test_proof_convert's random proofs
   (idT, cutT, nthAssumT, wrapT with an int) never build.  The 2026-11-11
   reach census found 153 of its 376 points reached by neither the proof
   census nor a unit test.
   Part 1: real proofs, one refinement each, by tactics that attach every
   attribute kind (with*T on a subgoal, add*T on the goal) and by
   composite tactics.  For each, the line prints the term's node and
   argument kinds in preorder and the round trips test_proof_convert
   checks: through Term_io (alpha-equal to the term), and through the
   term -> raw direction, which squashes (compared with the squashed
   proof); with the status and node count before and after.
   Part 2: hand-edited proof terms read back (term -> raw -> term): the
   rule status replaced by each status term, an address argument with
   each address kind, and a node or argument of a kind the reader does
   not know.  Each prints the status read, the argument kinds, or the
   exception.  Pinned as it reads today, including: the rule status in
   the term is not read (any status term, even an unknown one, reads
   back "incomplete"), and an address argument is accepted and then
   dropped (a tactic_arg's attributes have no address kind). *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Tactic_boot
open Proof_boot
open Proof_convert
open Tacticals_boot.Tacticals

let at n = mk_simple_term (Opname.make_opname [ n ]) []
let parse _ = raise (Invalid_argument "test_proof_term_kinds: parse")
let eval _ = raise (Invalid_argument "test_proof_term_kinds: eval")
let ex name = MLast.ExLid (Ploc.dummy, Ploc.VaVal name)
let aeq = TermSubst.alpha_equal
let st = function Proof.StatusBad -> "bad" | Proof.StatusIncomplete -> "incomplete" | Proof.StatusPartial -> "partial" | Proof.StatusComplete -> "complete"
let mk_int_term o i = mk_term (mk_op o [ make_param (Term_sig.Number (Lm_num.num_of_int i)) ]) []
let mk_str_term o v = mk_term (mk_op o [ make_param (Term_sig.String v) ]) []
let nc (a, b) = Printf.sprintf "%d/%d" a b

(* The Summary node and argument operators of a proof term, in preorder. *)
let kinds t =
  let acc = ref [] in
  let rec go t =
    if not (is_var_term t) then begin
      let o = opname_of_term t in
      (match Opname.dest_opname o with
       | n :: _ when String.length n > 4 && (String.sub n 0 4 = "ext_" || String.sub n 0 4 = "arg_" || (String.length n > 7 && String.sub n 0 7 = "status_")) ->
           acc := n :: !acc
       | _ -> ());
      List.iter (fun bt -> go (dest_bterm bt).bterm) (dest_term t).term_terms
    end
  in
  go t; String.concat " " (List.rev !acc)

let goal_arg () =
  let base = TacticInternal.debug_arg Mp_resource.empty_bookmark (at "A") in
  { base with TacticInternalType.ref_goal = Refine.mk_msequent (at "A") [ at "A" ] }

let to_t io = Convert.to_term () "p" (Convert.of_raw () "p" io)
let back t = Convert.to_raw () "p" (Convert.of_term () "p" t)

let real name tac =
  match Proof.refine (fun x -> x) (Proof.create (goal_arg ())) [] name (ex name) tac with
  | exception e -> Printf.printf "%-34s refine raised %s\n" name (Printexc.to_string e); at "none"
  | p ->
      let io = Proof.io_proof_of_proof false parse eval p and sq = Proof.io_proof_of_proof true parse eval p in
      let t = to_t io and ts = to_t sq in
      let b = back t in
      Printf.printf "%-34s %s\n   %s | status %s, after the term trip %s | nodes %s, after %s, squashed %s\n" name (kinds t)
        (String.concat ", " (List.map (fun (k, ok) -> k ^ (if ok then " ok" else " DIFFERS")) [
           "via term_io", aeq t (Convert.to_term () "p" (Convert.of_term_io () "p" (Convert.to_term_io () "p" (Convert.of_raw () "p" io))));
           "via term -> raw vs squashed", aeq ts (to_t b) ]))
        (st (Proof.status p [])) (st (Proof.status_of_io_proof b))
        (nc (Proof.node_count p)) (nc (Proof.node_count_of_io_proof b)) (nc (Proof.node_count_of_io_proof sq));
      t

let () =
  let b = at "B" and c = at "C" in
  print_endline "== part 1: real proofs";
  List.iter (fun (n, tac) -> ignore (real n tac)) [
    "withTermT w B (cutT B)", TacticInternal.withTermT "w" b (cutT b);
    "withTypeT w B (cutT B)", TacticInternal.withTypeT "w" b (cutT b);
    "withBoolT w true (cutT B)", TacticInternal.withBoolT "w" true (cutT b);
    "withIntT w 3 (cutT B)", TacticInternal.withIntT "w" 3 (cutT b);
    "withStringT w s (cutT B)", TacticInternal.withStringT "w" "s" (cutT b);
    "withTermListT w [B; C] (cutT B)", TacticInternal.withTermListT "w" [ b; c ] (cutT b);
    "addTermT w B", TacticInternal.addTermT "w" b;
    "addTypeT w B", TacticInternal.addTypeT "w" b;
    "addBoolT w false", TacticInternal.addBoolT "w" false;
    "addIntT w 3", TacticInternal.addIntT "w" 3;
    "addStringT w s", TacticInternal.addStringT "w" "s";
    "addTermListT w [B; C]", TacticInternal.addTermListT "w" [ b; c ];
    "cutT B thenT idT", prefix_thenT (cutT b) idT;
    "cutT B thenLT [idT; nthAssumT 1]", prefix_thenLT (cutT b) [ idT; nthAssumT 1 ];
    "nthAssumT 1 (complete)", nthAssumT 1;
    "withIntT k 3 (cutT B thenT addIntT j 4)", TacticInternal.withIntT "k" 3 (prefix_thenT (cutT b) (TacticInternal.addIntT "j" 4));
  ];
  (* Part 2: edit the term of a proof with a status and an argument list, and read it back. *)
  print_endline "== part 2: hand-edited proof terms, read back (term -> raw -> term)";
  let base = real "(base) addIntT w 3" (TacticInternal.addIntT "w" 3) in
  let sibling o n = match Opname.dest_opname o with _ :: rest -> Opname.make_opname (n :: rest) | [] -> o in
  let rec map_ops f t =
    if is_var_term t then t
    else
      let d = dest_term t in
      let t' = mk_term d.term_op (List.map (fun bt -> let db = dest_bterm bt in mk_bterm db.bvars (map_ops f db.bterm)) d.term_terms) in
      f t'
  in
  let named n t = (match Opname.dest_opname (opname_of_term t) with x :: _ -> x = n | [] -> false) in
  let read name t =
    Printf.printf "%-34s %s\n" name
      (try let b = back t in let t2 = to_t b in Printf.sprintf "status %s | %s" (st (Proof.status_of_io_proof b)) (kinds t2)
       with RefineError.RefineError (where, _) -> "refused (" ^ where ^ ")" | e -> "raised " ^ Printexc.to_string e)
  in
  let status_op = ref None and int_arg = ref None in
  ignore (map_ops (fun t -> if named "status_incomplete" t then status_op := Some (opname_of_term t);
                    if named "arg_int" t then int_arg := Some t; t) base);
  (match !status_op with
   | None -> print_endline "no status_incomplete in the base term"
   | Some so ->
       List.iter (fun n -> read ("status replaced by " ^ n) (map_ops (fun t -> if named "status_incomplete" t then mk_simple_term (sibling so n) [] else t) base))
         [ "status_bad"; "status_partial"; "status_complete"; "status_unknown" ]);
  (match !int_arg with
   | None -> print_endline "no arg_int in the base term"
   | Some ia ->
       let ao = opname_of_term ia in
       let addr k i = if i < 0 then mk_simple_term (sibling ao k) [] else mk_int_term (sibling ao k) i in
       let xlist l = mk_xlist_term l in
       let with_arg a = map_ops (fun t -> if named "arg_int" t then a else t) base in
       read "arg_int -> arg_address [subterm 2; arg; clause 1]"
         (with_arg (mk_simple_term (sibling ao "arg_address") [ xlist [ addr "addr_subterm" 2; addr "addr_arg" (-1); addr "addr_clause" 1 ] ]));
       read "arg_int -> arg_address [an unknown address]" (with_arg (mk_simple_term (sibling ao "arg_address") [ xlist [ addr "addr_other" 1 ] ]));
       read "arg_int -> arg_type{B}" (with_arg (mk_simple_term (sibling ao "arg_type") [ b ]));
       read "arg_int -> arg_term_list[B; C]" (with_arg (mk_simple_term (sibling ao "arg_term_list") [ xlist [ b; c ] ]));
       read "arg_int -> arg_bool \"true\"" (with_arg (mk_str_term (sibling ao "arg_bool") "true"));
       read "arg_int -> arg_unknown{B}" (with_arg (mk_simple_term (sibling ao "arg_unknown") [ b ]));
       read "arg_named -> a plain term" (map_ops (fun t -> if named "arg_named" t then b else t) base));
  read "ext_annotate -> ext_unknown" (map_ops (fun t -> if named "ext_annotate" t then mk_simple_term (sibling (opname_of_term t) "ext_unknown") (List.map (fun bt -> (dest_bterm bt).bterm) (dest_term t).term_terms) else t) base);
  read "tactic_arg -> a plain term" (map_ops (fun t -> if named "tactic_arg" t then b else t) base)
