(* TermAddr.find_subterm returns the addresses of the subterms satisfying a
   predicate; the reduce resource (support/tactics/top_conversionals.ml)
   uses it to reduce, before a rewrite, the subterms the contractum copies,
   and wraps each address in an address conversion.  Every address it
   returns must therefore be one that TermAddr.term_subterm accepts.

   Under TERMS = std, itt_vec_sequent_term's reduce_hyps_flatten_length
   failed: reduceC raised make_index at an address find_subterm had
   returned, and the whole reduction fell back to the identity.  This test
   builds that term in both implementations,
     hyps_length{ sequent[mk_vbind]{ x: A<|S|>; <T<|S|>['x]>
                    >- mk_core{ sequent[hypconslist]{ <K1<|S; T|>['x]> >- l<|H|> } } } }
   asks each for the addresses of its variables and second-order
   variables, and prints what term_subterm makes of each one.

   The reduce resource takes these addresses on a rule's REDEX and applies
   them to its instances, so they must not depend on how many hypotheses a
   context stands for.  The second half takes the addresses on the redex
   of reduce_hyps_length_bind_squashlist,
     hyps_length{ sequent[mk_vbind]{ <J> >- mk_core{ sequent[hypconslist]{ <K> >- l } } } }
   and resolves each on the instance above, where <J> is x: A; <T>. *)
open Lm_symbol
open Term_sig

module Check (R : Refiner_sig.RefinerSig) = struct
  open R.Term
  open R.TermMan
  let op s = Opname.make_opname [ s ]
  let v = add
  let seq arg hyps concl =
    mk_sequent_term
      { sequent_args = mk_simple_term (op arg) [];
        sequent_hyps = R.Term.SeqHyp.of_list hyps;
        sequent_concl = concl }
  let term =
    let x = mk_var_term (v "x") in
    let a = mk_so_var_term (v "A") [ v "S" ] [] in
    let l = mk_so_var_term (v "l") [ v "H" ] [] in
    let inner = seq "hypconslist" [ Context (v "K1", [ v "S"; v "T" ], [ x ]) ] l in
    let outer = seq "mk_vbind" [ Hypothesis (v "x", a); Context (v "T", [ v "S" ], [ x ]) ]
        (mk_simple_term (op "mk_core") [ inner ]) in
    mk_simple_term (op "hyps_length") [ outer ]
  let redex =
    let l = mk_so_var_term (v "l") [] [] in
    let inner = seq "hypconslist" [ Context (v "K", [], []) ] l in
    let outer = seq "mk_vbind" [ Context (v "J", [], []) ] (mk_simple_term (op "mk_core") [ inner ]) in
    mk_simple_term (op "hyps_length") [ outer ]
  let kind t =
    if is_so_var_term t then (let w, _, _ = dest_so_var t in "second-order variable " ^ string_of_symbol w)
    else if is_var_term t then "variable " ^ string_of_symbol (dest_var t)
    else "something else"
  let report name =
    let addrs = R.TermAddr.find_subterm term (fun t _ -> is_var_term t || is_so_var_term t) in
    let refused = ref 0 in
    let found = List.map (fun a ->
        match R.TermAddr.term_subterm term a with
        | t -> kind t
        | exception _ -> incr refused; "REFUSED by term_subterm") addrs in
    Printf.printf "%s: find_subterm returned %d addresses, term_subterm refused %d\n"
      name (List.length addrs) !refused;
    List.iter (fun s -> Printf.printf "  %s\n" s) found;
    List.filter (fun s -> s <> "REFUSED by term_subterm") found
  let report_redex name =
    let addrs = R.TermAddr.find_subterm redex (fun t _ -> is_so_var_term t) in
    Printf.printf "%s: on the redex, find_subterm returned %d addresses\n" name (List.length addrs);
    List.map (fun a ->
        let on_redex = (try kind (R.TermAddr.term_subterm redex a) with _ -> "REFUSED") in
        let on_instance = (try kind (R.TermAddr.term_subterm term a) with _ -> "REFUSED") in
        Printf.printf "  %s on the redex, %s on the instance\n" on_redex on_instance;
        on_redex ^ " / " ^ on_instance) addrs
end

module Std = Check (Refiner_std.Refiner)
module Ds = Check (Refiner_ds.Refiner)

let () =
  let s = Std.report "std" in
  let d = Ds.report "ds" in
  Printf.printf "the accepted subterms %s\n" (if s = d then "agree" else "DIFFER");
  let s = Std.report_redex "std" in
  let d = Ds.report_redex "ds" in
  Printf.printf "on the redex and its instance they %s\n" (if s = d then "agree" else "DIFFER")
