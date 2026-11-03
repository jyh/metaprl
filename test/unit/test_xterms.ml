(* The primitive term vocabulary of refiner/term_gen/term_man_gen that no
   unit test reached (2026-11-02): lists (xnil, xcons, xlist), xrewrite,
   xbind, a string with one subterm, first-or-second-order variables, and
   construct_redex.  In term_std and term_ds:
     - on 500 random lists of 0-5 terms, mk_xlist_term gives a list term
       that dest_xlist takes back to the same terms, the same as building it
       from xcons and xnil; dest_xcons undoes mk_xcons_term;
     - is_xlist_term and dest_xlist refuse a cons whose tail is not a list, a
       cons that binds a variable, and xnil with a parameter;
     - mk_xrewrite_term / dest_xrewrite, mk_xbind_term / is_xbind_term and
       mk_xstring_dep0_term / dest_xstring_dep0_term round-trip, and refuse
       the other shapes listed;
     - is_fso_var_term holds for a variable and for a second-order variable
       with contexts and no arguments, and not for one with an argument;
       dest_fso_var gives its name;
     - construct_redex [|v1..vn|] params terms is n xbinds, in order, around
       the list params @ terms.
   The generator is a fixed linear congruential sequence, not Random. *)
let state = ref 6161
let next () = state := (!state * 1103515245 + 12345) land 0x7fffffff; !state lsr 8
let pick n = next () mod n

module S (R : Refiner_sig.RefinerSig) = struct
  open R.Term
  open R.TermMan
  open R.TermSubst
  let op s = Opname.make_opname [ s ]
  let sym = Lm_symbol.add
  let simple s = mk_simple_term (op s) []
  let term_of = function 0 -> simple "c" | 1 -> mk_var_term (sym "x") | _ -> mk_simple_term (op "f") [ simple "d" ]
  let refused f = try ignore (f ()); "gave" with R.RefineError.RefineError _ -> "refused" | e -> "raised " ^ Printexc.to_string e
  let opname_of t = (dest_op (dest_term t).term_op).op_name
  let line name what v = Printf.printf "%-50s %s\n" (name ^ ": " ^ what) v

  let run name lists =
    let lists = List.map (List.map term_of) lists in
    let n = List.length lists in
    let same a b = List.length a = List.length b && List.for_all2 alpha_equal a b in
    let k1 = ref 0 and k2 = ref 0 and k3 = ref 0 in
    List.iter (fun l ->
        let t = mk_xlist_term l in
        if is_xlist_term t && same (dest_xlist t) l then incr k1;
        if alpha_equal t (List.fold_right mk_xcons_term l xnil_term) then incr k2;
        (match l with
         | a :: rest -> let h, tl = dest_xcons t in if alpha_equal h a && same (dest_xlist tl) rest && is_xcons_term t then incr k3
         | [] -> if is_xnil_term t && not (is_xcons_term t) then incr k3)) lists;
    line name (Printf.sprintf "mk_xlist_term / dest_xlist (%d lists)" n) (Printf.sprintf "%d of %d" !k1 n);
    line name "mk_xlist_term = xcons ... xnil" (Printf.sprintf "%d of %d" !k2 n);
    line name "dest_xcons / is_xnil_term" (Printf.sprintf "%d of %d" !k3 n);
    let cons = opname_of (mk_xcons_term (simple "c") xnil_term) and nil = opname_of xnil_term in
    List.iter (fun (what, t) -> line name what (Printf.sprintf "is_xlist %b, dest_xlist %s" (is_xlist_term t) (refused (fun () -> dest_xlist t))))
      [ "cons with tail c", mk_xcons_term (simple "c") (simple "c");
        "cons binding x", mk_term (mk_op cons []) [ mk_bterm [ sym "x" ] (simple "c"); mk_bterm [] xnil_term ];
        "xnil with a parameter", mk_term (mk_op nil [ make_param (Term_sig.Number (Lm_num.num_of_int 1)) ]) [] ];
    let a = simple "c" and b = mk_var_term (sym "x") in
    let r = mk_xrewrite_term a b in
    let ra, rb = dest_xrewrite r in
    line name "xrewrite round trip" (string_of_bool (is_xrewrite_term r && alpha_equal ra a && alpha_equal rb b));
    line name "xrewrite of an xcons" (Printf.sprintf "is %b, dest %s" (is_xrewrite_term (mk_xcons_term a b)) (refused (fun () -> dest_xrewrite (mk_xcons_term a b))));
    line name "xbind" (Printf.sprintf "is %b; of xcons %b" (is_xbind_term (mk_xbind_term (sym "v") a)) (is_xbind_term (mk_xcons_term a b)));
    let s, st = dest_xstring_dep0_term (mk_xstring_dep0_term "str" a) in
    line name "xstring_dep0 round trip" (string_of_bool (is_xstring_dep0_term (mk_xstring_dep0_term "str" a) && s = "str" && alpha_equal st a));
    let sop = opname_of (mk_xstring_term "s") in
    List.iter (fun (what, t) -> line name what (Printf.sprintf "is %b, dest %s" (is_xstring_dep0_term t) (refused (fun () -> dest_xstring_dep0_term t))))
      [ "xstring with no subterm", mk_xstring_term "s";
        "xstring with a bound subterm", mk_term (mk_op sop [ make_param (Term_sig.String "s") ]) [ mk_bterm [ sym "y" ] a ] ];
    let v = sym "z" in
    List.iter (fun (what, t) ->
        line name what (Printf.sprintf "is_fso %b, dest_fso_var %s" (is_fso_var_term t)
                          (try Lm_symbol.to_string (dest_fso_var t) with R.RefineError.RefineError _ -> "refused")))
      [ "variable z", mk_var_term v;
        "z<||> (no contexts, no arguments)", mk_so_var_term v [] [];
        "z<|H|> (a context, no arguments)", mk_so_var_term v [ sym "H" ] [];
        "z[c] (an argument)", mk_so_var_term v [] [ a ];
        "the term c", a ];
    let vars = [| sym "p"; sym "q"; sym "r" |] and params = [ simple "c"; simple "d" ] and terms = [ b ] in
    let rec peel t acc =
      if is_xbind_term t then
        match (dest_term t).term_terms with
        | [ bt ] -> (match (dest_bterm bt).bvars with [ x ] -> peel (dest_bterm bt).bterm (x :: acc) | _ -> None)
        | _ -> None
      else Some (List.rev acc, t) in
    line name "construct_redex [|p;q;r|] [c;d] [x]"
      (match peel (construct_redex vars params terms) [] with
       | Some (bs, inner) ->
           Printf.sprintf "binders %s, body is params @ terms %b"
             (String.concat "," (List.map Lm_symbol.to_string bs)) (same (dest_xlist inner) (params @ terms))
       | None -> "not xbinds");
    line name "xconcl_term" (Printf.sprintf "%s, %d subterms" (Opname.string_of_opname (opname_of xconcl_term)) (List.length (dest_term xconcl_term).term_terms))
end

module Std = S (Refiner_std.Refiner)
module Ds = S (Refiner_ds.Refiner)

let () =
  let lists_ds = List.init 500 (fun _ -> List.init (pick 6) (fun _ -> pick 3)) in
  Printf.printf "500 lists, lengths 0-5 (%d empty)\n" (List.length (List.filter (( = ) []) lists_ds));
  Std.run "std" lists_ds;
  Ds.run "ds" lists_ds
