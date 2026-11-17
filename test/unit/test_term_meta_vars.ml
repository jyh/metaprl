(* Term_meta_gen's variable walkers over meta-terms (refiner/term_gen/
   term_meta_gen.ml): context_vars, context_vars_info and so_vars_info,
   whose compound arms no unit test reached (bisect at a45cd0437:
   so_vars_info's 7 points, and the Implies/Iff/Function/Labeled arms of
   the other two).  One meta-term of each form is built from pieces that
   each carry their own second-order variables and contexts:
     p1 = f{'a<|H|>['x]}            p2 = s{<H>; y: 'b<|H|> >- 'c<|H|>['y]}
     p3 = g{'d}                     arg = 'e
   and each walker's result is printed, sorted, in term_std and term_ds
   (the two must agree).  so_vars_info maps a variable to (number of
   contexts, number of arguments); context_vars_info maps a context to
   (bound?, number of contexts, number of arguments).  The expected file
   is the output of the code. *)
open Term_sig
let v = Lm_symbol.add
module S (R : Refiner_sig.RefinerSig) = struct
  open R.Term
  open R.TermMan
  open R.TermMeta
  let op s = Opname.make_opname [ s ]
  let mk s ts = mk_simple_term (op s) ts
  let sov x conts args = mk_so_var_term (v x) (List.map v conts) args
  let p1 = mk "f" [ sov "a" [ "H" ] [ mk_var_term (v "x") ] ]
  let p2 = mk_sequent_term { sequent_args = mk "s" [];
                             sequent_hyps = R.Term.SeqHyp.of_list [ Context (v "H", [], []); Hypothesis (v "y", sov "b" [ "H" ] []) ];
                             sequent_concl = sov "c" [ "H" ] [ mk_var_term (v "y") ] }
  let p3 = mk "g" [ sov "d" [] [] ]
  let arg = sov "e" [] []
  let forms =
    [ "Theorem p1", MetaTheorem p1;
      "Labeled (l, Theorem p2)", MetaLabeled ("l", MetaTheorem p2);
      "Implies (p1, p2)", MetaImplies (MetaTheorem p1, MetaTheorem p2);
      "Iff (p2, p3)", MetaIff (MetaTheorem p2, MetaTheorem p3);
      "Function (arg, p1, p3)", MetaFunction (arg, MetaTheorem p1, MetaTheorem p3) ]
  let names s = String.concat " " (List.sort compare (List.map Lm_symbol.string_of_symbol (Lm_symbol.SymbolSet.to_list s)))
  let table show t = String.concat " " (List.sort compare (Lm_symbol.SymbolTable.fold (fun acc k x -> (Lm_symbol.string_of_symbol k ^ show x) :: acc) [] t))
  let lines () =
    List.map (fun (name, mt) ->
        let bound, all = context_vars mt in
        name,
        [ "context_vars: bound {" ^ names bound ^ "}, all {" ^ names all ^ "}";
          "context_vars_info: " ^ table (fun (b, c, a) -> Printf.sprintf "(%b,%d,%d)" b c a) (context_vars_info Lm_symbol.SymbolTable.empty mt);
          "so_vars_info: " ^ table (fun (c, a) -> Printf.sprintf "(%d,%d)" c a) (so_vars_info Lm_symbol.SymbolTable.empty mt) ]) forms
end
module Std = S (Refiner_std.Refiner)
module Ds = S (Refiner_ds.Refiner)
let () =
  let s = Std.lines () and d = Ds.lines () in
  List.iter2 (fun (name, ls) (_, ld) ->
      Printf.printf "%s:%s\n" name (if ls = ld then "" else "  (ds DIFFERS)");
      List.iter (fun l -> Printf.printf "  %s\n" l) ls;
      if ls <> ld then List.iter (fun l -> Printf.printf "  ds: %s\n" l) ld) s d
