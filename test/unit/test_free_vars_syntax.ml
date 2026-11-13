(* unit-link: filter *)
(* unit-native: camlp5/o_keywords.cmx camlp5/pa_o.cmx *)
(*
 * Free_vars (filter/base) on expressions parsed by camlp5's OCaml parser
 * (pa_o), for the constructs test_free_vars cannot build by hand: each line
 * is the expression, what Free_vars.free_vars gives, and whether that
 * agrees with the free variables OCaml gives it (the want list, read off
 * OCaml's scoping rules by hand, as in test_free_vars' hand cases).
 * pa_o is a native object only, hence line 2.
 *)
let sorted l = List.sort_uniq compare l
let show l = "[" ^ String.concat "," (sorted l) ^ "]"

let parse_expr s =
   match fst (List.hd (fst (Pcaml.parse_implem (Stream.of_string ("let _ = " ^ s ^ ";;"))))) with
      MLast.StVal (_, _, Ploc.VaVal [(_, e, _)]) -> e
    | MLast.StExp (_, MLast.ExLet (_, _, Ploc.VaVal [(_, e, _)], _), _) -> e (* pa_o may read "let _ = e;;" as an expression *)
    | MLast.StExp (_, e, _) -> e
    | _ -> failwith "not an expression"

let fv s =
   match Free_vars.free_vars (parse_expr s) with
      l -> show l
    | exception ex -> "ERROR " ^ Printexc.to_string ex

let cases = [
   (* already handled: the harness agrees with them *)
   "f x", ["f"; "x"];
   "fun x -> x y", ["y"];
   (* not handled before this test *)
   "{ r with a = x }", ["r"; "x"];
   "f ~y:x ()", ["f"; "x"];
   "f ~y", ["f"; "y"];
   "lazy (f x)", ["f"; "x"];
   "assert x", ["x"];
   "let open M in f x", ["f"; "x"];
   "x + 3l + 3L + 3n", ["+"; "x"];
   "function `A -> a | `B n -> n", ["a"];
   "function [| x; _ |] -> x | _ -> y", ["y"];
   "function 3l -> a | _ -> b", ["a"; "b"];
   "object (self) val v = a method m = self#n b method n = v end", ["a"; "b"];
   "(object method m = x end :> t)", ["x"];
   "fun (module X : S) -> X.f y", ["y"];
]

let () =
   List.iter (fun (s, want) ->
         let got = fv s in
         let want = show want in
            Printf.printf "%-62s %-12s %s\n" s got
               (if got = want then "agree" else "DIFFER, OCaml gives " ^ want)) cases
