(* Refine.create_input_form and Refine.mk_rewrite_hack
   (refiner/refiner/refine.ml): the arms no unit test reached (2026-11-15
   profile).  Each line is the output of the code as written (2026-11-15),
   never typed.
   create_input_form: an input form  g{'a} --> lam{y.'a}  is created Relaxed
   (strict = false, the only form the theories reached) and Strict, and
   applied through rwtactic and refine to g{y}, where y is free, and to a
   term it does not match; the contractum's binder y meets the goal's
   free y.  Measured: Relaxed CAPTURES it (g{y} becomes lam{y. y}),
   Strict renames the binder (lam{y1. y}).  Then with the "refine" and "rewrites" debug flags on, which
   print a creation line and a trace line per application on stderr.
   mk_rewrite_hack: the sequent  <H> >- t  it wraps a rewrite term in, where
   every second-order variable and context of t gains H among its
   contexts; here for a variable without H, one that already has it (kept
   once, where it was), and a context term.
   Not reached, and why: create_input_form's "no contracta" and "multiple
   contracta" arms; it gives term_rewrite one contractum and apply_rewrite
   maps over the compiled contracta (rewrite.ml), so a successful
   application returns one term. *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.Refine
open Refiner.Refiner.RefineError

module P = Simple_print.SimplePrint
let sp = P.string_of_term

let op s = Opname.make_opname [ s ]
let v = Lm_symbol.add
let app o ts = mk_simple_term (op o) ts
let lam x t = mk_term (mk_op (op "lam") []) [ mk_bterm [ v x ] t ]
let var s = mk_var_term (v s)
let sov ?(conts = []) x = mk_so_var_term (v x) (List.map v conts) []

let say s = print_string s; print_newline ()

(* A sequent prints on several lines; join them. *)
let one_line s = String.concat " | " (List.filter (fun l -> l <> "") (List.map String.trim (String.split_on_char '\n' s)))

let create strict =
  match create_input_form (null_refiner "test_refine_input_form") "iform" strict (app "g" [ sov "a" ]) (lam "y" (sov "a")) with
  | PrimRW r -> r
  | CondRW _ -> failwith "cond"

let apply r t =
  flush stdout;
  let result =
    match refine any_sentinal (rwtactic 0 r) (mk_msequent t []) with
    | [ m ], _ -> "rewrote to " ^ sp (msequent_goal m)
    | l, _ -> Printf.sprintf "%d subgoals" (List.length l)
    | exception RefineError (loc, _) -> Printf.sprintf "refused at %S" loc
  in
  flush stderr;
  say ("  " ^ sp t ^ ": " ^ result)

let case title strict flags =
  say title;
  List.iter (fun (n, b) -> Lm_debug.set_debug n b) flags;
  flush stdout;
  let r = create strict in
  flush stderr;
  apply r (app "g" [ var "y" ]);
  apply r (app "f" [ var "y" ]);
  List.iter (fun (n, _) -> Lm_debug.set_debug n false) flags

let () =
  say "== create_input_form g{'a} --> lam{y.'a}";
  case "Relaxed" false [];
  case "Strict" true [];
  case "Relaxed, \"refine\" and \"rewrites\" on" false [ "refine", true; "rewrites", true ];
  say "== mk_rewrite_hack";
  List.iter (fun (title, t) -> say (Printf.sprintf "  %-30s %s" title (one_line (sp (mk_rewrite_hack t))))) [
    "'a (no contexts)", sov "a";
    "'a<|J|> (another context)", sov ~conts:[ "J" ] "a";
    "'a<|H|> (H already there)", sov ~conts:[ "H" ] "a";
    "'a<|J; H|>", sov ~conts:[ "J"; "H" ] "a";
    "f{'a; 'b<|H|>}", app "f" [ sov "a"; sov ~conts:[ "H" ] "b" ];
    "a context <J> t", mk_context_term (v "J") (app "t" []) [] [];
    "a context <J<|H|>> t", mk_context_term (v "J") (app "t" []) [ v "H" ] [];
  ]
