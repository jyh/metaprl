(* Rewrite_compile_redex (refiner/rewrite): Strict compilation of a redex
   with argument redices, printed as the compiled program
   (Rewrite.print_rewrite_redex), so the restrictions an argument records
   (map_restricts: which contexts and bound variables a matched variable
   may mention) are seen directly.  Row 450 found that rewrite OUTCOMES do
   not show them: every refusal those probes met came from another check.
   Cases: a second-order variable, a context and a sequent context that
   occur both in the redex and in an argument, a free first-order variable
   in an argument, nested under a composite term, a sequent and a binder.
   Each prints the compiled stack and terms, or the RefineError.
   FOUND A DEFECT, pinned here, not fixed: an argument holding a term
   context with an address argument under a binder (lam y. D<H>[...])
   compiles, under Strict, to a RWSOFreeVarsContext whose restriction
   map_restricts_term looks up by the ADDRESS index i
   (List.assoc i restr) after testing the STACK index j
   (List.mem_assoc j restr), as its RWSOContext case does not; here i is
   not a key, so Not_found escapes compile_redices.  Where i happens to
   be a key, the restriction of another variable would be applied. *)
open Term_sig
open Refiner.Refiner
open TermType
open Term
open TermMan
open RefineError
open Rewrite_sig

let op s = Opname.make_opname [ s; "Rr" ]
let v = Lm_symbol.add
let app o ts = mk_term (mk_op (op o) []) (List.map (fun t -> mk_bterm [] t) ts)
let c0 o = app o []
let so name conts args = mk_so_var_term (v name) (List.map v conts) args
let var x = mk_var_term (v x)
let lam x t = mk_term (mk_op (op "lam") []) [ mk_bterm [ v x ] t ]
let ctx name conts body args = mk_context_term (v name) body (List.map v conts) args
let seq hyps concl =
  mk_sequent_term { sequent_args = c0 "arg"; sequent_hyps = SeqHyp.of_list hyps; sequent_concl = concl }
let show rx = let b = Buffer.create 256 in let out = Lm_printf.formatter_of_buffer b in
  Lm_printf.pp_set_margin out 100; Rewrite.print_rewrite_redex out rx; Lm_printf.pp_print_flush out (); Buffer.contents b

let case name ?(ints = [||]) ?(addrs = [||]) strict redex args =
  Printf.printf "== %s (%s)\n%!" name (match strict with Strict -> "Strict" | Relaxed -> "Relaxed");
  let r =
    try show (Rewrite.compile_redices strict { spec_ints = ints; spec_addrs = addrs } (redex :: args)) with
    | RefineError (s, e) ->
        "REFUSED: " ^ s ^ (match e with
          | StringVarError (m, x) -> " (" ^ m ^ ": " ^ Lm_symbol.to_string x ^ ")"
          | StringError m -> " (" ^ m ^ ")" | _ -> "")
    | Invalid_argument s -> "INVALID_ARGUMENT: " ^ s
    | Not_found -> "Not_found, escaping compile_redices"
  in
  print_endline r

let goal =
  seq [ Context (v "H", [], []); Hypothesis (v "x", so "A" [ "H" ] []); Context (v "J", [ v "H" ], [ var "x" ]) ]
    (so "C" [ "H"; "J" ] [ var "x" ])

let () =
  List.iter (fun strict ->
      case "goal, argument 'T<H>" strict goal [ so "T" [ "H" ] [] ] ~ints:[| v "H" |];
      case "goal, argument 'A<H> (the hypothesis' variable)" strict goal [ so "A" [ "H" ] [] ] ~ints:[| v "H" |];
      case "goal, argument 'C<H;J>['x]" strict goal [ so "C" [ "H"; "J" ] [ var "x" ] ] ~ints:[| v "H" |];
      case "goal, argument 'C<H>['x]" strict goal [ so "C" [ "H" ] [ var "x" ] ] ~ints:[| v "H" |];
      case "goal, argument J<H>['x] (a context)" strict goal [ ctx "J" [ "H" ] (c0 "hole") [ var "x" ] ] ~ints:[| v "H" |];
      case "goal, argument g{z} (z free)" strict goal [ app "g" [ var "z" ] ] ~ints:[| v "H" |];
      case "goal, argument x (the bound x)" strict goal [ var "x" ] ~ints:[| v "H" |];
      case "f{C<|H|>[g{'a}]}, argument C<H>[c]" strict
        (app "f" [ ctx "C" [] (app "g" [ so "a" [] [] ]) [] ]) [ ctx "C" [ "H" ] (c0 "c") [] ];
      case "f{lam y. 'b['y]}, argument 'b<H>['w]" strict
        (app "f" [ lam "y" (so "b" [] [ var "y" ]) ]) [ so "b" [ "H" ] [ var "w" ] ];
      case "f{'a; g{'a}}, argument 'a<H>" strict
        (app "f" [ so "a" [] []; app "g" [ so "a" [] [] ] ]) [ so "a" [ "H" ] [] ];
      case "f{z} (z free), argument z" strict (app "f" [ var "z" ]) [ var "z" ];
      case "f{z} (z free), argument g{z}" strict (app "f" [ var "z" ]) [ app "g" [ var "z" ] ];
      case "goal, argument <K<H>> >- c (a sequent)" strict goal [ seq [ Context (v "K", [ v "H" ], []) ] (c0 "c") ] ~ints:[| v "H" |];
      case "goal, argument <K<H>>; w: d >- c" strict goal
        [ seq [ Context (v "K", [ v "H" ], []); Hypothesis (v "w", c0 "d") ] (c0 "c") ] ~ints:[| v "H"; v "K" |];
      case "goal, argument <K<H>['x]> >- c" strict goal [ seq [ Context (v "K", [ v "H" ], [ var "x" ]) ] (c0 "c") ] ~ints:[| v "H" |];
      case "goal, argument D<H>[g{'a}] (address D)" strict goal [ ctx "D" [ "H" ] (app "g" [ so "a" [] [] ]) [] ] ~ints:[| v "H" |] ~addrs:[| v "D" |];
      case "goal, argument lam y. D<H>[g{'a}] (address D)" strict goal
        [ lam "y" (ctx "D" [ "H" ] (app "g" [ so "a" [] [] ]) []) ] ~ints:[| v "H" |] ~addrs:[| v "D" |];
      case "goal, argument g{'e; lam y. D<H>[g{'a}]} (address D)" strict goal
        [ app "g" [ so "e" [] []; lam "y" (ctx "D" [ "H" ] (app "g" [ so "a" [] [] ]) []) ] ] ~ints:[| v "H" |] ~addrs:[| v "D" |];
      case "goal, argument lam y. 'b<H>" strict goal [ lam "y" (so "b" [ "H" ] []) ] ~ints:[| v "H" |];
      case "goal, argument lam y. (<K<H>> >- c)" strict goal [ lam "y" (seq [ Context (v "K", [ v "H" ], []) ] (c0 "c")) ] ~ints:[| v "H" |];
      case "goal, argument <K<H>> >- g{<K>}" strict goal
        [ seq [ Context (v "K", [ v "H" ], []) ] (app "g" [ seq [ Context (v "K", [ v "H" ], []) ] (c0 "c") ]) ] ~ints:[| v "H" |];
      case "f{c}, argument lam y. z (z free)" strict (app "f" [ c0 "c" ]) [ lam "y" (var "z") ];
      case "<H>; x: 'A<H>; y: 'A<H> >- 'C<H>" strict
        (seq [ Context (v "H", [], []); Hypothesis (v "x", so "A" [ "H" ] []); Hypothesis (v "y", so "A" [ "H" ] []) ] (so "C" [ "H" ] [])) [])
    [ Strict; Relaxed ]
