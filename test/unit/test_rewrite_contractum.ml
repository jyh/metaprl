(* Rewrite_build_contractum (refiner/rewrite): the branches the proof
   census runs and no unit test did (2026-11-11 reach census, 38 lines):
   meta and variable parameters rebuilt in the contractum, a contractum
   binder renamed to avoid capturing a free variable of the substituted
   terms (one binder and two), a context filled through an address
   argument, and a sequent context whose bound variable is replaced by a
   term in the contractum (its hypotheses substituted).  Pinned as found:
   a new contractum binder is renamed away from clashing names in Strict
   mode only.  In Strict, apply_rewrite avoids the goal's free variables
   and the names collected from the match stack (collect_bnames); in
   Relaxed it avoids nothing.  So the Relaxed rewrite g{'a} --> lam y.
   h{'a; y} on g{y} captures y.  (Dropping the goal's free variables alone
   does not change these cases, because collect_bnames already holds y.)  Each case is a
   term_rewrite applied to a target; it prints the result, or the
   RefineError it raises.  The expected file is the output of the code as
   written (2026-11-11), never typed. *)
open Term_sig
open Term_addr_sig
open Refiner.Refiner
open TermType
open Term
open TermMan
open RefineError
open Rewrite_sig

let op s = Opname.make_opname [ s; "Rbc" ]
let v = Lm_symbol.add
let app o ts = mk_term (mk_op (op o) []) (List.map (fun t -> mk_bterm [] t) ts)
let p1 o prm = mk_term (mk_op (op o) [ make_param prm ]) []
let c0 o = app o []
let so name conts args = mk_so_var_term (v name) (List.map v conts) args
let var x = mk_var_term (v x)
let lam xs t = mk_term (mk_op (op "lam") []) [ mk_bterm (List.map v xs) t ]
let sp = Simple_print.SimplePrint.string_of_term
let seq hyps concl =
  mk_sequent_term { sequent_args = c0 "arg"; sequent_hyps = SeqHyp.of_list hyps; sequent_concl = concl }

let rw ?(strict = Relaxed) ?(ints = [||]) ?(addrs = [||]) ?(arg_ints = [||]) ?(arg_addrs = [||]) name redex contractum target =
  let r =
    try
      let rw = Rewrite.term_rewrite strict { spec_ints = ints; spec_addrs = addrs } [ redex ] [ contractum ] in
      match Rewrite.apply_rewrite rw ({ arg_ints; arg_addrs }, Lm_symbol.SymbolSet.empty) target [] with
      | [ r ] -> sp r
      | l -> Printf.sprintf "%d results" (List.length l)
    with
    | RefineError (s, _) -> "REFUSED: " ^ s
    | Invalid_argument s -> "INVALID_ARGUMENT: " ^ s
  in
  Printf.printf "%-46s %s\n" name r

let () =
  print_endline "== parameters rebuilt in the contractum";
  rw "h[@n:n] --> k[@n:n] on h[@m:n]" (p1 "h" (MNumber (v "n"))) (p1 "k" (MNumber (v "n"))) (p1 "h" (MNumber (v "m")));
  rw "h[@n:n] --> k[@n:n] on h[7:n]" (p1 "h" (MNumber (v "n"))) (p1 "k" (MNumber (v "n"))) (p1 "h" (Number (Lm_num.num_of_int 7)));
  rw "h[@s:s] --> k[@s:s] on h[@m:s]" (p1 "h" (MString (v "s"))) (p1 "k" (MString (v "s"))) (p1 "h" (MString (v "m")));
  rw "h[@t:t] --> k[@t:t] on h[@m:t]" (p1 "h" (MToken (v "t"))) (p1 "k" (MToken (v "t"))) (p1 "h" (MToken (v "m")));
  rw "h[@x:v] --> k[@x:v] on h[y:v]" (p1 "h" (Var (v "x"))) (p1 "k" (Var (v "x"))) (p1 "h" (Var (v "y")));
  print_endline "== contractum binders and capture";
  let redex = app "g" [ so "a" [] []; lam [ "y" ] (so "b" [] [ var "y" ]) ] in
  let contractum = lam [ "y" ] (app "h" [ so "a" [] []; so "b" [] [ var "y" ] ]) in
  rw "g{'a; lam y.'b['y]} --> lam y. h{'a; 'b['y]}, a = c" redex contractum (app "g" [ c0 "c"; lam [ "z" ] (var "z") ]);
  rw "the same, a = y (free y would be captured)" redex contractum (app "g" [ var "y"; lam [ "z" ] (var "z") ]);
  let redex2 = app "g" [ so "a" [] []; lam [ "x"; "y" ] (so "b" [] [ var "x"; var "y" ]) ] in
  let contractum2 = lam [ "x"; "y" ] (app "h" [ so "a" [] []; so "b" [] [ var "x"; var "y" ] ]) in
  rw "two binders, a = c" redex2 contractum2 (app "g" [ c0 "c"; lam [ "p"; "q" ] (app "f" [ var "p"; var "q" ]) ]);
  rw "two binders, a = f{x; y} (both would be captured)" redex2 contractum2
    (app "g" [ app "f" [ var "x"; var "y" ]; lam [ "p"; "q" ] (app "f" [ var "p"; var "q" ]) ]);
  let fresh = lam [ "y" ] (app "h" [ so "a" [] []; var "y" ]) in
  rw "g{'a} --> lam y. h{'a; y} (a new binder), a = c" (app "g" [ so "a" [] [] ]) fresh (app "g" [ c0 "c" ]);
  rw "the same, a = y, Relaxed (y captured)" (app "g" [ so "a" [] [] ]) fresh (app "g" [ var "y" ]);
  rw "the same, a = y, Strict (binder renamed)" ~strict:Strict (app "g" [ so "a" [] [] ]) fresh (app "g" [ var "y" ]);
  rw "the same, a = c, Strict" ~strict:Strict (app "g" [ so "a" [] [] ]) fresh (app "g" [ c0 "c" ]);
  print_endline "== a context filled through an address";
  let ctx t = app "f" [ mk_context_term (v "C") t [] [] ] in
  let at path = [| TermAddr.make_address (List.map (fun i -> Subterm i) path) |] in
  let target = app "f" [ app "h" [ app "k" [ c0 "d"; app "g" [ c0 "c" ] ] ] ] in
  rw "f{C[g{'x}]} --> f{C[m{'x; 'x}]}, hole at h.1.2" (ctx (app "g" [ so "x" [] [] ])) (ctx (app "m" [ so "x" [] []; so "x" [] [] ]))
    target ~addrs:[| v "C" |] ~arg_addrs:(at [ 1; 2 ]);
  rw "f{C[g{'x}]} --> m{'x}, hole at h.1.2" (ctx (app "g" [ so "x" [] [] ])) (app "m" [ so "x" [] [] ])
    target ~addrs:[| v "C" |] ~arg_addrs:(at [ 1; 2 ]);
  print_endline "== a sequent context with its variable replaced";
  let redex = seq [ Context (v "H", [], []); Hypothesis (v "x", so "A" [ "H" ] []); Context (v "J", [ v "H" ], [ var "x" ]) ]
      (so "C" [ "H"; "J" ] [ var "x" ]) in
  let thin t = seq [ Context (v "H", [], []); Context (v "J", [ v "H" ], [ t ]) ] (so "C" [ "H"; "J" ] [ t ]) in
  let target = seq [ Hypothesis (v "y", c0 "T"); Hypothesis (v "x", c0 "T"); Hypothesis (v "z", app "g" [ var "x" ]) ] (app "f" [ var "x"; var "z" ]) in
  rw "thin x, replacing it by c" redex (thin (c0 "c")) target ~ints:[| v "H" |] ~arg_ints:[| 2 |];
  rw "thin x, replacing it by y" redex (thin (var "y")) target ~ints:[| v "H" |] ~arg_ints:[| 2 |];
  rw "keep x (the identity)" redex redex target ~ints:[| v "H" |] ~arg_ints:[| 2 |];
  rw "J empty: thin x, replacing it by c" redex (thin (c0 "c"))
    (seq [ Hypothesis (v "y", c0 "T"); Hypothesis (v "x", c0 "T") ] (app "f" [ var "x" ])) ~ints:[| v "H" |] ~arg_ints:[| 2 |]
