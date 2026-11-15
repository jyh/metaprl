(* unit-link: filter *)
(* Mbterm (library/mbterm.ml), the Nuprl-5 link's MathBus encoding of
   terms: mbterm_of_term and term_of_mbterm, there and back.  Its
   parameter encoding (mbparameter_of_param) and the subterm loop of
   term_of_mbterm (loop1) were reached by no unit test, theory build or
   proof census (2026-11-15 rank).  The MathBus labels are numbers the
   link reads from lib/registry.txt (Registry.read_registry, only in the
   editor's connection code); here each label is stored in the local
   registry under a number of its own, which is all the encoding needs
   (distinct labels).  Each line prints what comes back, marked
   "(DIFFERS)" when it is not alpha_equal to what went in.
   Pinned as found:
   - a Number of 19 digits or more comes back cut to its first 18:
     MathBus.mb_number writes base-10^9 digits, as many as the number
     has, and number_value reads the first two;
   - a Token comes back as one flat name (Test!tk, one component), so
     it is not the token that went in;
   - a level expression comes back with its variables in the reverse
     order ({2 | 'j | 'i'}); a level is a max, but the term differs.
   A Quote parameter is refused (as the code says).
   The expected file is the output of the code as written (2026-11-15),
   never typed. *)
open Refiner.Refiner.Term
open Refiner.Refiner.TermType
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst

let labels = [ "Attributes"; "String"; "LongInteger"; "Token"; "Term"; "Variable"; "Bindings"; "Level";
               "ObjectId"; "ParmList"; "TermIndex"; "TokenIndex"; "StringIndex"; "MString"; "MLongInteger";
               "MLevel"; "MToken" ]
let () =
  List.iteri (fun i l -> Registry.registry_store_local l "StringId" (Lint32.lint32_of_int (0x1101 + i))) labels;
  MathBus.assign_mbs_vals ();
  Mbterm.assign_mbs_terms ()

let rec show_param p =
  match dest_param p with
    Number n -> "Number " ^ Lm_num.string_of_num n
  | String s -> Printf.sprintf "String %S" s
  | Token t -> "Token " ^ Opname.string_of_opname t
  | Var v -> "Var " ^ Lm_symbol.string_of_symbol v
  | MNumber v -> "MNumber " ^ Lm_symbol.string_of_symbol v
  | MString v -> "MString " ^ Lm_symbol.string_of_symbol v
  | MToken v -> "MToken " ^ Lm_symbol.string_of_symbol v
  | MLevel l -> "MLevel " ^ Simple_print.SimplePrint.string_of_level_exp l
  | ParamList ps -> "[" ^ String.concat "; " (List.map show_param ps) ^ "]"
  | ObId _ -> "ObId"
  | Quote -> "Quote"
  | Shape _ | MShape _ | Operator _ | MOperator _ -> "(other)"

let exn_string = function
  | Failure m -> "Failure " ^ m
  | Invalid_argument m -> "Invalid_argument " ^ m
  | e -> Printexc.to_string e

let params_of t = (dest_op (dest_term t).term_op).op_params

let param name p =
  let t = mk_term (mk_op (Opname.make_opname [ "p"; "Test" ]) [ p ]) [] in
  let r =
    try
      let t' = Mbterm.term_of_mbterm (Mbterm.mbterm_of_term t) in
        String.concat ", " (List.map show_param (params_of t')) ^ (if alpha_equal t t' then "" else "  (DIFFERS)")
    with e -> exn_string e
  in
    Printf.printf "%-14s %-42s -> %s\n%!" name (show_param p) r

let v = Lm_symbol.add
let lev = mk_level 2 [ mk_level_var (v "i") 1; mk_level_var (v "j") 0 ]

let () =
  print_endline "parameters, there and back:";
  param "number" (make_param (Number (Lm_num.num_of_int 42)));
  List.iter (fun (n, v) -> param n (make_param (Number (Lm_num.num_of_string v))))
    [ "negative", "-42"; "10^9", "1000000000"; "10^18 - 1", "999999999999999999"; "-(10^18 - 1)", "-999999999999999999";
      "10^18", "1000000000000000000"; "30 digits", "123456789012345678901234567890";
      "-30 digits", "-123456789012345678901234567890" ];
  param "string" (make_param (String "s"));
  param "token" (make_param (Token (Opname.make_opname [ "tk"; "Test" ])));
  param "var" (make_param (Var (v "x")));
  param "mnumber" (make_param (MNumber (v "n")));
  param "mstring" (make_param (MString (v "m")));
  param "mtoken" (make_param (MToken (v "t")));
  param "mlevel" (make_param (MLevel lev));
  param "list" (make_param (ParamList [ make_param (Number (Lm_num.num_of_int 1)); make_param (String "a") ]));
  param "quote" (make_param Quote)

let term name t =
  let r =
    try
      let t' = Mbterm.term_of_mbterm (Mbterm.mbterm_of_term t) in
        Simple_print.SimplePrint.string_of_term t' ^ (if alpha_equal t t' then "" else "  (DIFFERS)")
    with e -> exn_string e
  in
    Printf.printf "%-18s %s\n%!" name r

let op s ps = mk_op (Opname.make_opname [ s; "Test" ]) ps
let c = mk_term (op "c" []) []
let () =
  print_endline "terms, there and back:";
  term "constant" c;
  term "one subterm" (mk_term (op "f" []) [ mk_bterm [] c ]);
  term "three subterms" (mk_term (op "g" []) [ mk_bterm [] c; mk_bterm [] c; mk_bterm [] c ]);
  term "binding last" (mk_term (op "lam" []) [ mk_bterm [ v "x" ] (mk_var_term (v "x")) ]);
  term "binding first" (mk_term (op "h" []) [ mk_bterm [ v "x"; v "y" ] (mk_var_term (v "y")); mk_bterm [] c ]);
  term "params" (mk_term (op "p" [ make_param (Number (Lm_num.num_of_int 3)); make_param (String "s") ]) [ mk_bterm [] c ]);
  term "two bindings" (mk_term (op "k" []) [ mk_bterm [ v "x" ] (mk_var_term (v "x")); mk_bterm [ v "y" ] c; mk_bterm [] c ])
