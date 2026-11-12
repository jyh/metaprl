(* Tactic_boot, the parts no test reached (2026-11-11 reach census: 178 of
   tactic_boot.ml's 378 points reached by nothing): the arglist
   compression (compress_arglist / expand_arglist, one arm per argument
   shape), the extract and attribute printers (format_extract,
   format_attrs), the remove*T and without*T attribute tactics, and the
   accessors set_goal, set_label, set_msequent, all_assums, get_strings,
   mem_string.
   (1) Every list of one or two attributes over String, Bool, Int and Term
       (and None, a three-element list, and other kinds) is compressed and
       expanded; the line prints the arglist constructor and whether the
       expansion is the input.
   (2) The extract of a refinement by each kind of tactic, and the
       attributes after add*T of every kind, are printed with
       Dform.null_base at width 100.
   (3) For each attribute kind, the subgoal of add*T then remove*T, and the
       argument seen inside without*T, print whether the attribute is
       there, and the values of the string attribute s, which holds two.
   Pinned as it reads today, including: removeStringT and withoutStringT
   on a name with two values remove only the most recent one. *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Tactic_boot
open Tactic_boot_sig
open Tacticals_boot.Tacticals

let at n = mk_simple_term (Opname.make_opname [ n ]) []
let print w f = let buf = Lm_rformat.new_buffer () in match f buf with () -> Lm_rformat_text.print_text_string w buf | exception e -> "raised " ^ Printexc.to_string e
let say fmt = Printf.ksprintf (fun s -> print_string s; flush stdout) fmt

let show_attr = function
  | TermArg t -> "Term " ^ Simple_print.SimplePrint.string_of_term t | TypeArg t -> "Type " ^ Simple_print.SimplePrint.string_of_term t
  | IntArg i -> "Int " ^ string_of_int i | AddrArg _ -> "Addr" | BoolArg b -> "Bool " ^ string_of_bool b
  | StringArg s -> "String " ^ s | TermListArg l -> Printf.sprintf "TermList(%d)" (List.length l)
let kind = function
  | NoneArgList _ -> "None" | IntArgList _ -> "Int" | BoolArgList _ -> "Bool" | StringArgList _ -> "String" | TermArgList _ -> "Term"
  | IntIntArgList _ -> "IntInt" | IntBoolArgList _ -> "IntBool" | IntStringArgList _ -> "IntString" | IntTermArgList _ -> "IntTerm"
  | BoolIntArgList _ -> "BoolInt" | BoolBoolArgList _ -> "BoolBool" | BoolStringArgList _ -> "BoolString" | BoolTermArgList _ -> "BoolTerm"
  | StringIntArgList _ -> "StringInt" | StringBoolArgList _ -> "StringBool" | StringStringArgList _ -> "StringString" | StringTermArgList _ -> "StringTerm"
  | TermIntArgList _ -> "TermInt" | TermBoolArgList _ -> "TermBool" | TermStringArgList _ -> "TermString" | TermTermArgList _ -> "TermTerm"
  | GeneralArgList a -> Printf.sprintf "General(%d)" (Array.length a)

let base () =
  let b = TacticInternal.debug_arg Mp_resource.empty_bookmark (at "A") in
  { b with TacticInternalType.ref_goal = Refine.mk_msequent (at "A") [ at "A" ] }

let () =
  (* (1) arglists: the name is the first attribute, which must be a string *)
  say "== compress_arglist / expand_arglist\n";
  let atoms = [ StringArg "s"; BoolArg true; IntArg 3; TermArg (at "T") ] in
  let check l =
    match Tactic.compress_arglist l with
    | exception e -> say "%-34s raised %s\n" (String.concat ", " (List.map show_attr l)) (Printexc.to_string e)
    | c -> say "%-34s %-14s expands back: %b\n" (String.concat ", " (List.map show_attr l)) (kind c)
             (Tactic.expand_arglist c = l) in
  List.iter (fun x -> check [ StringArg "name"; x ]) atoms;
  let atoms2 = [ StringArg "s2"; BoolArg false; IntArg 4; TermArg (at "U") ] in
  List.iter (fun x -> List.iter (fun y -> check [ StringArg "name"; x; y ]) atoms2) atoms;
  check [ StringArg "name" ];
  check [ StringArg "name"; IntArg 1; IntArg 2; IntArg 3 ];
  check [ StringArg "name"; TypeArg (at "T") ];
  check [ StringArg "name"; TermListArg [ at "T" ] ];
  check [ IntArg 1 ];
  check [];
  (* (2) printers *)
  say "== format_extract (width 100)\n";
  let ext name tac =
    match TacticInternal.refine tac (base ()) with
    | exception e -> say "%s: refine raised %s\n" name (Printexc.to_string e)
    | _, e -> say "-- %s\n%s\n" name (print 100 (fun buf -> TacticInternal.format_extract Dform.null_base buf e)) in
  ext "idT" idT;
  ext "cutT B" (cutT (at "B"));
  ext "nthAssumT 1" (nthAssumT 1);
  ext "wrapT (cutT B)" (TacticInternal.wrapT (IntArgList ("w", 7)) (cutT (at "B")));
  ext "addIntT k 3" (TacticInternal.addIntT "k" 3);
  ext "cutT B thenLT [idT; nthAssumT 1]" (prefix_thenLT (cutT (at "B")) [ idT; nthAssumT 1 ]);
  ext "withTermT w C (cutT B)" (TacticInternal.withTermT "w" (at "C") (cutT (at "B")));
  say "== format_attrs after add*T of every kind (width 100)\n";
  let arg = List.fold_left (fun a tac -> match TacticInternal.refine tac a with [ a' ], _ -> a' | _ -> a) (base ()) [
      TacticInternal.addTermT "t" (at "T"); TacticInternal.addTermListT "tl" [ at "T"; at "U" ]; TacticInternal.addTypeT "ty" (at "Ty");
      TacticInternal.addBoolT "b" true; TacticInternal.addIntT "i" 5; TacticInternal.addStringT "s" "str"; TacticInternal.addStringT "s" "two" ] in
  say "%s\n" (print 100 (fun buf -> TacticInternal.format_attrs Dform.null_base buf arg.TacticInternalType.ref_attributes));
  say "get_strings s: [%s]; mem_string s two: %b; mem_string s three: %b\n"
    (String.concat "; " (TacticInternal.get_strings arg "s")) (TacticInternal.mem_string arg "s" "two") (TacticInternal.mem_string arg "s" "three");
  (* (3) remove*T and without*T *)
  say "== remove*T and without*T\n";
  let present a = String.concat " " (List.filter_map (fun (n, f) -> if f a then Some n else None) [
      "term", (fun a -> TacticInternal.get_term a "t" <> None); "term_list", (fun a -> TacticInternal.get_term_list a "tl" <> None);
      "type", (fun a -> TacticInternal.get_type a "ty" <> None); "bool", (fun a -> TacticInternal.get_bool a "b" <> None);
      "int", (fun a -> TacticInternal.get_int a "i" <> None); "string", (fun a -> TacticInternal.get_strings a "s" <> []) ]) in
  say "%-32s %s\n" "all added" (present arg);
  let after name tac = match TacticInternal.refine tac arg with [ a ], _ -> say "%-32s %s | strings %s\n" name (present a) (String.concat "," (TacticInternal.get_strings a "s")) | l, _ -> say "%-32s %d subgoals\n" name (List.length l) in
  after "removeTermT t" (TacticInternal.removeTermT "t");
  after "removeTermListT tl" (TacticInternal.removeTermListT "tl");
  after "removeTypeT ty" (TacticInternal.removeTypeT "ty");
  after "removeBoolT b" (TacticInternal.removeBoolT "b");
  after "removeIntT i" (TacticInternal.removeIntT "i");
  after "removeStringT s" (TacticInternal.removeStringT "s");
  after "removeStringValT s two" (TacticInternal.removeStringValT "s" "two");
  after "removeStringValT s str" (TacticInternal.removeStringValT "s" "str");
  let inside name w = let seen = ref "" in
    ignore (TacticInternal.refine (w (fun a -> seen := present a ^ " | strings " ^ String.concat "," (TacticInternal.get_strings a "s"); idT a)) arg);
    say "%-32s %s\n" name !seen in
  inside "withoutTermT t" (TacticInternal.withoutTermT "t");
  inside "withoutTermListT tl" (TacticInternal.withoutTermListT "tl");
  inside "withoutTypeT ty" (TacticInternal.withoutTypeT "ty");
  inside "withoutBoolT b" (TacticInternal.withoutBoolT "b");
  inside "withoutIntT i" (TacticInternal.withoutIntT "i");
  inside "withoutStringT s" (TacticInternal.withoutStringT "s");
  inside "withoutStringValT s two" (TacticInternal.withoutStringValT "s" "two");
  inside "withoutStringValT s str" (TacticInternal.withoutStringValT "s" "str");
  (* accessors *)
  say "== accessors\n";
  let a = TacticInternal.set_goal arg (at "G") in
  say "set_goal: goal %s, assumptions %d\n" (Simple_print.SimplePrint.string_of_term (TacticInternal.goal a)) (List.length (TacticInternal.all_assums a));
  say "set_label: %s\n" (TacticInternal.set_label arg "lbl").TacticInternalType.ref_label;
  let m = TacticInternal.set_msequent arg (Refine.mk_msequent (at "H") [ at "P"; at "Q" ]) in
  say "set_msequent: goal %s, all_assums %s\n" (Simple_print.SimplePrint.string_of_term (TacticInternal.goal m))
    (String.concat " " (List.map Simple_print.SimplePrint.string_of_term (TacticInternal.all_assums m)))
