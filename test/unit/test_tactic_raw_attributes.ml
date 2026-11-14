(* Tactic_boot's raw attributes, the form a proof's attributes take when
   it is saved (Proof_term_boot.to_term reads Tactic.raw_attributes of the
   goal) and loaded (attribute_info_of_raw_attributes, Proof_boot): no
   unit test, theory build or proof replay reached raw_attributes
   (2026-11-13 rank).  raw_attribute is abstract outside Tactic_boot, so
   each case loads a list of raw attributes into a tactic argument, reads
   it with attributes and get_options, saves it with raw_attributes,
   loads the save again, and prints both sides.
   Pinned as the code reads today (2026-11-14), including:
     - the kinds come back grouped, in the order raw_attributes lists them,
       each kind in its input order;
     - an address attribute is not loaded (attribute_info_of_raw_attributes
       has no RawAddr arm), so it is not saved again;
     - a term attribute named "allow" (the ASCII IO 1.0.25-26 spelling) is
       an option and is saved as "ййallow"; options are folded from the
       right, so of "allow a" then "ignore a" the allow is applied last;
     - EACH SAVE AND LOAD REVERSES THE OPTIONS: the loader numbers a raw
       list from its right end, so its FIRST option becomes the most recent
       decision, while raw_attributes writes the options OLDEST first
       (list_options).  With two options the most recent decision flips at
       every round trip: a rule labelled pa and pe (rule_labels_are_allowed
       takes the most recent decision on its labels) is allowed after the
       load of [allow pa; exclude pe], refused after one save and load, and
       allowed after two; the argument after one round trip is not
       tactic_arg_alpha_equal_with_attributes to the one saved (one option
       round-trips equal);
     - the sentinel keys (attr_keys, RawSentinal) are made only from each
       other (raw_attributes reads the keys, the loader and
       update_attributes read RawSentinal), so no attribute list built
       outside Tactic_boot carries one and every case saves none. *)
open Refiner.Refiner
open Refiner.Refiner.Term
open Tactic_boot
open Tactic_boot_sig

let op s = Opname.make_opname [ s ]
let mk s ts = mk_simple_term (op s) ts
let flat s = String.concat " " (List.filter (( <> ) "") (List.map String.trim (String.split_on_char '\n' s)))
let sp t = flat (Simple_print.SimplePrint.string_of_term t)
let goal = Refine.mk_msequent (mk "C" []) []
(* an option names a rule label: a select{"tok"} token term (options_boot.ml) *)
let lab s = Refiner.Refiner.TermOp.mk_token_term (Opname.make_opname [ "select"; "Perv" ]) (op s)

let arg attrs =
  { TacticInternalType.ref_goal = goal;
    ref_label = "main";
    ref_attributes = attrs;
    ref_bookmark = Mp_resource.empty_bookmark;
    ref_sentinal = Tactic.null_sentinal }

let cooked (name, a) =
  name ^ "=" ^ (match a with
    | TermArg t -> "term " ^ sp t
    | TermListArg ts -> "terms [" ^ String.concat "; " (List.map sp ts) ^ "]"
    | TypeArg t -> "type " ^ sp t
    | IntArg i -> "int " ^ string_of_int i
    | BoolArg b -> "bool " ^ string_of_bool b
    | StringArg s -> "string " ^ s
    | _ -> "other")

let input = [
  Tactic.term_attribute "x" (mk "a" []);
  Tactic.string_attribute "s" "v";
  Tactic.term_attribute "x" (mk "b" []);
  Tactic.term_list_attribute "l" [ mk "a" []; mk "b" [] ];
  Tactic.type_attribute "ty" (mk "T" []);
  Tactic.int_attribute "n" 3;
  Tactic.bool_attribute "flag" true;
  Tactic.addr_attribute "ad" (TermAddr.make_address [ Term_addr_sig.Subterm 1 ]);
  Tactic.term_attribute "ййallow" (lab "pa");
  Tactic.term_attribute "ййignore" (lab "pa");
  Tactic.term_attribute "ййexclude" (lab "pe");
  Tactic.term_attribute "allow" (lab "pold");
  Tactic.term_attribute "ййignore" (lab "pgone");
  Tactic.term_attribute "ййallow" (lab "pgone");
]

let line name l = Printf.printf "%-28s [%s]\n" name (String.concat "; " l)
let load raws = arg (TacticInternal.attribute_info_of_raw_attributes raws)
let save a = Tactic.raw_attributes a
let shown a = List.map cooked (Tactic.attributes a)
let allowed a labels = Options_boot.rule_labels_are_allowed (TacticInternal.get_options a) (Options_boot.rule_labels_of_terms (List.map lab labels))

let case name raws =
  Printf.printf "== %s: %d raw attributes\n" name (List.length raws);
  let a = load raws in
  line "loaded" (shown a);
  let a2 = load (save a) in
  Printf.printf "saved %d, saved then loaded:\n" (List.length (save a));
  line "" (shown a2);
  Printf.printf "same attributes %b, alpha equal with attributes %b\n" (shown a2 = shown a)
    (TacticInternal.tactic_arg_alpha_equal_with_attributes a a2);
  a, a2

let () =
  let _ = case "every kind" input in
  let _ = case "one option" [ Tactic.term_attribute "ййexclude" (lab "pe") ] in
  let a, a2 = case "allow pa, then exclude pe" [ Tactic.term_attribute "ййallow" (lab "pa"); Tactic.term_attribute "ййexclude" (lab "pe") ] in
  Printf.printf "rule labelled [pa; pe]: allowed %b, after save and load %b\n" (allowed a [ "pa"; "pe" ]) (allowed a2 [ "pa"; "pe" ]);
  let a3 = load (save a2) in
  Printf.printf "after a second save and load: allowed %b, alpha equal to the first %b\n" (allowed a3 [ "pa"; "pe" ])
    (TacticInternal.tactic_arg_alpha_equal_with_attributes a a3);
  let info = TacticInternal.attribute_info_of_raw_attributes input in
  let u = arg (TacticInternal.update_attributes info [ Tactic.int_attribute "m" 9 ]) in
  Printf.printf "update_attributes (no sentinel): saved %d, same attributes %b\n" (List.length (save u)) (shown u = shown (load input));
  Printf.printf "squash_attributes: saved %d\n" (List.length (save (arg (TacticInternal.squash_attributes info))));
  Printf.printf "empty: saved %d, %d attributes\n" (List.length (save (arg TacticInternal.empty_attribute))) (List.length (shown (arg TacticInternal.empty_attribute)))
