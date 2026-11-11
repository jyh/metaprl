(* Options_boot is the option table behind every select label: add_option
   with allow / exclude / ignore, list_options in insertion order,
   options_eq and rule_labels_are_allowed.  This test drives random add
   sequences over a few labels and compares the table against an
   association-list model (a later add of the same label replaces it and
   takes a new position; ignore removes it; every add advances the
   counter; a rule is allowed by the live label it carries with the
   latest position, and by default), then pins the string forms, the
   refusals, and the automatic select_crw label. *)
open Refiner.Refiner
open Options_boot

let select_opname = Opname.make_opname [ "select"; "Perv" ]
let mk_label_term = TermOp.mk_token_term select_opname
let get_label = TermOp.dest_token_term select_opname

let labels = Array.map (fun s -> Opname.make_opname [ s ]) [| "a"; "b"; "c"; "d"; "e" |]
let infos = [| OptionAllow; OptionExclude; OptionIgnore |]

let name_of t = Opname.string_of_opname (get_label t)
let show_info = function OptionAllow -> "allow" | OptionExclude -> "exclude" | OptionIgnore -> "ignore"

(* The model: (label, (index, allow)) kept in insertion order of the live entry. *)
let model_add (m, i) op info =
  let i = i + 1 in
  let m = List.remove_assoc op m in
  match info with
    OptionAllow -> m @ [ op, (i, true) ], i
  | OptionExclude -> m @ [ op, (i, false) ], i
  | OptionIgnore -> m, i

let model_list (m, _) =
  List.map (fun (op, (_, b)) -> Opname.string_of_opname op, (if b then "allow" else "exclude")) m

let real_list opts = List.map (fun (t, info) -> name_of t, show_info info) (list_options opts)

let () =
  Random.init 20261110;
  let agree = ref 0 and n = 1000 and eq_ok = ref 0 and allow_ok = ref 0 in
  for _ = 1 to n do
    let len = Random.int 12 in
    let opts = ref options_empty and m = ref ([], 0) in
    for _ = 1 to len do
      let op = labels.(Random.int (Array.length labels)) and info = infos.(Random.int 3) in
      opts := add_option !opts (mk_label_term op) info;
      m := model_add !m op info
    done;
    if real_list !opts = model_list !m then incr agree;
    (* rule_labels_are_allowed on a random label set, against the model. *)
    let rl = List.filter (fun _ -> Random.bool ()) (Array.to_list labels) in
    let expect =
      match List.sort compare (List.filter_map (fun op -> List.assoc_opt op (fst !m)) rl) with
        [] -> true
      | l -> snd (List.nth l (List.length l - 1)) in
    if rule_labels_are_allowed !opts (rule_labels_of_terms (List.map mk_label_term rl)) = expect then incr allow_ok;
    (* options_eq: reflexive, and false against one more allow of a fresh label. *)
    let more = add_option !opts (mk_label_term (Opname.make_opname [ "z" ])) OptionAllow in
    if options_eq !opts !opts && not (options_eq !opts more) then incr eq_ok
  done;
  Printf.printf "list_options agrees with the model: %d/%d\n" !agree n;
  Printf.printf "options_eq reflexive and separating: %d/%d\n" !eq_ok n;
  Printf.printf "rule_labels_are_allowed agrees with the model: %d/%d\n" !allow_ok n;
  (* Same live entries, different counters (an ignore of an absent label still advances it): not equal. *)
  let a1 = add_option options_empty (mk_label_term labels.(0)) OptionAllow in
  let a2 = add_option a1 (mk_label_term labels.(1)) OptionIgnore in
  Printf.printf "options_eq after an ignore of an absent label: %b (same list: %b)\n" (options_eq a1 a2) (real_list a1 = real_list a2);
  (* One sequence, printed: re-adding a label moves it to the end; ignore removes it. *)
  let s = List.fold_left (fun o (l, i) -> add_option o (mk_label_term labels.(l)) i) options_empty
      [ 0, OptionAllow; 1, OptionExclude; 2, OptionAllow; 0, OptionExclude; 1, OptionIgnore ] in
  List.iter (fun (a, b) -> Printf.printf "  %s %s\n" a b) (real_list s);
  (* The string forms (escaped: the legal strings carry a two-character prefix). *)
  Array.iter (fun i -> Printf.printf "string_of_option %s = \"%s\"\n" (show_info i) (String.escaped (string_of_option i))) infos;
  Array.iter (fun i -> Printf.printf "round trip %s: %b\n" (show_info i) (option_of_string (string_of_option i) = i)) infos;
  List.iter (fun s -> Printf.printf "option_of_string \"%s\" = %s, is_option_string %b\n" s (show_info (option_of_string s)) (is_option_string s))
    [ "allow"; "exclude"; "ignore" ];
  List.iter (fun s ->
      Printf.printf "option_of_string \"%s\": %s, is_option_string %b\n" s
        (try ignore (option_of_string s); "accepted" with RefineError.RefineError _ -> "refused") (is_option_string s))
    [ "Allow"; ""; "allowx" ];
  let check name l =
    Printf.printf "rule_labels_not_allowed %s: %s\n" name
      (try rule_labels_not_allowed Ploc.dummy l; "passes" with Ploc.Exc (_, RefineError.RefineError _) -> "refused") in
  check "None" None;
  check "[select_crw]" (Some [ mk_label_term (Opname.make_opname [ "select_crw"; "Perv" ]) ]);
  check "[a]" (Some [ mk_label_term labels.(0) ]);
  check "[select_crw; a]" (Some [ mk_label_term (Opname.make_opname [ "select_crw"; "Perv" ]); mk_label_term labels.(0) ]);
  Printf.printf "rule_labels_empty allowed by the empty table: %b\n" (rule_labels_are_allowed options_empty rule_labels_empty)
