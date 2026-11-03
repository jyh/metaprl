(* Level expressions and primitive strings (refiner/term_gen/term_man_gen),
   which no unit test reached (2026-11-02 profile).  A level expression
   stands for max(c, v1 + o1, ..., vn + on) over variables that take
   natural numbers.  In term_std and term_ds:
     - on 3000 random expressions built from mk_const_level_exp,
       mk_var_level_exp, max_level_exp l1 l2 o (= max(l1, l2 + o)) and
       incr_level_exp (= l + 1), the level built has exactly the value of
       the expression under each of the 64 assignments of 0..3 to the
       variables u, v, w; and its variables are distinct and in increasing
       order, which level_le and level_lt rely on;
     - on 3000 pairs, level_le and level_lt are SOUND: when they say yes,
       the first is <= (resp. <) the second under every assignment.  They
       compare constant with constant and offset with offset, so they may
       say no where the values agree; the test counts those pairs and
       does not call them wrong;
     - mk_xstring_term s is a string term giving back s, and is_xstring_term
       and dest_xstring refuse a variable, another operator with a string,
       the string operator with a number, and the string operator with a
       subterm.
   The generator is a fixed linear congruential sequence, not Random. *)
let state = ref 3131
let next () = state := (!state * 1103515245 + 12345) land 0x7fffffff; !state lsr 8
let pick n = next () mod n

type e = C of int | V of string | Max of e * e * int | Incr of e
let rec gen d =
  match pick (if d = 0 then 2 else 5) with
  | 0 -> C (pick 4)
  | 1 -> V [| "u"; "v"; "w" |].(pick 3)
  | 2 | 3 -> Max (gen (d - 1), gen (d - 1), pick 3)
  | _ -> Incr (gen (d - 1))
let rec eval s = function
  | C c -> c | V v -> List.assoc v s
  | Max (a, b, o) -> max (eval s a) (eval s b + o) | Incr a -> eval s a + 1
let grid =
  List.concat_map (fun a -> List.concat_map (fun b -> List.map (fun c -> [ "u", a; "v", b; "w", c ]) [ 0; 1; 2; 3 ]) [ 0; 1; 2; 3 ]) [ 0; 1; 2; 3 ]
let rec show = function
  | C c -> string_of_int c | V v -> v
  | Max (a, b, o) -> Printf.sprintf "max(%s,%s+%d)" (show a) (show b) o | Incr a -> Printf.sprintf "(%s)+1" (show a)

module S (R : Refiner_sig.RefinerSig) = struct
  open R.Term
  open R.TermMan
  let rec build = function
    | C c -> mk_const_level_exp c | V v -> mk_var_level_exp (Lm_symbol.add v)
    | Max (a, b, o) -> max_level_exp (build a) (build b) o | Incr a -> incr_level_exp (build a)
  let vars l = List.map dest_level_var (dest_level l).le_vars
  let value s l =
    List.fold_left (fun m (lv : Term_sig.poly_level_exp_var) -> max m (List.assoc (Lm_symbol.to_string lv.le_var) s + lv.le_offset))
      (dest_level l).le_const (vars l)
  let rec ordered = function
    | (a : Term_sig.poly_level_exp_var) :: (b :: _ as t) -> not (Lm_symbol.eq a.le_var b.le_var) && a.le_var < b.le_var && ordered t
    | _ -> true

  let run name trees pairs =
    let n = List.length trees in
    let exact = List.filter (fun t -> let l = build t in List.for_all (fun s -> value s l = eval s t) grid) trees in
    let first_bad = List.find_opt (fun t -> let l = build t in not (List.for_all (fun s -> value s l = eval s t) grid)) trees in
    Printf.printf "%-48s %4d of %d%s\n" (name ^ ": the level has the expression's value") (List.length exact) n
      (match first_bad with None -> "" | Some t -> " (first: " ^ show t ^ ")");
    Printf.printf "%-48s %4d of %d\n" (name ^ ": variables distinct and increasing")
      (List.length (List.filter (fun t -> ordered (vars (build t))) trees)) n;
    let np = List.length pairs in
    let tally cmp scmp =
      let yes = ref 0 and unsound = ref 0 and missed = ref 0 in
      List.iter (fun (a, b) ->
          let la = build a and lb = build b in
          let sem = List.for_all (fun s -> scmp (eval s a) (eval s b)) grid in
          if cmp la lb then (incr yes; if not sem then incr unsound) else if sem then incr missed) pairs;
      !yes, !unsound, !missed in
    List.iter (fun (nm, cmp, scmp) ->
        let yes, unsound, missed = tally cmp scmp in
        Printf.printf "%-48s %4d of %d (said yes %d; holds on the grid but said no %d)\n"
          (name ^ ": " ^ nm ^ " sound") (np - unsound) np yes missed)
      [ "level_le", level_le, ( <= ); "level_lt", level_lt, ( < ) ]

  let strings name =
    let ok = List.for_all (fun s -> let t = mk_xstring_term s in is_xstring_term t && dest_xstring t = s) [ ""; "a"; "a b"; "\"q\""; String.make 300 'x' ] in
    Printf.printf "%-48s %b\n" (name ^ ": mk_xstring_term round trip (5 strings)") ok;
    let sop = (dest_op (dest_term (mk_xstring_term "s")).term_op).op_name in
    let others = [
      "a variable", mk_var_term (Lm_symbol.add "x");
      "another operator with a string", mk_term (mk_op (Opname.make_opname [ "str" ]) [ make_param (Term_sig.String "s") ]) [];
      "the string operator with a number", mk_term (mk_op sop [ make_param (Term_sig.Number (Lm_num.num_of_int 1)) ]) [];
      "the string operator with a subterm", mk_term (mk_op sop [ make_param (Term_sig.String "s") ]) [ mk_bterm [] (mk_xstring_term "t") ] ] in
    List.iter (fun (what, t) ->
        Printf.printf "%-48s is_xstring %b, dest_xstring %s\n" (name ^ ": " ^ what) (is_xstring_term t)
          (try "gave " ^ dest_xstring t with R.RefineError.RefineError _ -> "refused" | e -> "raised " ^ Printexc.to_string e))
      others
end

module Std = S (Refiner_std.Refiner)
module Ds = S (Refiner_ds.Refiner)

let () =
  let trees = List.init 3000 (fun _ -> gen 4) in
  (* a third of the pairs put the first under the second by construction *)
  let pairs = List.init 3000 (fun _ ->
      let a = gen 3 in
      match pick 3 with
      | 0 -> a, (if pick 2 = 0 then Max (a, gen 2, pick 2) else Max (gen 2, a, pick 2))
      | 1 -> a, Incr a
      | _ -> a, gen 3) in
  let rec size = function C _ | V _ -> 1 | Max (a, b, _) -> 1 + size a + size b | Incr a -> 1 + size a in
  Printf.printf "%d expressions (mean size %.1f), %d pairs, %d assignments\n" (List.length trees)
    (float (List.fold_left (fun k t -> k + size t) 0 trees) /. 3000.) (List.length pairs) (List.length grid);
  Std.run "std" trees pairs; Std.strings "std";
  Ds.run "ds" trees pairs; Ds.strings "ds"
