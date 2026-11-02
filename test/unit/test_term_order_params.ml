(* Term_order on parameters (refiner/reflib): compare_params, and through
   it compare_levels, compare_level_vars and compare_opparams, which no
   unit test reached (2026-11-02 profile).  On 400 generated parameters of
   every kind -- numbers, strings, tokens, variables, meta-variables of
   each sort, levels max(c, v+o, ...) and operator parameters -- it checks
   that compare_params is a total order:
     - compare a a = 0, and compare a b = 0 exactly when a and b are the
       same parameter (the same kind and the same parts, as dest_param and
       dest_level give them);
     - the sign of compare a b is minus the sign of compare b a;
     - it is transitive (on 20,000 random triples);
   and that the order puts the kinds in the order of its match, numbers
   first.  The generator is a fixed linear congruential sequence, not
   Random. *)
open Term_sig
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan

module O = Term_order.TermOrder (Refiner.Refiner)

let state = ref 9090
let next () = state := (!state * 1103515245 + 12345) land 0x7fffffff; !state lsr 8
let pick n = next () mod n

let sym () = Lm_symbol.add [| "a"; "b"; "c" |].(pick 3)
let level () =
  mk_level (pick 3) (List.filter_map (fun v -> if pick 2 = 0 then Some (mk_level_var (Lm_symbol.add v) (pick 3)) else None) [ "k"; "m" ])
let opname () = Opname.make_opname [ [| "f"; "g" |].(pick 2) ]
let rec gen depth =
  let p =
    match pick (if depth > 0 then 13 else 12) with
    | 0 -> Number (Lm_num.num_of_int (pick 5 - 2))
    | 1 -> String [| "x"; "y"; "" |].(pick 3)
    | 2 -> Token (opname ())
    | 3 -> Var (sym ())
    | 4 -> MNumber (sym ())
    | 5 -> MString (sym ())
    | 6 -> MToken (sym ())
    | 7 -> MShape (sym ())
    | 8 -> MOperator (sym ())
    | 9 | 10 -> MLevel (level ())
    | 11 -> Quote
    | _ -> Operator { opparam_name = opname (); opparam_params = List.init (pick 3) (fun _ -> gen (depth - 1)); opparam_arities = List.init (pick 2) (fun _ -> pick 2) }
  in
  make_param p

(* The parameter as its parts, for "the same parameter". *)
let rec parts p =
  let lv l =
    let { le_const; le_vars } = dest_level l in
    string_of_int le_const ^ "[" ^ String.concat "," (List.map (fun v -> let { le_var; le_offset } = dest_level_var v in Lm_symbol.string_of_symbol le_var ^ "+" ^ string_of_int le_offset) le_vars) ^ "]" in
  match dest_param p with
  | Number n -> "0 " ^ Lm_num.string_of_num n
  | String s -> "1 " ^ String.escaped s
  | Token t -> "2 " ^ String.concat "!" (Opname.dest_opname t)
  | Var v -> "3 " ^ Lm_symbol.string_of_symbol v
  | Operator op -> "5 " ^ String.concat "!" (Opname.dest_opname op.opparam_name) ^ "(" ^ String.concat "; " (List.map parts op.opparam_params) ^ ")" ^ String.concat "," (List.map string_of_int op.opparam_arities)
  | Quote -> "6"
  | MNumber v -> "7 " ^ Lm_symbol.string_of_symbol v
  | MString v -> "8 " ^ Lm_symbol.string_of_symbol v
  | MToken v -> "9 " ^ Lm_symbol.string_of_symbol v
  | MShape v -> "10 " ^ Lm_symbol.string_of_symbol v
  | MOperator v -> "11 " ^ Lm_symbol.string_of_symbol v
  | MLevel l -> "12 " ^ lv l
  | _ -> "?"
let kind p = int_of_string (List.hd (String.split_on_char ' ' (parts p)))

let sign x = compare x 0

let () =
  let n = 400 in
  let ps = Array.init n (fun _ -> gen 2) in
  let tried = Array.make 4 0 and ok = Array.make 4 0 and first = Array.make 4 None in
  let note k b what = tried.(k) <- tried.(k) + 1; if b then ok.(k) <- ok.(k) + 1 else if first.(k) = None then first.(k) <- Some (what ()) in
  let both a b () = parts a ^ "  vs  " ^ parts b in
  Array.iter (fun a -> note 0 (O.compare_params a a = 0) (both a a)) ps;
  Array.iter (fun a -> Array.iter (fun b ->
      let c = O.compare_params a b in
      note 1 ((c = 0) = (parts a = parts b)) (both a b);
      note 2 (sign c = - (sign (O.compare_params b a))) (both a b);
      if kind a < kind b then note 3 (c < 0) (both a b)) ps) ps;
  let trans = ref 0 and trans_ok = ref 0 and trans_first = ref None in
  for _ = 1 to 20000 do
    let a = ps.(pick n) and b = ps.(pick n) and c = ps.(pick n) in
    if O.compare_params a b <= 0 && O.compare_params b c <= 0 then begin
      incr trans;
      if O.compare_params a c <= 0 then incr trans_ok
      else if !trans_first = None then trans_first := Some (parts a ^ " <= " ^ parts b ^ " <= " ^ parts c)
    end
  done;
  let kinds = List.sort_uniq compare (Array.to_list (Array.map kind ps)) in
  Printf.printf "%d parameters of %d kinds (%d of them levels, %d operator parameters)\n" n (List.length kinds)
    (Array.fold_left (fun k p -> if kind p = 12 then k + 1 else k) 0 ps) (Array.fold_left (fun k p -> if kind p = 5 then k + 1 else k) 0 ps);
  List.iteri (fun k name ->
      Printf.printf "%-48s %6d of %6d\n" name ok.(k) tried.(k);
      match first.(k) with None -> () | Some w -> Printf.printf "  first difference: %s\n" w)
    [ "compare a a = 0"; "compare a b = 0 iff the same parameter"; "sign (compare a b) = - sign (compare b a)"; "kinds in the order of the match" ];
  Printf.printf "%-48s %6d of %6d\n" "transitive (a <= b <= c gives a <= c)" !trans_ok !trans;
  match !trans_first with None -> () | Some w -> Printf.printf "  first difference: %s\n" w
