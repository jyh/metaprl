(* Supinf.MakeSAF (refiner/reflib), the min/max forms under itt_supinf's
   SUP-INF procedure: an affine form, or the min or max of two such forms.
   The proof census runs 155 of supinf.ml's 437 points, the unit tests 59
   (2026-11-11 reach census).  The field mirrors itt_supinf's
   RationalBoundField, as test_supinf_af does.  On 3,000 random forms over
   the variables 1-3, built from affine forms (small integer coefficients)
   by SAF.min, SAF.max, SAF.scale (by -2..2) and SAF.add, against a model
   that evaluates both sides at 6 random integer points:
     - the form evaluates to min/max/scale/sum of its operands' values
       (a min or max of two non-affine forms of different kinds, or of two
       maxes in min, raises Invalid_argument "SAF.min: detected a mixture
       of min and max", from max as well; the model predicts when);
     - a variable occurs in the result only if it occurs in an operand,
       and it occurs whenever the model's value depends on it (two points
       that differ only in that variable give different values);
     - isAffine, and value_of of a constant result.
   And fixed cases: min and max with plus and minus infinity, and the
   sources recorded for min, max, scale and add, printed.  Pinned as found:
   SAF.max records Smin(s1,s2) as its source when one side is affine (it
   records Smax only for two maxes); itt_supinf's source2hyp treats Smin
   and Smax alike, so only the printed source and its debug trace differ.
   It prints each count with how many checks were made, and the first
   difference.  The generator is a fixed linear congruential sequence,
   not Random. *)
open Supinf

let state = ref 93
let next () = state := (!state * 1103515245 + 12345) land 0x7fffffff; !state lsr 8
let pick n = next () mod n

let rec gcd a b = if b = 0 then abs a else gcd b (a mod b)

module F = struct
  type bfield = Num of int * int | MinusInfinity | PlusInfinity
  let fieldUnit = Num (1, 1)
  let fieldZero = Num (0, 1)
  let plusInfinity = PlusInfinity
  let minusInfinity = MinusInfinity
  let isInfinite = function Num _ -> false | _ -> true
  let isNegative = function Num (a, b) -> a * b < 0 | PlusInfinity -> false | MinusInfinity -> true
  let mul a b = match a, b with Num (a1, a2), Num (b1, b2) -> Num (a1 * b1, a2 * b2) | _ -> invalid_arg "mul"
  let add a b = match a, b with Num (a1, a2), Num (b1, b2) -> Num (a1 * b2 + a2 * b1, a2 * b2) | _ -> invalid_arg "add"
  let neg = function Num (a, b) -> Num (-a, b) | PlusInfinity -> MinusInfinity | MinusInfinity -> PlusInfinity
  let sub a b = add a (neg b)
  let inv = function Num (a, b) -> Num (b, a) | _ -> invalid_arg "inv"
  let div a b = mul a (inv b)
  let compare a b = match a, b with
    | Num (a1, a2), Num (b1, b2) -> Stdlib.compare (a1 * b2 * (if a2 * b2 < 0 then -1 else 1)) (b1 * a2 * (if a2 * b2 < 0 then -1 else 1))
    | MinusInfinity, MinusInfinity | PlusInfinity, PlusInfinity -> 0
    | MinusInfinity, _ | _, PlusInfinity -> -1
    | _ -> 1
  let print out = function
    | Num (a, b) -> Lm_printf.fprintf out "%d/%d" a b
    | MinusInfinity -> Lm_printf.fprintf out "-oo" | PlusInfinity -> Lm_printf.fprintf out "+oo"
  let no _ = invalid_arg "term_of: not used here"
  let term_of = no
  let mul_term _ = no let add_term _ = no let neg_term = no let sub_term _ = no
  let inv_term = no let div_term _ = no let ge_term _ = no let max_term _ = no let min_term _ = no
end

module Src = MakeSource (F)
module AF = MakeAF (F) (Src)

(* The model: reduced rationals (n, d), d > 0, per variable 0-3. *)
let norm (n, d) = if n = 0 then (0, 1) else let g = gcd n d * (if d < 0 then -1 else 1) in (n / g, d / g)
let radd (a, b) (c, d) = norm (a * d + c * b, b * d)
let rmul (a, b) (c, d) = norm (a * c, b * d)
let of_f = function F.Num (a, b) -> norm (a, b) | _ -> (max_int, 1)

module SAF = MakeSAF (F) (Src) (AF)

let norm (n, d) = if n = 0 then (0, 1) else let g = gcd n d * (if d < 0 then -1 else 1) in (n / g, d / g)
let of_f = function F.Num (a, b) -> norm (a, b) | _ -> invalid_arg "of_f: infinite"
let rcmp (a, b) (c, d) = compare (a * d) (c * b)
let rmin x y = if rcmp x y <= 0 then x else y
let rmax x y = if rcmp x y >= 0 then x else y

(* the value of an affine form at a point (point.(0) is 1, the constant) *)
let af_val f pt =
  let acc = ref (0, 1) in
  for v = 0 to 3 do
    let (n, d) = of_f (AF.coef f v) in
    let (a, b) = !acc in acc := norm (a * d + n * pt.(v) * b, b * d)
  done; !acc
let rec saf_val (_, f) pt =
  match f with
  | SAF.Affine a -> af_val a pt
  | SAF.Min (x, y) -> rmin (saf_val x pt) (saf_val y pt)
  | SAF.Max (x, y) -> rmax (saf_val x pt) (saf_val y pt)

(* the model of a generated form: its value at a point, the variables in
   its operands' leaves, and its kind as the code will see it *)
type kind = KAff | KMin | KMax
let kind_of (_, f) = match f with SAF.Affine _ -> KAff | SAF.Min _ -> KMin | SAF.Max _ -> KMax

exception Mixture
let rec gen d : SAF.saf * ((int array -> int * int)) * bool array * string =
  let leaf () =
    let cs = Array.init 4 (fun i -> if i = 0 || pick 2 = 0 then pick 7 - 3 else 0) in
    let f = ref (AF.mk_number (F.Num (cs.(0), 1))) in
    for v = 1 to 3 do if cs.(v) <> 0 then f := AF.add !f (AF.scale (F.Num (cs.(v), 1)) (AF.mk_var v)) done;
    let s = String.concat " + " (Printf.sprintf "%d" cs.(0) :: List.filter_map (fun v -> if cs.(v) <> 0 then Some (Printf.sprintf "%d*v%d" cs.(v) v) else None) [ 1; 2; 3 ]) in
    SAF.affine !f, (fun pt -> norm (Array.fold_left (+) 0 (Array.mapi (fun i c -> c * pt.(i)) cs), 1)),
    Array.map (fun c -> c <> 0) cs, "(" ^ s ^ ")"
  in
  if d = 0 then leaf () else
  let both op name =
    let (f1, m1, o1, s1) = gen (d - 1) in let (f2, m2, o2, s2) = gen (d - 1) in
    let k1 = kind_of f1 and k2 = kind_of f2 in
    let want = if name = "min" then KMin else KMax in
    if k1 <> KAff && k2 <> KAff && not (k1 = want && k2 = want) then raise Mixture;
    let r = op f1 f2 in
    let mf = if name = "min" then (fun pt -> rmin (m1 pt) (m2 pt)) else if name = "max" then (fun pt -> rmax (m1 pt) (m2 pt)) else (fun pt -> let (a, b) = m1 pt and (c, e) = m2 pt in norm (a * e + c * b, b * e)) in
    r, mf, Array.map2 (||) o1 o2, Printf.sprintf "%s(%s, %s)" name s1 s2
  in
  match pick 6 with
  | 0 -> leaf ()
  | 1 | 2 -> both SAF.min "min"
  | 3 -> both SAF.max "max"
  | 4 -> let (f, m, o, s) = gen (d - 1) and k = pick 5 - 2 in
      SAF.scale (F.Num (k, 1)) f, (fun pt -> let (a, b) = m pt in norm (k * a, b)), (if k = 0 then Array.make 4 false else o), Printf.sprintf "%d*%s" k s
  | _ ->
      let (f1, m1, o1, s1) = gen (d - 1) in let (f2, m2, o2, s2) = gen (d - 1) in
      SAF.add f1 f2, (fun pt -> let (a, b) = m1 pt and (c, e) = m2 pt in norm (a * e + c * b, b * e)), Array.map2 (||) o1 o2, Printf.sprintf "(%s + %s)" s1 s2

let names = [| "value at 6 points = the model's"; "occurs v only if v occurs in an operand, and if the value depends on v";
               "a mixture raises exactly when the model says"; "value_of a constant result = its value" |]
let tried = Array.make 4 0 and ok = Array.make 4 0 and first = Array.make 4 None
let note k b what = tried.(k) <- tried.(k) + 1; if b then ok.(k) <- ok.(k) + 1 else if first.(k) = None then first.(k) <- Some what

let show_src s = let b = Buffer.create 32 in let out = Lm_printf.formatter_of_buffer b in Src.print out s; Lm_printf.pp_print_flush out (); Buffer.contents b
let show_saf f = let b = Buffer.create 32 in let out = Lm_printf.formatter_of_buffer b in SAF.print out f; Lm_printf.pp_print_flush out (); Buffer.contents b

let () =
  let n = 3000 and mixtures = ref 0 and affines = ref 0 in
  for _ = 1 to n do
    (* the model predicts a mixture by raising Mixture before calling the code;
       to check the code raises too, call it again on the same operands *)
    let st = !state in
    match (try `Ok (gen 4) with Mixture -> `Mix) with
    | `Mix ->
        incr mixtures;
        (* replay the same draw, letting the code run the mixed call *)
        state := st;
        let raised = ref false in
        (try
           let rec replay d =
             let leaf () = let (f, _, _, _) = gen 0 in f in
             if d = 0 then leaf () else
             match pick 6 with
             | 0 -> leaf ()
             | 1 | 2 -> let f1 = replay (d - 1) in let f2 = replay (d - 1) in SAF.min f1 f2
             | 3 -> let f1 = replay (d - 1) in let f2 = replay (d - 1) in SAF.max f1 f2
             | 4 -> let f = replay (d - 1) and k = pick 5 - 2 in SAF.scale (F.Num (k, 1)) f
             | _ -> let f1 = replay (d - 1) in let f2 = replay (d - 1) in SAF.add f1 f2
           in ignore (replay 4)
         with Invalid_argument _ -> raised := true);
        note 2 !raised "the model predicted a mixture and the code raised nothing"
    | `Ok (f, m, o, s) ->
        note 2 true "";
        if SAF.isAffine f then incr affines;
        let pts = List.init 6 (fun _ -> Array.init 4 (fun i -> if i = 0 then 1 else pick 11 - 5)) in
        note 0 (List.for_all (fun pt -> rcmp (saf_val f pt) (m pt) = 0) pts) s;
        let depends v = List.exists (fun pt -> let pt' = Array.copy pt in pt'.(v) <- pt.(v) + 1; rcmp (m pt) (m pt') <> 0) pts in
        note 1 (List.for_all (fun v -> (o.(v) || not (SAF.occurs v f)) && (not (depends v) || SAF.occurs v f)) [ 1; 2; 3 ]) s;
        if SAF.isAffine f && (match f with (_, SAF.Affine a) -> AF.isNumber a | _ -> false) then
          note 3 (rcmp (of_f (SAF.value_of f)) (m [| 1; 0; 0; 0 |]) = 0) s
  done;
  Printf.printf "%d forms: %d mixtures predicted, %d affine results\n" n !mixtures !affines;
  Array.iteri (fun k name ->
      Printf.printf "%-48s %5d of %5d\n" name ok.(k) tried.(k);
      match first.(k) with None -> () | Some w -> Printf.printf "  first difference: %s\n" w) names;
  print_endline "== infinities and sources";
  let h i f = SAF.setSource (Src.Shypothesis i) f in
  let x = h 1 (SAF.affine (AF.mk_var 1)) and three = h 2 (SAF.affine (AF.mk_number (F.Num (3, 1)))) in
  let five = h 3 (SAF.affine (AF.mk_number (F.Num (5, 1)))) in
  let pinf = h 4 (SAF.affine AF.plusInfinity) and minf = h 5 (SAF.affine AF.minusInfinity) in
  List.iter (fun (name, f) ->
      Printf.printf "%-24s %-30s source %s\n" name (show_saf f) (show_src (SAF.getSource f)))
    [ "min(v1, +oo)", SAF.min x pinf; "min(v1, -oo)", SAF.min x minf;
      "max(v1, +oo)", SAF.max x pinf; "max(v1, -oo)", SAF.max x minf;
      "min(3, 5)", SAF.min three five; "max(3, 5)", SAF.max three five;
      "min(v1, 3)", SAF.min x three; "max(v1, 3)", SAF.max x three;
      "max(max(v1,3), max(v1,5))", SAF.max (SAF.max x three) (SAF.max x five);
      "-2 * min(v1, 3)", SAF.scale (F.Num (-2, 1)) (SAF.min x three);
      "0 * max(v1, 3)", SAF.scale (F.Num (0, 1)) (SAF.max x three);
      "min(v1, 3) + 5", SAF.add (SAF.min x three) five ];
  Printf.printf "isPlusInfinity +oo %b · isMinusInfinity -oo %b · isInfinite v1 %b\n"
    (SAF.isPlusInfinity pinf) (SAF.isMinusInfinity minf) (SAF.isInfinite x)
