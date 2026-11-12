(* Supinf (refiner/reflib), the parts of SupInf the proof census runs and
   the unit tests did not (2026-11-11 reach census: 35 lines after the AF
   and SAF tests): the Tree module that itt_supinf's source2hyp uses to
   assemble a proof from a source, the infinities of MakeAF, the
   conversion of forms back to terms, and the source setters.
     - Tree, on 2,000 random trees of integer leaves (with Ignore, Left,
       Right and Pair), against a model over the flattened leaves:
       treeMap f maps every leaf and keeps the shape; treeProduct f t1 t2
       has as leaves f a b for every leaf a of t1 and b of t2, t1-major,
       which is what itt_supinf's Ssum (a sum of two inequalities, each
       derived by cases) needs; leftBranch and rightBranch.  treeMergeLeft
       and treeMergeRight (the transitive steps) have no model here: fixed
       pairs are printed, with the leaves each result combines.
     - MakeAF: mk_number of the infinities, and add on infinities.
     - term_of for affine, min and max forms, over a field whose terms
       are plain terms (n/d, mul, add, max, min) and variables x1-x3;
       printed.
     - the sources set by extract2left/right, contradiction, hypothesis
       and the transitive steps; printed.
   The generator is a fixed linear congruential sequence, not Random. *)
open Refiner.Refiner.Term
open Supinf
open Supinf.Tree

let state = ref 97
let next () = state := (!state * 1103515245 + 12345) land 0x7fffffff; !state lsr 8
let pick n = next () mod n

let op s = Opname.make_opname [ s ]
let t0 s = mk_simple_term (op s) []
let t2 s a b = mk_simple_term (op s) [ a; b ]
let t1 s a = mk_simple_term (op s) [ a ]

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
  let term_of = function
    | Num (a, b) -> t0 (Printf.sprintf "%d/%d" a b)
    | MinusInfinity -> t0 "-oo" | PlusInfinity -> t0 "+oo"
  let mul_term = t2 "mul" let add_term = t2 "add" let neg_term = t1 "neg" let sub_term = t2 "sub"
  let inv_term = t1 "inv" let div_term = t2 "div" let ge_term = t2 "ge" let max_term = t2 "max" let min_term = t2 "min"
end

module Src = MakeSource (F)
module AF = MakeAF (F) (Src)
module SAF = MakeSAF (F) (Src) (AF)

let show_src s = let b = Buffer.create 32 in let out = Lm_printf.formatter_of_buffer b in Src.print out s; Lm_printf.pp_print_flush out (); Buffer.contents b
let show_af f = let b = Buffer.create 32 in let out = Lm_printf.formatter_of_buffer b in AF.print out f; Lm_printf.pp_print_flush out (); Buffer.contents b
let show_term = Simple_print.SimplePrint.string_of_term
let leaves t = "[" ^ String.concat " " (List.map string_of_int (treeFlatten t)) ^ "]"

let rec gen d =
  if d = 0 then (if pick 5 = 0 then Ignore else Leaf (pick 9 + 1))
  else match pick 6 with
    | 0 -> Ignore | 1 -> Leaf (pick 9 + 1) | 2 -> Left (gen (d - 1)) | 3 -> Right (gen (d - 1))
    | _ -> Pair (gen (d - 1), gen (d - 1))
let rec shape = function
  | Ignore -> "I" | Leaf _ -> "L" | Left t -> "l(" ^ shape t ^ ")" | Right t -> "r(" ^ shape t ^ ")"
  | Pair (a, b) -> "p(" ^ shape a ^ "," ^ shape b ^ ")"

let names = [| "treeMap: leaves mapped, shape kept"; "treeProduct: leaves f a b, t1-major";
               "leftBranch/rightBranch" |]
let tried = Array.make 3 0 and ok = Array.make 3 0 and first = Array.make 3 None
let note k b what = tried.(k) <- tried.(k) + 1; if b then ok.(k) <- ok.(k) + 1 else if first.(k) = None then first.(k) <- Some what

let () =
  for _ = 1 to 2000 do
    let t1 = gen 3 and t2 = gen 3 in
    let s = string_of_tree t1 ^ " x " ^ string_of_tree t2 in
    let m = treeMap (fun x -> 10 * x) t1 in
    note 0 (treeFlatten m = List.map (fun x -> 10 * x) (treeFlatten t1) && shape m = shape t1) s;
    let p = treeProduct (fun a b -> 100 * a + b) t1 t2 in
    let want = List.concat_map (fun a -> List.map (fun b -> 100 * a + b) (treeFlatten t2)) (treeFlatten t1) in
    note 1 (treeFlatten p = want) (s ^ ": " ^ leaves p);
    let br f = try Some (f t1) with Invalid_argument _ -> None in
    let wl, wr = match t1 with
      | Ignore -> Some Ignore, Some Ignore | Leaf _ -> None, None
      | Left a -> Some a, Some Ignore | Right a -> Some Ignore, Some a | Pair (a, b) -> Some a, Some b in
    note 2 (br leftBranch = wl && br rightBranch = wr) s
  done;
  Array.iteri (fun k name ->
      Printf.printf "%-40s %4d of %4d\n" name ok.(k) tried.(k);
      match first.(k) with None -> () | Some w -> Printf.printf "  first difference: %s\n" w) names;
  print_endline "== treeMergeLeft / treeMergeRight (leaves a*100+b)";
  let pairs = [
    Leaf 1, Leaf 2;
    Leaf 1, Left (Leaf 2);
    Leaf 1, Right (Leaf 2);
    Left (Leaf 1), Pair (Leaf 2, Leaf 3);
    Right (Leaf 1), Pair (Leaf 2, Leaf 3);
    Pair (Leaf 1, Leaf 2), Pair (Leaf 3, Leaf 4);
    Pair (Leaf 1, Ignore), Leaf 3;
    Pair (Ignore, Leaf 2), Leaf 3;
    Pair (Leaf 1, Leaf 2), Leaf 3;
    Pair (Leaf 1, Leaf 2), Left (Leaf 3);
    Pair (Leaf 1, Leaf 2), Right (Leaf 3);
    Ignore, Leaf 1;
    Leaf 1, Ignore;
    Left (Leaf 1), Leaf 2;
  ] in
  let merge f a b = try let t = f (fun a b -> 100 * a + b) a b in string_of_tree t ^ " " ^ leaves t with Invalid_argument s -> "Invalid_argument: " ^ String.trim s in
  List.iter (fun (a, b) ->
      Printf.printf "%s, %s\n   left  %s\n   right %s\n" (string_of_tree a ^ leaves a) (string_of_tree b ^ leaves b)
        (merge treeMergeLeft a b) (merge treeMergeRight a b)) pairs;
  print_endline "== AF infinities";
  let pinf = AF.mk_number F.plusInfinity and minf = AF.mk_number F.minusInfinity and one = AF.mk_number (F.Num (1, 1)) in
  Printf.printf "mk_number +oo: isPlusInfinity %b · mk_number -oo: isMinusInfinity %b\n" (AF.isPlusInfinity pinf) (AF.isMinusInfinity minf);
  let add a b = try show_af (AF.add a b) with Invalid_argument s -> "Invalid_argument: " ^ s in
  List.iter (fun (n, a, b) -> Printf.printf "%-10s = %s\n" n (add a b))
    [ "+oo + +oo", pinf, pinf; "-oo + -oo", minf, minf; "+oo + -oo", pinf, minf; "-oo + +oo", minf, pinf;
      "+oo + 1", pinf, one; "1 + -oo", one, minf ];
  print_endline "== term_of";
  let info = [| t0 "x1"; t0 "x2"; t0 "x3" |] in
  let v i = AF.mk_var i and k a = AF.mk_number (F.Num (a, 1)) in
  let f1 = AF.add (AF.scale (F.Num (2, 1)) (v 1)) (k 3) in
  let f2 = AF.add (v 2) (AF.scale (F.Num (-1, 1)) (v 3)) in
  let f0 = AF.sub (v 1) (v 1) in
  List.iter (fun (n, f) -> Printf.printf "AF %-14s %s\n" n (show_term (AF.term_of info f)))
    [ "2*x1 + 3", f1; "x2 - x3", f2; "x1 - x1", f0; "5", k 5; "x3", v 3 ];
  let a1 = SAF.affine f1 and a2 = SAF.affine f2 in
  List.iter (fun (n, f) -> Printf.printf "SAF %-13s %s\n" n (show_term (SAF.term_of info f)))
    [ "affine", a1; "max", SAF.max a1 a2; "min", SAF.min a1 a2; "min(max,_)", SAF.min (SAF.max a1 a2) a1 ];
  print_endline "== sources";
  let h = AF.hypSource 4 f1 in
  List.iter (fun (n, f) -> Printf.printf "%-22s %s\n" n (show_src (AF.getSource f)))
    [ "hypSource 4", h; "extract2leftSource 2", AF.extract2leftSource 2 h; "extract2rightSource 3", AF.extract2rightSource 3 h;
      "contrSource", AF.contrSource h f2; "setSource Signore", AF.setSource Src.Signore h ];
  let s1 = SAF.affine h and s2 = SAF.affine (AF.hypSource 7 f2) in
  List.iter (fun (n, f) -> Printf.printf "%-22s %s\n" n (show_src (SAF.getSource f)))
    [ "transitiveLeftSource", SAF.transitiveLeftSource s1 s2 1; "transitiveRightSource", SAF.transitiveRightSource 1 s1 s2 ];
  let m = SAF.min (SAF.affine pinf) a2 in
  Printf.printf "min(+oo, x2 - x3): isAffine %b, source %s\n" (SAF.isAffine m) (show_src (SAF.getSource m));
  let m = SAF.min (SAF.affine (AF.hypSource 9 pinf)) a2 in
  Printf.printf "min(+oo from hyp 9, x2 - x3): isAffine %b, source %s\n" (SAF.isAffine m) (show_src (SAF.getSource m))
