(* Supinf.MakeAF (refiner/reflib), the affine forms c0 + c1*v1 + ... under
   itt_supinf's SUP-INF procedure.  The field here mirrors itt_supinf's
   RationalBoundField: a fraction is a pair of integers, NOT reduced (1/2 +
   -1/2 is 0/4), and BField.compare compares values.  On 2,000 random forms
   over the variables 1-3 (0 is the constant), built from numbers and
   variables by scale, add, sub and remove, against a model (a map from
   variable to a reduced rational):
     - coef of every variable equals the model's (by BField.compare);
     - isNumber holds exactly when every variable's coefficient is zero;
     - value_of of a number is the model's constant;
     - split returns the largest variable with a nonzero coefficient (else
       the constant), its coefficient, and the form without it.
   It prints each count with how many checks were made, and the first
   difference.  (AF.value_of writes a message to stderr before it raises;
   stderr goes to the null device so the output is stdout alone.)  The generator is a fixed linear congruential sequence,
   not Random. *)
open Supinf

let state = ref 61
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

type m = (int * int) array
let rec gen d : AF.af * m * string =
  let leaf () =
    if pick 2 = 0 then let k = (pick 7 - 3, 1 + pick 2) in
      AF.mk_number (F.Num (fst k, snd k)), Array.init 4 (fun i -> if i = 0 then norm k else (0, 1)), Printf.sprintf "%d/%d" (fst k) (snd k)
    else let v = 1 + pick 3 in AF.mk_var v, Array.init 4 (fun i -> if i = v then (1, 1) else (0, 1)), Printf.sprintf "v%d" v in
  if d = 0 then leaf () else
  match pick 5 with
  | 0 -> let (f, m, s) = gen (d - 1) and k = (pick 5 - 2, 1 + pick 3) in
      AF.scale (F.Num (fst k, snd k)) f, Array.map (rmul (norm k)) m, Printf.sprintf "%d/%d*(%s)" (fst k) (snd k) s
  | 1 | 2 -> let (f1, m1, s1) = gen (d - 1) in let (f2, m2, s2) = gen (d - 1) in
      AF.add f1 f2, Array.map2 radd m1 m2, Printf.sprintf "(%s + %s)" s1 s2
  | 3 -> let (f1, m1, s1) = gen (d - 1) in let (f2, m2, s2) = gen (d - 1) in
      AF.sub f1 f2, Array.map2 (fun a (n, dd) -> radd a (-n, dd)) m1 m2, Printf.sprintf "(%s - %s)" s1 s2
  | _ -> let (f, m, s) = gen (d - 1) and v = 1 + pick 3 in
      AF.remove f v, Array.mapi (fun i c -> if i = v then (0, 1) else c) m, Printf.sprintf "remove(%s, v%d)" s v

let names = [| "coef = the model's, every variable"; "isNumber iff no variable's coefficient is nonzero";
               "value_of a number = the model's constant"; "split = largest nonzero variable, its coef, the rest" |]
let tried = Array.make 4 0 and ok = Array.make 4 0 and first = Array.make 4 None
let note k b what = tried.(k) <- tried.(k) + 1; if b then ok.(k) <- ok.(k) + 1 else if first.(k) = None then first.(k) <- Some what
let safe f = try Some (f ()) with _ -> None

let () =
  Unix.dup2 (Unix.openfile Filename.null [ Unix.O_WRONLY ] 0) Unix.stderr;
  let n = 2000 and numbers = ref 0 in
  for _ = 1 to n do
    let (f, m, s) = gen 4 in
    let coefs = Array.init 4 (fun v -> of_f (AF.coef f v)) in
    note 0 (coefs = m) s;
    let is_num = Array.for_all (fun c -> c = (0, 1)) (Array.sub m 1 3) in
    if is_num then incr numbers;
    note 1 (AF.isNumber f = is_num) (Printf.sprintf "%s: model %s" s (if is_num then "a number" else "not a number"));
    if is_num then note 2 (safe (fun () -> of_f (AF.value_of f)) = Some m.(0)) s;
    let rec top v = if v = 0 then 0 else if m.(v) <> (0, 1) then v else top (v - 1) in
    let v = top 3 in
    (match safe (fun () -> AF.split f) with
     | Some (c, v', rest) ->
         let rest_m = Array.init 4 (fun i -> if i = v then (0, 1) else of_f (AF.coef rest i)) in
         let want_rest = Array.mapi (fun i c -> if i = v then (0, 1) else c) m in
         note 3 (v' = v && of_f c = m.(v) && rest_m = want_rest) (Printf.sprintf "%s: split gave v%d" s v')
     | None -> note 3 false (s ^ ": split raised"))
  done;
  Printf.printf "%d forms, %d of them numbers\n" n !numbers;
  Array.iteri (fun k name ->
      Printf.printf "%-50s %5d of %5d\n" name ok.(k) tried.(k);
      match first.(k) with None -> () | Some w -> Printf.printf "  first difference: %s\n" w) names
