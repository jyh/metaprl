(* Constructs for the Filter_ocaml pin that the tree itself uses rarely. *)
open List
module M = Map.Make (String)
module N = Set.Make (struct type t = int let compare = compare end)
module type S = sig type t val f : t -> t end
module F (X : S) = struct let g x = X.f (X.f x) end
module rec R1 : sig val v : int end = struct let v = 1 end
include struct let inc = 2 end
type 'a tree = Leaf | Node of 'a tree * 'a * 'a tree
type r = { a : int; mutable b : string }
type v = [ `A | `B of int ]
type 'a ab = 'a constraint 'a = int
exception E of int * string
external ident : 'a -> 'a = "%identity"
let qualified = String.length "abc" + List.length [1; 2]
let deep = Lm_symbol.add "x"
let rec fact n = if n <= 1 then 1 else n * fact (n - 1)
let rf = { a = 1; b = "x" }
let rw = { rf with a = 2 }
let fld = rf.a + rw.M.a
let () = rf.b <- "y"
let arr = [| 1; 2; 3 |]
let ai = arr.(0) + Char.code "abc".[1]
let () = arr.(1) <- 4
let tup (x, y) = x + y
let lbl = opt ~y:2 ()
let poly : 'a. 'a -> 'a = fun x -> x
let pv = function `A -> 0 | `B n -> n
let mt = match Leaf with Leaf -> 0 | Node (_, x, _) when x > 0 -> x | Node _ -> -1
let tr = try fact 3 with E (n, _) -> n | Not_found -> 0
let lp = for i = 0 to 3 do ignore i done; let k = ref 0 in while !k < 3 do incr k done
let seq = print_string "a"; print_string "b"
let lm = let module L = List in L.length []
let lop = let open List in length []
let lazy_v = lazy (fact 5)
let asr_v = assert true
let cast = (1 : int)
let coerce = ((object method m = 1 end) :> < m : int >)
class c x = object val mutable v = x method get = v method set y = v <- y end
class type ct = object method get : int end
let o = new c 1
let send = o#get
let objv = object (self) method m = 1 method n = self#m end
let fm (module X : S with type t = int) = X.f 1
let pk = (module struct type t = int let f x = x end : S with type t = int)
let ch = 'a'
let fl = 1.5
let i32 = 3l
let i64 = 3L
let nat = 3n
let str = "s\n\t"
let cons = 1 :: 2 :: []
let unit_v = ()
let andb = true && false || not true
let pa = function (a, _) as p -> fst p + a
let range = function 'a' .. 'z' -> 1 | _ -> 0
let recp { a; b = _ } = a
let arrp = function [| x; _ |] -> x | _ -> 0
(* Not covered, found by the pin: the camlp5 7 filter overflows the stack on
 * an optional argument with a default, "let opt ?(x = 1) ~y () = x + y";
 * the camlp5 7 parser rejects "type ext = .." and "match ... with exception". *)
