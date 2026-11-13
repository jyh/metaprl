(* unit-link: filter *)
(* unit-native: camlp5/o_keywords.cmx camlp5/pa_o.cmx camlp5/pr_o.cmx *)
(*
 * Filter_ocaml (filter/base): OCaml syntax to terms and back.  Each item is
 * parsed by camlp5's OCaml parser (pa_o), turned into a term
 * (term_of_str_item / term_of_sig_item), back into syntax
 * (str_item_of_term / sig_item_of_term), and both are printed by camlp5's
 * OCaml printer (pr_o, on one line).  "same" means the round trip prints
 * what was parsed.  pa_o and pr_o are native objects only, hence line 2.
 *
 * The only other check of this module is the manual camlp5 parity pin
 * (filter/test/pin_filter_ocaml.ml), and no theory build or census reaches
 * 2,341 of its 2,639 points (bisect, 008a9607e).
 *
 * The expected file is the output of the code, so it records the items
 * whose way back fails today (RAISES).  filter_ocaml also prints a line to
 * stderr for each of those; stdout is flushed after every item so the two
 * keep their order.
 *)
module F = Filter_ocaml.FilterOCaml (Refiner.Refiner)

let parse_str s = fst (List.hd (fst (Pcaml.parse_implem (Stream.of_string s))))
let pr_str si = Eprinter.apply Pcaml.pr_str_item Pprintf.empty_pc si

let parse_sig s = fst (List.hd (fst (Pcaml.parse_interf (Stream.of_string s))))
let pr_sig si = Eprinter.apply Pcaml.pr_sig_item Pprintf.empty_pc si

let one_line s = String.concat " " (List.filter (( <> ) "") (List.map String.trim (String.split_on_char '\n' s)))

let rec str s =
   flush stdout; str1 s; flush stdout
and str1 s =
   match parse_str s with
      exception e -> Printf.printf "PARSE %s: %S\n" (Printexc.to_string e) s
    | si ->
         let a = one_line (pr_str si) in
         match F.str_item_of_term (F.term_of_str_item [] si) with
            si' -> let b = one_line (pr_str si') in
               if a = b then Printf.printf "same      %s\n" a else Printf.printf "DIFFERS   %s\n       ->  %s\n" a b
          | exception e -> Printf.printf "RAISES    %s\n       ->  %s\n" a (match e with Filter_ocaml.FormatError (m, _) -> "FormatError " ^ m | e -> Printexc.to_string e)

let rec sg s =
   flush stdout; sg1 s; flush stdout
and sg1 s =
   match parse_sig s with
      exception e -> Printf.printf "PARSE %s: %S\n" (Printexc.to_string e) s
    | si ->
         let a = one_line (pr_sig si) in
         match F.sig_item_of_term (F.term_of_sig_item si) with
            si' -> let b = one_line (pr_sig si') in
               if a = b then Printf.printf "same      %s\n" a else Printf.printf "DIFFERS   %s\n       ->  %s\n" a b
          | exception e -> Printf.printf "RAISES    %s\n       ->  %s\n" a (match e with Filter_ocaml.FormatError (m, _) -> "FormatError " ^ m | e -> Printexc.to_string e)

let () =
   List.iter str [
      "let x = 1 + 2;;"; "let rec f n = if n = 0 then 1 else n * f (n - 1);;";
      "let rec f x = g x and g x = f x;;"; "let rec a x = x and b x = x and c x = x;;"; "let h () = let rec f x = g x and g x = f x in f 1;;"; "class c = let rec f x = g x and g x = f x in object method m = f 1 end;;";
      "let f (x, y) = match x with Some z when z > 0 -> z | Some _ | None -> y;;";
      "let f = fun x -> function [] -> x | h :: _ -> h;;";
      "let g ~y = y;;"; "let g ~y:z = z;;"; "let g ?(x = 1) ~y z = x + y + z;;"; "let h = f ~y:1 ?x:None;;";
      "let s = \"a\" ^ String.make 2 'c';;";
      "let a = [| 1; 2 |].(0) and b = \"xy\".[1];;"; "let r = { a = 1; b = \"s\" }.a;;";
      "let r' = { r with a = 2 };;"; "let u = (1 : int);;"; "let l = lazy 3;;";
      "let e = try raise Not_found with Not_found -> 0 | _ -> 1;;";
      "let w = while true do () done; for i = 1 to 3 do print_int i done;;";
      "let v = `A 3;;"; "let q = M.x + M.N.y;;"; "let o = object method m = 1 end;;";
      "let pa = function `A -> 0 | _ -> 1;;"; "let pv = function `A -> 0 | `B n -> n;;"; "let pw = function `C (x, y) -> x + y;;"; "type t = < m : int; n : string >;;"; "type t = < m : int; .. >;;"; "let coerce = ((object method m = 1 end) :> < m : int >);;";
      "let a = x.contents <- 2;;"; "let s = let open List in length [];;";
      "let f () = let a = 1 and b = 2 in a + b;;"; "let f () = let a, b = 1, 2 and c = 3 and d = 4 in a + b + c + d;;";
      "type t = int;;"; "type t = A;;"; "type t = A | B of int * string;;"; "type 'a t = 'a list;;";
      "type t = { a : int; mutable b : string };;"; "type t = [ `A | `B of int ];;"; "type t = int -> string;;";
      "type t = (int * string) option;;"; "type ('a, 'b) t = 'a * 'b;;"; "type +'a t = 'a;;"; "type _ t = A : int t | B : 'a -> 'a t;;";
      "exception E;;"; "exception F of int;;"; "external f : int -> int = \"c_f\";;";
      "module M = struct let x = 1 end;;"; "module M = F (G);;"; "module F (X : S) = struct end;;";
      "module type S = sig val x : int end;;"; "open List;;"; "include M;;";
      "class c = object val x = 1 method m = x end;;"; "let o = object (self) method m = 1 method n = self#m end;;";
      "class c (x : int) = object method m = x end;;"; "class type ct = object method m : int end;;";
      "let r = ({ a = 1 } : t);;";
      "let s = (a; b; c);;";
      "let c = (x :> t);;";
      "let c = (x : t :> u);;";
      "let a = assert (x > 0);;";
      "let m = let module N = M in N.x;;";
      "let p = (module M : S);;";
      "let f (module X : S) = X.x;;";
      "let u = M.(x + y);;";
      "type t += A;;";
      "type t += B of int;;";
      "exception E = F;;";
      "let x = 1 [@@inline];;";
      "let y = (f x [@attr]);;";
      "module type T = S with type t = int;;";
      "module type F = functor (X : S) -> T;;";
      "module type U = sig module M : S end;;";
      "module M : S = struct end;;";
      "module N = (val m : S);;";
      "module N = (val m);;";
      "type t = private int;;";
      "type t = { a : int } [@@deriving show];;";
      "type 'a t = 'a constraint 'a = int;;";
      "let f x = match x with A | B -> 1 | C _ -> 2 | exception E -> 3;;";
      "let l = [1; 2; 3];;";
      "let a = [| |];;";
      "let s = \"x\".[0] <- c;;";
      "let f = fun (type a) (x : a) -> x;;";
      "let g : type a. a -> a = fun x -> x;;";
      "let h = function x :: (_ :: _ as t) -> t | _ -> [];;";
      "let q = f ?x ~y;;";
      "let o = x#m 1;;";
      "let r = x.contents;;";
      "let w = for i = 10 downto 1 do () done;;";
      "let e = { M.a = 1 };;";
      "let z = `A (1, 2);;";
      "let i = 0x1F + 0o7 + 0b1;;";
      "let c = '\\n';;";
      "let f = 1.5e3;;";
      "include struct let x = 1 end;;";
      "open! List;;";
      "module rec A : S = struct end and B : T = struct end;;";
      "let () = ();;";
      "let f (g : x:int -> int) = g ~x:1;;";
      "type t = ?x:int -> unit -> int;;";
      "let f { a = x; b } = x;;";
      "let f { M.a = x; _ } = x;;";
      "let f [| x; y |] = x;;";
      "class virtual c = object val virtual x : int method virtual m : int end;;";
      "class type ct = object method virtual m : int end;;";
      "class type ct = object val mutable x : int method private m : int end;;";
      "module type T = S with module M = N;;";
      "module type T = S with type t := int;;";
      "module type T = S with type 'a t = 'a list;;";
      "let b = a.{1};;";
      "let b = a.{1, 2};;";
      "type t = M.t;;";
      "type t = int M.t;;";
      "type t = (int, string) M.N.t;;";
      "class c = object inherit [int] d end;;";
      "class c : [int] ct = object end;;";
      "let x = [%ext 1];;";
      "module M = F (struct end);;";
      "module type T = functor (X : S) -> S with type t = X.t;;";
      "let x : int = 1;;";
      "let f = function 'a' .. 'z' -> 1 | _ -> 0;;";
      "let f = function (x, y) as p -> p;;";
      "let f = function Some (A | B) -> 1 | _ -> 0;;";
      "let f = function M.A x -> x;;";
      "type t = { mutable a : int; b : float };;";
      "let x = - 1 + (- y);;";
      "let x = not (a && b || c);;";
      "let s = 'x' :: [];;";
      "let o = new c;;"; "let o = new M.c 1;;"; "class c = object val x = 1 method m = {< x = 2 >} end;;"; "class c = object method m = {< >} end;;"; "class c = let y = 1 in object method m = y end;;"; "class c = let rec f x = x in object method m = f 1 end;;";
   ];
   List.iter sg [
      "val x : int;;"; "type t;;"; "type 'a t = A of 'a;;"; "exception E of string;;";
      "module M : sig val x : int end;;"; "module type S = sig type t end;;"; "open M;;";
      "external f : int -> int = \"c_f\";;"; "class c : object method m : int end;;";
   ]
