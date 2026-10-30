(* Weak_memo (mllib), the hash-consing table under the refiner's TermNorm:
   a term added after one of its subterms was collected must get the same
   index every time.  The subterm leaf is hash-consed, dropped and
   collected; then g{leaf} is added three times.  Weak_memo.lookup finds
   leaf's entry with its value collected and makes the value again in the
   same slot; the first add sees that remade value under a new
   descriptor, while the table entry keeps the old one, so a header that
   names leaf differs between the first add of g{leaf} and the later ones
   (headers compare subterm descriptors with ==).  It prints
   TermNorm.compare_terms of the first and second add, and of the second
   and third (0 = the same index). *)
open Refiner.Refiner.Term
module N = Refiner.Refiner.TermNorm

let op s = Opname.make_opname [ s ]
let leaf () = mk_simple_term (op "leaf") []
let g a = mk_simple_term (op "g") [ a ]

let () =
  ignore (N.add (leaf ()));
  Gc.full_major ();
  Gc.full_major ();
  let p1 = N.add (g (leaf ())) in
  let p2 = N.add (g (leaf ())) in
  let p3 = N.add (g (leaf ())) in
  Printf.printf "g{leaf} after leaf was collected: first and second add same index %b, second and third %b\n"
    (N.compare_terms p1 p2 = 0) (N.compare_terms p2 p3 = 0)
