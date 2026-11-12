(* Mp_resource (refiner/reflib), the paths test_mp_resource does not take
   and the proof census does (2026-11-11 reach census, 15 lines): an
   Imperative processor (make_proc_functional), improve_list, a theory
   whose first act extends a theory with Private items (so its data must
   be collected item by item rather than taken whole), and recompute_top,
   the resource of every closed theory, computed and then recomputed after
   another theory closes.  Two resources collect the same items, one
   Functional and one Imperative; each line prints what a bookmark sees
   (sorted), the visibility test_mp_resource's model gives (a theory sees
   its own items, public and private, and the public items of the theories
   it extends, transitively, each once), and "<- DIFFERS" if they differ.
     a: improve_list Public [1; 2], then Private 3
     b: extends a, then Public 10            c: Public 20, then extends a
     d: extends b, then extends c (a diamond on a)
     e: Private 40, Public 30 (closed after the first recompute_top)
   The top resource sees every closed theory's public items.  The order
   each processor returns (not part of the model) is printed as found. *)
open Mp_resource

let fget = create_resource "mpr_fun"
    (Functional { fp_empty = []; fp_add = (fun l (x : int) -> x :: l); fp_retr = (fun l -> l) })
let iget = create_resource "mpr_imp"
    (Imperative { imp_create = (fun () -> ref []); imp_add = (fun r (x : int) -> r := x :: !r); imp_retr = (fun r -> !r) })

let item pvt x = improve pvt "mpr_fun" (Obj.repr x); improve pvt "mpr_imp" (Obj.repr x)
let items pvt l = improve_list pvt "mpr_fun" (List.map Obj.repr l); improve_list pvt "mpr_imp" (List.map Obj.repr l)

let show l = "[" ^ String.concat "; " (List.map string_of_int (List.sort compare l)) ^ "]"
let line name bm want =
  let g = find bm in let f = show (fget g) and i = show (iget g) and w = show want in
  Printf.printf "%-6s functional %-22s imperative %-22s model %s%s\n" name f i w
    (if f = w && i = w then "" else "  <- DIFFERS")

let () =
  items Public [ 1; 2 ]; item Private 3; close_theory "mpr_a";
  extends_theory "mpr_a"; item Public 10; close_theory "mpr_b";
  item Public 20; extends_theory "mpr_a"; close_theory "mpr_c";
  extends_theory "mpr_b"; extends_theory "mpr_c"; close_theory "mpr_d";
  (* d first, so b, c and a are computed on demand, from d *)
  line "d" (theory_bookmark "mpr_d") [ 1; 2; 10; 20 ];
  line "a" (theory_bookmark "mpr_a") [ 1; 2; 3 ];
  line "b" (theory_bookmark "mpr_b") [ 1; 2; 10 ];
  line "c" (theory_bookmark "mpr_c") [ 1; 2; 20 ];
  recompute_top ();
  line "top" top_bookmark [ 1; 2; 10; 20 ];
  item Private 40; item Public 30; close_theory "mpr_e";
  line "e" (theory_bookmark "mpr_e") [ 30; 40 ];
  line "top" top_bookmark [ 1; 2; 10; 20 ];
  recompute_top ();
  line "top'" top_bookmark [ 1; 2; 10; 20; 30 ];
  let raw l = String.concat " " (List.map string_of_int l) in
  List.iter (fun (n, bm) -> let g = find bm in Printf.printf "order at %s: functional %s · imperative %s\n" n (raw (fget g)) (raw (iget g)))
    [ "a", theory_bookmark "mpr_a"; "d", theory_bookmark "mpr_d"; "top'", top_bookmark ];
  Printf.printf "parents of d: %s\n" (String.concat ", " (get_parents "mpr_d"))
