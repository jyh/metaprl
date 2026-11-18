(* Jordering.nodups (refiner/reflib/jordering.ml), the merge function JProver
   passes to every PMap.union of its position maps (jall.ml).  The maps it
   joins never share a key, so no prover test ever called it (2026-11-15
   profile).  Pinned by a direct call: equal values give the value, unequal
   ones raise Invalid_argument "no dupes allowed in map"; the key is not
   looked at.
   Not reached here, and why: jall.ml's ftree_eq and rule_eq; they are
   internal to the JProver functor (not in jall.mli), and their callers are
   proof-permutation paths no prover test takes.
   The expected file is the output of the code as written, never typed. *)
let show name f =
  Printf.printf "%-36s %s\n" name (try f () with Invalid_argument s -> "Invalid_argument " ^ s)

let () =
  show "nodups k 3 3" (fun () -> string_of_int (Jordering.nodups "k" 3 3));
  show "nodups k 3 4" (fun () -> string_of_int (Jordering.nodups "k" 3 4));
  show "nodups k \"a\" \"a\"" (fun () -> Jordering.nodups "k" "a" "a");
  show "nodups (any key) [1; 2] [1; 2]" (fun () -> String.concat ";" (List.map string_of_int (Jordering.nodups () [ 1; 2 ] [ 1; 2 ])))
