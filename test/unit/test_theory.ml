(* Theory (refiner/reflib), the registry every theory module records itself
   in at load time; the shell and the browser list theories from it. No
   unit test called it (the 11-02 reflib coverage page). record_theory
   pushes, get_theories lists the most recent first, get_theory finds a
   name (the most recent record when a name is recorded twice) and fails
   with a message naming it otherwise. Nothing in this test loads a
   theory, so the registry starts empty. *)
open Refiner.Refiner.Refine

let thy name group = { Theory.thy_name = name; thy_group = group; thy_groupdesc = group ^ " theories";
                       thy_refiner = refiner_of_build (null_refiner name) }
let names l = String.concat " " (List.map (fun t -> t.Theory.thy_name ^ "/" ^ t.Theory.thy_group) l)
let find n = try let t = Theory.get_theory n in t.Theory.thy_name ^ "/" ^ t.Theory.thy_group with Failure m -> "Failure " ^ m

let () =
  Printf.printf "get_theories, nothing recorded: [%s]\n" (names (Theory.get_theories ()));
  Printf.printf "get_theory a, nothing recorded: %s\n" (find "a");
  Theory.record_theory (thy "a" "g1");
  Theory.record_theory (thy "b" "g1");
  Theory.record_theory (thy "a" "g2");
  Printf.printf "get_theories after a/g1, b/g1, a/g2: [%s]\n" (names (Theory.get_theories ()));
  Printf.printf "get_theory a: %s\n" (find "a");
  Printf.printf "get_theory b: %s\n" (find "b");
  Printf.printf "get_theory c: %s\n" (find "c");
  Printf.printf "get_theory \"\": %s\n" (find "")
