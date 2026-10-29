(* mllib Bitset against a bool array: 2,000 random sizes up to 200, 50
   set/reset steps each, reading a random bit after each. *)
let seed = ref 127
let rnd n = seed := (!seed * 1103515245 + 12345) land 0x3fffffff; (!seed lsr 12) mod n
let () =
  let bad = ref 0 and first = ref "" and n = 2000 in
  for _ = 1 to n do
    let size = rnd 200 in
    let b = Bitset.create size and m = Array.make (max size 1) false in
    for _ = 1 to 50 do
      if size > 0 then begin
        let i = rnd size in
        (match rnd 2 with 0 -> Bitset.set b i; m.(i) <- true | _ -> Bitset.reset b i; m.(i) <- false);
        let j = rnd size in
        if Bitset.get b j <> m.(j) && !first = "" then first := Printf.sprintf "size %d bit %d" size j;
        if Bitset.get b j <> m.(j) then incr bad
      end
    done
  done;
  Printf.printf "bitset against a bool array: %d of %d reads differ%s\n" !bad (n * 50) (if !first = "" then "" else " (first: " ^ !first ^ ")")
