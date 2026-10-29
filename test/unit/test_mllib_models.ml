(* mllib modules against plain OCaml, from a fixed LCG; per check, how
   many cases differ and the first:
   - Sort.list (OCaml 4.07's Sort, kept in mllib) against List.stable_sort
     on (key, tag) pairs ordered by key, so stability shows; Sort.array
     against Array.stable_sort by key only (it is deprecated for
     Array.sort, which is not stable); Sort.merge of two sorted lists;
   - List_neq_append, an accumulator that keeps a list appended twice
     (the same physical list) once: to_list of cons and append gives the
     elements in reverse order of insertion (no order is documented; this
     records it), and append x x gives x's elements once;
   - Flist: first, last, singleton of a list built by create and append;
   - Permutations, as its interface states: permute_list (get_permut l l') l'
     is in l's order, for l' a permutation of a list of distinct
     elements; id_perm leaves a list. *)
let seed = ref 131
let rnd n = seed := (!seed * 1103515245 + 12345) land 0x3fffffff; (!seed lsr 12) mod n
let report name n bad first =
  Printf.printf "%s: %d of %d differ%s\n" name bad n (if bad = 0 then "" else " (first: " ^ first ^ ")")
let run name n case =
  seed := 131;
  let bad = ref 0 and first = ref "" in
  for _ = 1 to n do
    match case () with true, _ -> () | false, d -> incr bad; if !first = "" then first := d ()
  done;
  report name n !bad !first
let ints l = "[" ^ String.concat ";" (List.map string_of_int l) ^ "]"
let pairs l = "[" ^ String.concat ";" (List.map (fun (k, t) -> Printf.sprintf "%d.%d" k t) l) ^ "]"

let () =
  let le (a, _) (b, _) = a <= b and cmp (a, _) (b, _) = compare a b in
  let gen () = List.init (rnd 20) (fun t -> (rnd 6, t)) in
  run "Sort.list against List.stable_sort" 2000 (fun () ->
      let l = gen () in
      let got = Sort.list le l and want = List.stable_sort cmp l in
      got = want, (fun () -> pairs l ^ " -> " ^ pairs got));
  run "Sort.array against Array.stable_sort" 2000 (fun () ->
      let a = Array.of_list (gen ()) in
      let b = Array.copy a and c = Array.copy a in
      Sort.array le b; Array.stable_sort cmp c;
      Array.map fst b = Array.map fst c, (fun () -> pairs (Array.to_list a) ^ " -> " ^ pairs (Array.to_list b)));
  run "Sort.merge of two sorted lists" 2000 (fun () ->
      let a = List.stable_sort cmp (gen ()) and b = List.stable_sort cmp (gen ()) in
      let got = Sort.merge le a b and want = List.stable_sort cmp (a @ b) in
      got = want, (fun () -> pairs a ^ " + " ^ pairs b ^ " -> " ^ pairs got));
  run "List_neq_append: to_list (append a b) is rev (a @ b); append x x is x" 2000 (fun () ->
      let build l = List.fold_right List_neq_append.cons l List_neq_append.nil in
      let a = List.init (rnd 6) (fun _ -> rnd 9) and b = List.init (rnd 6) (fun _ -> rnd 9) in
      let got = List_neq_append.to_list (List_neq_append.append (build a) (build b)) in
      let x = build a in
      let twice = List_neq_append.to_list (List_neq_append.append x x) in
      got = List.rev (a @ b) && twice = List_neq_append.to_list x,
      (fun () -> ints a ^ " @ " ^ ints b ^ " -> " ^ ints got ^ "; twice " ^ ints twice));
  run "Flist: first, last, singleton after create and append" 2000 (fun () ->
      let l = List.init (1 + rnd 8) (fun _ -> rnd 9) in
      let f = List.fold_left (fun acc x -> Flist.append acc (Flist.create x)) (Flist.create (List.hd l)) (List.tl l) in
      let ok = Flist.first f = List.hd l && Flist.last f = List.nth l (List.length l - 1)
               && Flist.singleton f = (List.length l = 1) in
      ok, (fun () -> ints l));
  run "Permutations: permute_list (get_permut l l') l' is l; id_perm" 2000 (fun () ->
      let n = rnd 8 in
      let l = List.init n (fun i -> i * 10) in
      let l' = List.map snd (List.sort compare (List.map (fun x -> (rnd 1000, x)) l)) in
      let got = (try Permutations.permute_list (Permutations.get_permut l l') l' with e -> [ -1; Hashtbl.hash (Printexc.to_string e) ]) in
      let id = (try Permutations.permute_list (Permutations.id_perm n) l = l with _ -> false) in
      got = l && id, (fun () -> ints l ^ " / " ^ ints l' ^ ": got " ^ ints got))
