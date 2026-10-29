(* The rest of mllib's plain modules against plain OCaml, from a fixed LCG:
   - Memo.Memo and Weak_memo.TheMemo: apply against g p (f p a), where the
     header is the argument modulo 50 (so the comparison merges arguments),
     with fresh boxed arguments so the physical-equality table misses;
     Memo.Memo computes g once per class of headers;
   - Weak_memo.TheWeakMemo: lookup/retrieve against the function, across
     forced major collections that clear the weak array and drive the
     slot-reuse and array-growth paths; while a descriptor is held, a second
     lookup of an equal header returns the same value (==) and descriptors
     compare 0 exactly when the headers are equal;
   - Line_buffer.LineBuffer: add/remove_last/last/length/fold/iter/clone
     against a list of the last 100 lines;
   - Line_buffer.LineTable: add/mem/find/fold against an association list of
     the 100 most recently added keys. Keys are added in increasing order
     and never re-added while the table is full: the table orders entries
     by Unix.gettimeofday, and two entries with the same time are ordered
     by key, which only agrees with insertion order when keys increase.
   Per check: how many cases differ, and the first. *)
let seed = ref 211
let rnd n = seed := (!seed * 1103515245 + 12345) land 0x3fffffff; (!seed lsr 12) mod n
let run name n case =
  seed := 211;
  let bad = ref 0 and first = ref "" in
  for i = 1 to n do
    match case i with true, _ -> () | false, d -> incr bad; if !first = "" then first := d ()
  done;
  Printf.printf "%s: %d of %d differ%s\n%!" name !bad n (if !bad = 0 then "" else " (first: " ^ !first ^ ")")

(* A boxed argument, fresh at every call. *)
type arg = { v : int }
let header _ a = a.v mod 50
let result h = "r" ^ string_of_int h

let () =
  let calls = ref 0 in
  let m = Memo.Memo.create 3 0 "test" header (fun _ h -> h) ( = )
            (fun _ h -> incr calls; result h) in
  run "Memo.Memo apply = g (f a)" 3000 (fun _ ->
      let a = { v = rnd 1000 } in
      let r = Memo.Memo.apply m () a in
      r = result (a.v mod 50), (fun () -> Printf.sprintf "%d -> %s" a.v r));
  Printf.printf "Memo.Memo calls of g: %d for 50 classes of headers\n" !calls;
  (* The same argument (==) is found by the first table. *)
  let a = { v = 7 } in
  let before = !calls in
  ignore (Memo.Memo.apply m () a); ignore (Memo.Memo.apply m () a);
  Printf.printf "Memo.Memo repeated argument: %d more calls of g\n" (!calls - before)

let () =
  let m = Weak_memo.TheMemo.create 3 10 "test" header (fun _ h -> h) ( = )
            (fun _ h -> result h) in
  run "Weak_memo.TheMemo apply = g (f a), with major collections" 3000 (fun i ->
      if i mod 97 = 0 then Gc.full_major ();
      let a = { v = rnd 1000 } in
      let r = Weak_memo.TheMemo.apply m () a in
      r = result (a.v mod 50), (fun () -> Printf.sprintf "%d -> %s" a.v r))

module W = Weak_memo.TheWeakMemo

let () =
  (* Headers are ints 0..399; results are fresh strings, so the weak array
     loses them at a major collection unless a descriptor is held. *)
  let w = W.create 4 10 "test" (fun _ h -> h) (fun _ h -> h) ( = )
            (fun _ h -> "w" ^ string_of_int h) in
  let held = Hashtbl.create 64 in
  run "Weak_memo.TheWeakMemo lookup/retrieve, holding and dropping descriptors" 6000 (fun i ->
      if i mod 61 = 0 then Gc.full_major ();
      let h = rnd 400 in
      let d = W.lookup w () h in
      let v = W.retrieve w () d in
      let ok_value = v = "w" ^ string_of_int h && W.retrieve_check w d in
      let ok_held =
        match Hashtbl.find_opt held h with
        | Some d' -> W.retrieve w () d' == v && W.compare d d' = 0
        | None -> true in
      (* Descriptors of different headers compare non-zero. *)
      let ok_distinct =
        Hashtbl.fold (fun h' d' ok -> ok && (h' = h || W.compare d d' <> 0)) held true in
      (match rnd 4 with
       | 0 -> Hashtbl.replace held h d
       | 1 -> Hashtbl.remove held h
       | _ -> ());
      if Hashtbl.length held > 40 then Hashtbl.reset held;
      ok_value && ok_held && ok_distinct,
      (fun () -> Printf.sprintf "step %d header %d -> %S value %b held %b distinct %b"
                   i h v ok_value ok_held ok_distinct))

module B = Line_buffer.LineBuffer
module T = Line_buffer.LineTable

let rec take n = function x :: l when n > 0 -> x :: take (n - 1) l | _ -> []

let () =
  let b = B.create () in
  let model = ref [] in        (* newest first *)
  run "Line_buffer.LineBuffer against the last 100 lines" 5000 (fun _ ->
      (match rnd 5 with
       | 0 -> B.remove_last b; (match !model with _ :: l -> model := l | [] -> ())
       | _ -> let x = rnd 10000 in B.add b x; model := take 100 (x :: !model));
      let l = List.rev !model in
      let it = ref [] in B.iter (fun x -> it := x :: !it) b;
      let c = B.clone b string_of_int in
      let ok = B.length b = List.length l
               && B.last b = (match !model with x :: _ -> Some x | [] -> None)
               && B.fold (fun acc x -> x :: acc) [] b = !model
               && List.rev !it = l
               && B.fold (fun acc x -> x :: acc) [] c = List.map string_of_int !model in
      ok, (fun () -> Printf.sprintf "length %d, model %d" (B.length b) (List.length l)))

let () =
  let t = ref T.empty and model = ref [] in      (* newest first *)
  let key i = Printf.sprintf "k%05d" i in
  run "Line_buffer.LineTable against the 100 most recent keys" 400 (fun i ->
      let k = key i in
      t := T.add !t k i; model := take 100 ((k, i) :: !model);
      let keys = List.sort compare (List.map fst !model) in
      let ok = T.fold (fun acc k _ -> k :: acc) [] !t |> List.rev = keys
               && List.for_all (fun (k, v) -> T.mem !t k && T.find !t k = v) !model
               && not (T.mem !t (key (i - 100))) in
      ok, (fun () -> Printf.sprintf "after %s: %d entries" k (T.fold (fun n _ _ -> n + 1) 0 !t)));
  (* Below the bound, adding a key again replaces its value. *)
  let t = List.fold_left (fun t (k, v) -> T.add t k v) T.empty [ "a", 1; "b", 2; "a", 3 ] in
  Printf.printf "LineTable re-add: a=%d b=%d entries=%d\n" (T.find t "a") (T.find t "b")
    (T.fold (fun n _ _ -> n + 1) 0 t)
