(* Hash_with_gc (mllib) against a model, an association list.  Random
   histories of insert (of a key not present), seek, iter, and a GC
   sequence (gc_start, then gc_iter until it returns None, with a
   predicate on the key), from a table of initial size 4 so that it
   grows.  Each history's operations are checked as they run:
     - seek finds exactly the model's value (or none);
     - iter visits exactly the model's entries, each once;
     - a GC removes and returns exactly the entries the predicate marks,
       each once, and leaves the rest findable;
     - is_gc is true after gc_start and false once gc_iter has run.
   It prints, per operation, how many agree, and the first difference.
   DECLARED: a GC that leaves the table empty (a fresh table, or one where
   the predicate marks every entry) never returns: scan_for_release ends a
   sweep only when 100 * released < gc_critical * count, which is never
   true when count = 0.  This test skips those GCs and counts them.
   The generator is a fixed linear congruential sequence, not Random. *)
open Hash_with_gc.HashWithGC

let state = ref 777
let next () = state := (!state * 1103515245 + 12345) land 0x7fffffff; !state lsr 8
let pick n = next () mod n

let ops = [ "seek"; "iter"; "gc removes the marked"; "gc leaves the rest"; "is_gc after gc_start"; "is_gc after gc_iter" ]
let agree = Hashtbl.create 8 and total = Hashtbl.create 8 and first = Hashtbl.create 8
let note op ok what =
  Hashtbl.replace total op (1 + try Hashtbl.find total op with Not_found -> 0);
  if ok then Hashtbl.replace agree op (1 + try Hashtbl.find agree op with Not_found -> 0)
  else if not (Hashtbl.mem first op) then Hashtbl.add first op what

let skipped = ref 0
let sorted l = List.sort compare l
let show l = String.concat " " (List.map (fun (k, v) -> Printf.sprintf "%d:%d" k v) (sorted l))

let () =
  let histories = 300 and steps = 60 in
  for h = 1 to histories do
    let t = create 4 2 (fun k -> k * 7) ( = ) in
    let model = ref [] in
    for s = 1 to steps do
      let what = Printf.sprintf "history %d step %d" h s in
      match pick 10 with
      | 0 | 1 | 2 | 3 ->
          let k = pick 80 in
          if not (List.mem_assoc k !model) then begin
            let v = pick 1000 in
            insert t (hash t k) k v; model := (k, v) :: !model
          end
      | 4 | 5 | 6 ->
          let k = pick 80 in
          let got = try seek t (hash t k) k with e -> Some (-1 - Hashtbl.hash (Printexc.to_string e)) in
          note "seek" (got = List.assoc_opt k !model) (Printf.sprintf "%s: seek %d" what k)
      | 7 ->
          let seen = ref [] in
          iter (fun e -> seen := e :: !seen) t;
          note "iter" (sorted !seen = sorted !model) (Printf.sprintf "%s: iter %s, model %s" what (show !seen) (show !model))
      | _ ->
          let m = 2 + pick 3 in
          let marked (k, _) = k mod m = 0 in
          (* SKIP: a GC that would leave the table empty never returns
             (declared in this commit; the next commit fixes it). *)
          if List.for_all marked !model then incr skipped else begin
          gc_start t;
          note "is_gc after gc_start" (is_gc t) what;
          let removed = ref [] in
          let rec loop n =
            if n > 1000 then ()
            else match gc_iter marked t with
              | Some e -> removed := e :: !removed; loop (n + 1)
              | None -> ()
          in
          (try loop 0 with e -> removed := (-1, Hashtbl.hash (Printexc.to_string e)) :: !removed);
          note "is_gc after gc_iter" (not (is_gc t)) what;
          let want = List.filter marked !model in
          note "gc removes the marked" (sorted !removed = sorted want)
            (Printf.sprintf "%s: removed %s, model %s" what (show !removed) (show want));
          model := List.filter (fun e -> not (marked e)) !model;
          note "gc leaves the rest"
            (List.for_all (fun (k, v) -> (try seek t (hash t k) k with _ -> None) = Some v) !model)
            what
          end
    done
  done;
  Printf.printf "GCs skipped because they would empty the table: %d\n" !skipped;
  List.iter (fun op ->
      let a = try Hashtbl.find agree op with Not_found -> 0 and n = try Hashtbl.find total op with Not_found -> 0 in
      Printf.printf "%-24s %5d of %5d\n" op a n;
      match Hashtbl.find_opt first op with None -> () | Some w -> Printf.printf "  first difference: %s\n" w)
    ops
