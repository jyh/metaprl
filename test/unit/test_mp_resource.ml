(* Mp_resource (refiner/reflib), the resources a theory inherits from the
   theories it extends (the rules a tactic like autoT may use, the reduce
   table, ...). No unit test drove it (the 11-02 reflib coverage page: 9 %).
   A model over random theory graphs, from a fixed LCG: 150 worlds of 2-7
   theories, each theory extending a random set of earlier ones (so
   diamonds occur), improving one resource with Public and Private items
   and placing bookmarks, interleaved at random. The resource collects its
   items in a list. The model: what a theory sees at a point (its end, or a
   bookmark) is its own items before that point, public and private, plus,
   for each theory it extends before that point, that theory's public items
   and, transitively, its ancestors' public items — each theory once,
   private items never. Items are compared as sets (every item is unique)
   and their order is not checked. Also: get_parents, a duplicate
   bookmark, closing a theory twice, extending an unknown theory, and find
   of an unknown bookmark. *)
open Mp_resource

let state = ref 21
let next () = state := (!state * 1103515245 + 12345) land 0x7fffffff; !state lsr 8
let pick n = next () mod n

let get = create_resource "test_items"
    (Functional { fp_empty = []; fp_add = (fun l (x : int) -> x :: l); fp_retr = List.rev })
let improve_int pvt x = improve pvt "test_items" (Obj.repr x)

type step = Item of private_flag * int | Ext of int | Mark of string

let () =
  let checks = ref 0 and ok = ref 0 and first = ref None and diamonds = ref 0 and marks = ref 0 in
  let parents_ok = ref 0 and parents_n = ref 0 in
  for w = 1 to 150 do
    let n = 2 + pick 6 in
    let name i = Printf.sprintf "w%dt%c" w (Char.chr (97 + i)) in
    let steps = Array.make n [] in
    for i = 0 to n - 1 do
      let exts = List.filter (fun _ -> pick 2 = 0) (List.init i (fun j -> j)) in
      let items = List.init (pick 5) (fun k -> Item ((if pick 3 = 0 then Private else Public), (w * 100 + i) * 10 + k)) in
      let ms = List.init (pick 2) (fun k -> Mark (Printf.sprintf "m%d" k)) in
      (* interleave: a random merge of the three lists *)
      let rec merge a b = match a, b with
        | [], l | l, [] -> l
        | x :: a', y :: b' -> if pick 2 = 0 then x :: merge a' b else y :: merge a b' in
      steps.(i) <- merge (merge (List.map (fun j -> Ext j) exts) items) ms;
      List.iter (function
          | Item (p, x) -> improve_int p x
          | Ext j -> extends_theory (name j)
          | Mark m -> bookmark m) steps.(i);
      close_theory (name i)
    done;
    (* the model *)
    let rec pub_star j seen =
      if List.mem j seen then seen
      else List.fold_left (fun seen s -> match s with Ext k -> pub_star k seen | _ -> seen) (j :: seen) steps.(j) in
    let visible i upto =
      let rec go acc theories = function
        | [] -> acc, theories
        | s :: rest when (match upto, s with Some m, Mark m' -> m = m' | _ -> false) -> ignore rest; acc, theories
        | Item (_, x) :: rest -> go (x :: acc) theories rest
        | Ext j :: rest -> go acc (pub_star j theories) rest
        | Mark _ :: rest -> go acc theories rest in
      let own, theories = go [] [] steps.(i) in
      let inherited = List.concat_map (fun j ->
          List.filter_map (function Item (Public, x) -> Some x | _ -> None) steps.(j)) theories in
      List.sort compare (own @ inherited) in
    for i = 0 to n - 1 do
      let exts = List.filter_map (function Ext j -> Some j | _ -> None) steps.(i) in
      let anc = List.concat_map (fun j -> pub_star j []) exts in
      if List.length anc <> List.length (List.sort_uniq compare anc) then incr diamonds;
      let points = None :: List.filter_map (function Mark m -> Some (Some m) | _ -> None) steps.(i) in
      List.iter (fun upto ->
          incr checks;
          if upto <> None then incr marks;
          let bk = match upto with None -> theory_bookmark (name i) | Some m -> (name i, m) in
          let got = try List.sort compare (get (find bk)) with e -> [ - String.length (Printexc.to_string e) ] in
          let want = visible i upto in
          if got = want then incr ok
          else if !first = None then
            first := Some (Printf.sprintf "world %d theory %s%s: got [%s], model [%s]" w (name i)
                             (match upto with None -> "" | Some m -> "." ^ m)
                             (String.concat ";" (List.map string_of_int got)) (String.concat ";" (List.map string_of_int want))))
        points;
      incr parents_n;
      let par = try List.sort compare (get_parents (name i)) with e -> [ Printexc.to_string e ] in
      if par = List.sort compare (List.map name exts) then incr parents_ok
    done;
    clear ()
  done;
  Printf.printf "150 worlds: %d of %d points agree with the model (%d at a bookmark; %d theories with a diamond)\n%!"
    !ok !checks !marks !diamonds;
  (match !first with None -> () | Some s -> Printf.printf "  first difference: %s\n%!" s);
  Printf.printf "get_parents = the theories extended directly: %d of %d\n%!" !parents_ok !parents_n;
  let attempt name f = Printf.printf "%-40s %s\n%!" name (try f (); "accepted" with e -> "raised " ^ Printexc.to_string e) in
  attempt "a duplicate bookmark in one theory" (fun () -> bookmark "dup"; bookmark "dup");
  close_theory "errs_a";
  attempt "close_theory of a closed name" (fun () -> close_theory "errs_a");
  attempt "extends_theory of an unknown theory" (fun () -> extends_theory "no_such_theory");
  attempt "find of an unknown bookmark" (fun () -> ignore (find ("errs_a", "no_such_mark")));
  attempt "find of an unknown theory" (fun () -> ignore (find (theory_bookmark "no_such_theory")))
