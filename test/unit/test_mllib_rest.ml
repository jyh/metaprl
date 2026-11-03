(* The single mllib functions no unit test entered (the 11-02 mllib
   coverage page), each against a model or its own interface's words:
   - Flist (the rewriter's list with O(1) ends): 2000 lists built from a
     fixed LCG by create, append and append_skip, each compared with a plain
     list on first, last, singleton and tree_of_list flattened. append_skip
     l1 x l2 is, by its mli, l1 without its last element, then x, then l2
     without its first.
   - Line_buffer.iter visits what fold visits, in the same order, after adds
     and a remove_last.
   - Weak_memo.TheWeakMemo.create_default: lookup and retrieve work, the
     same header gives an equal descriptor, retrieve_hack agrees with
     retrieve, and apply raises (create_default forbids it). *)

let seed = ref 7
let rnd n = seed := (!seed * 1103515245 + 12345) land 0x3fffffff; (!seed lsr 4) mod n

let rec flat = function
  | Flist.Empty -> []
  | Flist.Leaf x -> [ x ]
  | Flist.Append (a, b) -> flat a @ flat b

let rec init = function [] | [ _ ] -> [] | x :: r -> x :: init r
let rec last_of = function [ x ] -> x | _ :: r -> last_of r | [] -> assert false

let flist () =
  let pool = ref [ (Flist.create 0, [ 0 ]) ] and next = ref 1 in
  let pick () = List.nth !pool (rnd (List.length !pool)) in
  let bad = ref 0 and first_bad = ref "" and ops = Array.make 3 0 in
  for _ = 1 to 2000 do
    let op = rnd 3 in
    ops.(op) <- ops.(op) + 1;
    let fl, model =
      match op with
      | 0 -> let x = !next in incr next; (Flist.create x, [ x ])
      | 1 -> let a, ma = pick () and b, mb = pick () in (Flist.append a b, ma @ mb)
      | _ ->
          let x = !next in incr next;
          let a, ma = pick () and b, mb = pick () in
          (Flist.append_skip a x b, init ma @ [ x ] @ List.tl mb) in
    let got = (Flist.first fl, Flist.last fl, Flist.singleton fl, flat (Flist.tree_of_list fl)) in
    let want = (List.hd model, last_of model, List.length model = 1, model) in
    if got <> want then begin
      incr bad;
      if !first_bad = "" then
        first_bad := Printf.sprintf "op %d: model [%s], tree [%s]" op
            (String.concat ";" (List.map string_of_int model))
            (String.concat ";" (List.map string_of_int (let _, _, _, t = got in t)))
    end;
    if List.length model < 40 then pool := (fl, model) :: !pool
  done;
  Printf.printf "Flist: 2000 lists (create %d, append %d, append_skip %d), %d differ from the model%s\n"
    ops.(0) ops.(1) ops.(2) !bad (if !first_bad = "" then "" else "; first: " ^ !first_bad)

let line_buffer () =
  let b = Line_buffer.LineBuffer.create () in
  List.iter (Line_buffer.LineBuffer.add b) [ "a"; "b"; "c"; "d" ];
  Line_buffer.LineBuffer.remove_last b;
  Line_buffer.LineBuffer.add b "e";
  let it = ref [] in
  Line_buffer.LineBuffer.iter (fun s -> it := s :: !it) b;
  let fo = Line_buffer.LineBuffer.fold (fun acc s -> s :: acc) [] b in
  Printf.printf "Line_buffer: iter visits [%s], fold visits [%s]\n"
    (String.concat ";" (List.rev !it)) (String.concat ";" (List.rev fo))

let weak_memo () =
  let module W = Weak_memo.TheWeakMemo in
  let t = W.create_default "test" (fun () h -> h) ( = ) (fun () h -> "image of " ^ h) in
  let d1 = W.lookup t () "x" and d2 = W.lookup t () "x" and d3 = W.lookup t () "y" in
  Printf.printf "Weak_memo.create_default: retrieve %S, retrieve_hack %S, same header equal %b, other header equal %b\n"
    (W.retrieve t () d1) (W.retrieve_hack d1) (W.compare d1 d2 = 0) (W.compare d1 d3 = 0);
  Printf.printf "Weak_memo.create_default: apply %s\n"
    (try ignore (W.apply t () "x"); "returned" with Invalid_argument m -> "raised Invalid_argument " ^ m)

let () = flist (); line_buffer (); weak_memo ()
