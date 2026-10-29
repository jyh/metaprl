(* More of mllib against plain OCaml, from a fixed LCG:
   - Latin1_case: the case of each of the 256 characters against the
     ISO 8859-1 table (A-Z and 0xC0-0xDE but 0xD7 map to their letter
     32 above; 0xDF and 0xFF have no upper case in Latin-1), and the
     string functions on random strings (mllib's simplehashtbl.ml is not
     built — it is not in mllib's FILES — and nothing uses it);
   - Precedence: get_prec after random add_lt and add_eq, against the
     transitive closure of the constraints (with add_eq merging classes);
     only consistent constraint sets are generated (no cycle through <).
   Per check: how many cases differ, and the first. *)
let seed = ref 137
let rnd n = seed := (!seed * 1103515245 + 12345) land 0x3fffffff; (!seed lsr 12) mod n
let run name n case =
  seed := 137;
  let bad = ref 0 and first = ref "" in
  for _ = 1 to n do
    match case () with true, _ -> () | false, d -> incr bad; if !first = "" then first := d ()
  done;
  Printf.printf "%s: %d of %d differ%s\n" name !bad n (if !bad = 0 then "" else " (first: " ^ !first ^ ")")

let lower c = let k = Char.code c in
  if (k >= 65 && k <= 90) || (k >= 0xC0 && k <= 0xDE && k <> 0xD7) then Char.chr (k + 32) else c
let upper c = let k = Char.code c in
  if (k >= 97 && k <= 122) || (k >= 0xE0 && k <= 0xFE && k <> 0xF7) then Char.chr (k - 32) else c

let () =
  let bad = ref 0 and first = ref "" in
  for k = 0 to 255 do
    let c = Char.chr k in
    if Latin1_case.char_lowercase c <> lower c || Latin1_case.char_uppercase c <> upper c then begin
      incr bad; if !first = "" then first := Printf.sprintf "0x%02X: lower 0x%02X upper 0x%02X" k
                   (Char.code (Latin1_case.char_lowercase c)) (Char.code (Latin1_case.char_uppercase c)) end
  done;
  Printf.printf "Latin1_case on all 256 characters against ISO 8859-1: %d differ%s\n" !bad
    (if !bad = 0 then "" else " (first: " ^ !first ^ ")");
  run "Latin1_case strings: lowercase, uppercase, capitalize, uncapitalize" 2000 (fun () ->
      let s = String.init (rnd 6) (fun _ -> Char.chr (if rnd 2 = 0 then 65 + rnd 58 else 0xC0 + rnd 64)) in
      let cap f s = if s = "" then s else String.make 1 (f s.[0]) ^ String.sub s 1 (String.length s - 1) in
      let ok = Latin1_case.lowercase s = String.map lower s && Latin1_case.uppercase s = String.map upper s
               && Latin1_case.capitalize s = cap upper s && Latin1_case.uncapitalize s = cap lower s in
      ok, (fun () -> String.escaped s));
  run "Precedence: get_prec against the closure of add_lt and add_eq" 1000 (fun () ->
      let n = 2 + rnd 6 in
      let p = Array.init n (fun _ -> Precedence.new_prec ()) in
      (* a random order consistent by construction: rank r.(i); lt only from lower rank, eq only within a rank *)
      let r = Array.init n (fun _ -> rnd 4) in
      let cls = Array.init n (fun i -> i) in
      let rec find i = if cls.(i) = i then i else find cls.(i) in
      let lt = ref [] in
      for _ = 1 to rnd 8 do
        let a = rnd n and b = rnd n in
        if r.(a) < r.(b) then (Precedence.add_lt p.(a) p.(b); lt := (a, b) :: !lt)
        else if r.(a) = r.(b) && a <> b then (Precedence.add_eq p.(a) p.(b); cls.(find a) <- find b)
      done;
      let rec reach seen a b =
        find a = find b && seen <> [] || List.exists (fun (x, y) -> find x = find a && not (List.mem y seen) && reach (y :: seen) y b) !lt in
      let rel a b =
        if find a = find b then Precedence.EQRelation
        else if reach [] a b then Precedence.LTRelation
        else if reach [] b a then Precedence.GTRelation
        else Precedence.NoRelation in
      let name = function Precedence.EQRelation -> "=" | Precedence.LTRelation -> "<" | Precedence.GTRelation -> ">" | Precedence.NoRelation -> "?" in
      let bad = ref "" in
      for a = 0 to n - 1 do for b = 0 to n - 1 do
        let got = Precedence.get_prec p.(a) p.(b) and want = rel a b in
        if got <> want && !bad = "" then bad := Printf.sprintf "%d,%d: got %s want %s" a b (name got) (name want)
      done done;
      !bad = "", (fun () -> Printf.sprintf "n %d, lt %s: %s" n (String.concat " " (List.map (fun (a, b) -> Printf.sprintf "%d<%d" a b) !lt)) !bad))
