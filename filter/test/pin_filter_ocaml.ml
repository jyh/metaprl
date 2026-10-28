(*
 * Pin for Filter_ocaml, the map between OCaml syntax and MetaPRL terms.
 *
 * For each top-level item of each file named on the command line, print
 * the term the item maps to (as an MD5 unless PIN_FULL is set), and
 * whether mapping that term back to OCaml and then to a term again gives
 * the same term, and Free_vars.free_vars of each expression a top-level
 * let binds.  The output is compared
 * with pin_filter_ocaml.expected, which was produced by the same program
 * built against the camlp5 7 filter (see run_pin_filter_ocaml.sh).
 *)
module F = Filter_ocaml.FilterOCaml (Refiner.Refiner)

let string_of_term = Simple_print.SimplePrint.string_of_term

(* PIN_FULL=1 prints each term; otherwise its MD5, which keeps the
 * expected file small.  Use PIN_FULL on both sides to see a difference. *)
let full = (try Sys.getenv "PIN_FULL" <> "" with Not_found -> false)

let parse_file name =
   Pcaml.input_file := name;
   let ic = open_in_bin name in
   let cs = Stream.of_channel ic in
   let rec loop acc =
      let items, st = Grammar.Entry.parse Pcaml.implem cs in
      let acc = List.rev_append items acc in
         (* Stop at end of input; a parse that consumes nothing also ends it. *)
         if st = None || items = [] || Stream.peek cs = None then
            List.rev acc
         else
            loop acc
   in
   let items = try loop [] with e -> close_in ic; raise e in
      close_in ic;
      items

(* Free_vars.free_vars of each expression a top-level let binds, in order. *)
let free_vars_of si =
   match Pin_compat.let_exprs si with
      None -> ""
    | Some el ->
         let one e =
            match Free_vars.free_vars e with
               exception e -> "ERROR " ^ Printexc.to_string e
             | vl -> String.concat "," vl
         in
            " fv=[" ^ String.concat "|" (List.map one el) ^ "]"

let print_item i (si, _) =
   let fv = free_vars_of si in
   match F.term_of_str_item [] si with
      exception e ->
         Printf.printf "%d TO-TERM-ERROR %s%s\n" i (Printexc.to_string e) fv
    | t ->
         let s = string_of_term t in
         let shown = if full then s else Digest.to_hex (Digest.string s) in
         (* The term without source locations: every term's parameters start
          * with its location pair, which camlp5 7 and 8 record differently.
          * Whitespace is collapsed first, since the printer wraps lines by
          * width, the location numbers change the width, and a wrap can fall
          * inside a location pair. *)
         let shape =
            let s = Str.global_replace (Str.regexp "[ \t\n]+") " " s in
            let s = Str.global_replace (Str.regexp "\\[[0-9]+:n, [0-9]+:n") "[L, L" s in
               Digest.to_hex (Digest.string s)
         in
         let rt =
            match F.term_of_str_item [] (F.str_item_of_term t) with
               exception e -> "ERROR " ^ Printexc.to_string e
             | t' -> if string_of_term t' = s then "same" else "DIFFERENT"
         in
            Printf.printf "%d %s shape=%s roundtrip=%s%s\n%!" i shown shape rt fv

let () =
   for k = 1 to Array.length Sys.argv - 1 do
      let name = Sys.argv.(k) in
         Printf.printf "== %s\n%!" (Filename.basename name);
         match parse_file name with
            exception e ->
               Printf.printf "PARSE-ERROR %s\n" (Printexc.to_string e)
          | items ->
               List.iteri print_item items
   done
