(* unit-link: filter *)
(* Ascii_scan.scan_char_delimited_list and scan_delimited_list
   (library/ascii_scan.ml), the Nuprl-5 link's list readers, which no
   unit test, theory build or proof census reached (2026-11-15 re-rank,
   deadsplit680).  Each input is read with scan_num items: [] (empty),
   [1], [1|22|3], a list with no closing bracket, one closed by the wrong
   character, and one with no opening bracket; it prints the items read,
   or the exception raised (Basic.Nuprl5_Exception is not exported, so
   its message is the line Basic.error prints before raising it).
   The expected file is the output of the code as written (2026-11-15). *)
let show f input =
  let s = Ascii_scan.make_scanner "\\" " \n\t" (Stream.of_string input) in
  try "[" ^ String.concat "; " (f s) ^ "]" with
  | Failure m -> "Failure " ^ m
  | e -> Printexc.to_string e

let () =
  List.iter (fun input ->
      Printf.printf "%-12S char %s\n" input
        (show (fun s -> Ascii_scan.scan_char_delimited_list s (fun () -> Lm_num.string_of_num (Ascii_scan.scan_num s)) '[' ']' '|') input);
      Printf.printf "%-12S byte %s\n" input
        (show (fun s -> Ascii_scan.scan_delimited_list s (fun () -> Lm_num.string_of_num (Ascii_scan.scan_num s))
                  Ascii_scan.ilsquare Ascii_scan.irsquare Ascii_scan.ibar) input))
    [ "[]"; "[1]"; "[1|22|3]"; "[1|2"; "[1|2)"; "1]" ]
