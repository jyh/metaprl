(* unit-link: filter *)
(* Db.scan_level_expression (library/db.ml), the Nuprl-5 link's reader
   of a level expression's text, through Db.string_to_parameter with type
   "l".  Its atoms (a number, a variable, a bracketed list [a | b]) and
   its suffixes (' and a number) were mostly reached by no unit test,
   theory build or proof census (2026-11-15 rank; test_db_string_params
   reads "i" and "j 1" only).  Each line prints the level read
   (Simple_print), or the exception.
   Pinned as found: a number suffix n (incr_level_exp_n) adds n only to
   the variables whose offset is 0 and takes max(n, c) of the constant,
   where ' (incr_level_exp) adds one to every part: "i 2" is i+2, but
   "i' 2" is {2 | i+1}, "[i' | j] 2" is {i+1 | j+2} and "3 2" is 3.
   Whether that is the Nuprl-5 text form's meaning is not known here.
   The expected file is the output of the code as written (2026-11-15),
   never typed. *)
open Refiner.Refiner.Term
open Refiner.Refiner.TermType

let level_of value =
  match dest_param (Db.string_to_parameter value "l") with
    ParamList [ _; l; _ ] -> (match dest_param l with MLevel l -> Simple_print.SimplePrint.string_of_level_exp l | _ -> "(not a level)")
  | _ -> "(not a level list)"

let show value =
  let r = try level_of value with Failure m -> "Failure " ^ m | e -> Printexc.to_string e in
    Printf.printf "%-16S %s\n%!" value r

let () =
  List.iter show
    [ "0"; "3"; "i"; "i'"; "i''"; "i 2"; "i' 2"; "3'"; "[i | j]"; "[i | 3]"; "[i' | j 2]"; "[3 | 5]"; "[i]"; "[[i | j] | k]";
      "[i | j]'"; "[i | j] 2"; "[i' | j] 2"; "3 2"; "[3 | i] 2"; "[]" ]
