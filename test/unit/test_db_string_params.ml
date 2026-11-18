(* unit-link: filter *)
(* Db.string_to_parameter (library/db.ml), the Nuprl-5 link's reader of
   a parameter from its value and type strings, and its two helpers
   mk_real_param_from_strings and mk_meta_param_from_strings, which no
   unit test, theory build or proof census reached (2026-11-15 rank,
   deadsplit680).  Each line prints the parameter read (a ParamList as
   [..], a level as MLevel), or the exception raised; Basic's
   Nuprl5_Exception is not exported, so its message is the line
   Basic.error prints before raising it.  The forms: a plain value of
   each type (n, time, t, s, q, b, v, l, and an unknown type), a value
   escaped by "%%" (which keeps one "%", so "%%7" is not a number), the
   extended forms %A, %D and %S, and the meta forms %d (display) and %a
   of each type, then an unknown "%" form.
   Not reached, and why: the "oid" and "o" types, which read a stamp
   term (a stamp is this host's address, pid and time: see
   test_nuprl_stamp).
   The expected file is the output of the code as written (2026-11-15),
   never typed. *)
open Refiner.Refiner.Term
open Refiner.Refiner.TermType

let rec show_param p =
  match dest_param p with
    Number n -> "Number " ^ Lm_num.string_of_num n
  | String s -> Printf.sprintf "String %S" s
  | Token t -> "Token " ^ Opname.string_of_opname t
  | Var v -> "Var " ^ Lm_symbol.string_of_symbol v
  | MNumber v -> "MNumber " ^ Lm_symbol.string_of_symbol v
  | MString v -> "MString " ^ Lm_symbol.string_of_symbol v
  | MToken v -> "MToken " ^ Lm_symbol.string_of_symbol v
  | MLevel _ -> "MLevel"
  | ParamList ps -> "[" ^ String.concat "; " (List.map show_param ps) ^ "]"
  | ObId _ -> "ObId"
  | Quote -> "Quote"
  | Shape _ | MShape _ | Operator _ | MOperator _ -> "(other)"

let show value ptype =
  let r =
    try show_param (Db.string_to_parameter value ptype) with
    | Failure m -> "Failure " ^ m
    | e -> Printexc.to_string e
  in
    Printf.printf "%-12S %-5s %s\n%!" value ptype r

let () =
  List.iter (fun (v, t) -> show v t)
    [ "12", "n"; "1700000000", "time"; "tok", "t"; "str", "s"; "q1", "q";
      "true", "b"; "T", "b"; "false", "b"; "F", "b"; "maybe", "b"; "x", "v"; "i", "l"; "j 1", "l";
      "z", "zz";
      "%%7", "n"; "%%A", "s"; "%", "s";
      "%Aname", "t"; "%Dname", "t"; "%Sname", "t";
      "%dm", "n"; "%dm", "t"; "%dm", "s"; "%dm", "q"; "%dm", "v";
      "%am", "n"; "%am", "t"; "%am", "s"; "%am", "q"; "%a1", "b"; "%am", "v"; "%ai", "l"; "%am", "zz";
      "%Xm", "n" ]
