(* unit-link: filter *)
(* Filter_ocaml's labelled argument (mk_lab_expr, dest_lab_expr) and
   camlp5's "declare ... end" class-field group (CrDcl), which no unit test,
   theory build or proof census reached (2026-11-16 rank: mk_lab_expr,
   dest_dcl_cf).  Each is built as camlp5 syntax (an object with grouped
   fields, nested and empty groups), turned into a term and back.  Then the
   2005 form of a label, lab[s]{opt(e)} (filter_ocaml before 2005-10-28,
   still in proof archives saved in 2006), built by hand from the current
   form's operator and location and read back.
   Not reached, stated: mk_lab_expr's several-label and no-label arms
   (patt_ifelse, patt_fail): camlp5 8's ExLab holds exactly one label.
   The expected file is the output of the code as written (2026-11-16),
   never typed. *)
open MLast
open Refiner.Refiner.Term
module F = Filter_ocaml.FilterOCaml (Refiner.Refiner)

let loc = Ploc.dummy
let v x = Ploc.VaVal x
let flat t = String.concat " " (List.filter (( <> ) "") (String.split_on_char ' ' (String.map (fun c -> if c = '\n' then ' ' else c) (Simple_print.SimplePrint.string_of_term t))))
let rec e_s = function
  | ExLid (_, Ploc.VaVal s) -> s
  | ExInt (_, Ploc.VaVal s, _) -> s
  | ExLab (_, PaLid (_, Ploc.VaVal l), Ploc.VaVal None) -> "~" ^ l
  | ExLab (_, PaLid (_, Ploc.VaVal l), Ploc.VaVal (Some e)) -> "~" ^ l ^ ":(" ^ e_s e ^ ")"
  | ExObj (_, _, Ploc.VaVal cfl) -> "object " ^ String.concat " " (List.map cf_s cfl) ^ " end"
  | _ -> "<expr>"
and cf_s = function
  | CrDcl (_, Ploc.VaVal l) -> "declare " ^ String.concat " " (List.map cf_s l) ^ " end"
  | CrIni (_, e, _) -> "initializer " ^ e_s e ^ ";"
  | CrVal (_, _, _, Ploc.VaVal s, e, _) -> "val " ^ s ^ " = " ^ e_s e ^ ";"
  | _ -> "<field>"
let back t = match F.expr_of_term t with
  | e -> e_s e
  | exception Filter_ocaml.FormatError (m, _) -> "FormatError " ^ m
  | exception e -> "raises " ^ Printexc.to_string e
let case name e =
  let r = match F.term_of_expr [] e with
    | exception Refiner.Refiner.RefineError.RefineError (n, Refiner.Refiner.RefineError.StringError m) -> "refused (" ^ n ^ ": " ^ m ^ ")"
    | exception e -> "raises " ^ Printexc.to_string e
    | t -> flat t ^ "\n      back: " ^ back t in
  Printf.printf "%-34s %s\n%!" name r

let x = ExLid (loc, v "x")
let one = ExInt (loc, v "1", "")
let ini e = CrIni (loc, e, v [])
let vl s e = CrVal (loc, v false, v false, v s, e, v [])
let () =
  case "~l" (ExLab (loc, PaLid (loc, v "l"), v None));
  case "~l:x" (ExLab (loc, PaLid (loc, v "l"), v (Some x)));
  case "object declare end end" (ExObj (loc, v None, v [ CrDcl (loc, v []) ]));
  case "object declare initializer x; end end" (ExObj (loc, v None, v [ CrDcl (loc, v [ ini x ]) ]));
  case "object declare val a = 1; initializer x; end end" (ExObj (loc, v None, v [ CrDcl (loc, v [ vl "a" one; ini x ]) ]));
  case "object declare declare end end end" (ExObj (loc, v None, v [ CrDcl (loc, v [ CrDcl (loc, v []) ]) ]))

(* The 2005 form of a label, lab[s]{opt(e)}: the label's name as the term's
   string parameter.  Built from the current form's operator and location. *)
let legacy s eo =
  let t = F.term_of_expr [] (ExLab (loc, PaLid (loc, v "z"), v None)) in
  let op = dest_op (dest_term t).term_op in
  let locs = match op.op_params with a :: b :: _ -> [ a; b ] | l -> l in
  let opt = match eo with
    | None -> mk_term (mk_op F.none_op []) []
    | Some e -> mk_term (mk_op F.some_op []) [ mk_bterm [] (F.term_of_expr [] e) ] in
  mk_term (mk_op op.op_name (locs @ [ make_param (String s) ])) [ mk_bterm [] opt ]
let () =
  List.iter (fun (name, t) -> Printf.printf "%-34s %s\n      back: %s\n%!" name (flat t) (back t))
    [ "2005 form lab[\"l\"]{none}", legacy "l" None; "2005 form lab[\"l\"]{some x}", legacy "l" (Some x) ]
