(* Dform's built-in "slot" (refiner/reflib/dform.ml, slot and init_list),
   printed through the null base: a slot over a term with each parenthesis
   kind ("le", "lt", "raw", another string, none), and the parameter slots
   (a string, the "raw", "esc" and "cesc" string forms, a token, a shape,
   an operator, a level, a number, a variable).  The cov605 rank (master
   332a148a2) found every arm but the plain ones unreached by any unit
   test, theory build or proof census.  Each line prints the term, or the
   exception.  The expected file is the code's output as written, never
   typed. *)
open Opname
open Refiner.Refiner
open TermType
open Term
open TermMan
open Dform

let op n = mk_opname n xperv
let slot ps subs = mk_term (mk_op (op "slot") ps) (List.map (fun t -> mk_bterm [] t) subs)
let st x = make_param (String x)
let f = mk_simple_term (op "f") [ mk_var_term (Lm_symbol.add "x") ]
let show name t =
  Printf.printf "%-26s %s\n" name (try string_of_term null_base t with e -> "EXCEPTION " ^ Printexc.to_string e)

let () =
  show "slot[\"le\"]{f{x}}" (slot [ st "le" ] [ f ]);
  show "slot[\"lt\"]{f{x}}" (slot [ st "lt" ] [ f ]);
  show "slot[\"raw\"]{f{x}}" (slot [ st "raw" ] [ f ]);
  show "slot[\"other\"]{f{x}}" (slot [ st "other" ] [ f ]);
  show "slot{f{x}}" (slot [] [ f ]);
  show "slot[\"s\"]" (slot [ st "a b" ] []);
  show "slot[\"raw\"; \"s\"]" (slot [ st "raw"; st "a\tb" ] []);
  show "slot[\"esc\"; \"s\"]" (slot [ st "esc"; st "a\tb\"" ] []);
  show "slot[\"cesc\"; \"s\"]" (slot [ st "cesc"; st "a\tb\"" ] []);
  show "slot[token]" (slot [ make_param (Token (op "tok")) ] []);
  show "slot[shape]" (slot [ make_param (Shape (TermShape.shape_of_term f)) ] []);
  show "slot[operator]" (slot [ make_param (Operator (TermShape.opparam_of_term f)) ] []);
  show "slot[level]" (slot [ make_param (MLevel (mk_var_level_exp (Lm_symbol.add "l"))) ] []);
  show "slot[number]" (slot [ make_param (Number (Lm_num.num_of_int 42)) ] []);
  show "slot[var]" (slot [ make_param (Var (Lm_symbol.add "v")) ] []);
  show "slot[meta number]" (slot [ make_param (MNumber (Lm_symbol.add "n")) ] []);
  show "slot[meta token]" (slot [ make_param (MToken (Lm_symbol.add "t")) ] [])
