(*
 * This file contains the primitive syntax and display
 * for ocaml terms.
 *)

include Ocaml
include Ocaml_base_df

(*
 * Constants.
 *)
dform "char"[$c:s] =
   "'" slot[$c:s] "'"

dform "int"[$i:s] =
   slot[$i:s]

dform "string"[$s:s] =
   "\"" slot[$s:s] "\""

dform "float"[$f:s] =
   slot[$f:s]

(*
 * Projection.
 *)
dform parens :: "prec"[prec_proj] :: "proj"{'A; 'B} =
   pushm slot{'A} proj slot{'B} popm

(*
 * Application.
 *)
dform parens :: "prec"[prec_apply] :: "apply"{'e1; 'e2} =
   pushm slot{'e1} space slot{'e2} popm

(*
 * Subscripting.
 *)
dform parens :: "prec"[prec_proj] :: "array_subscript"{'e1; 'e2} =
   slot{'e1} array_subscript pushm slot{'e2} popm right_paren

dform parens :: "prec"[prec_proj] :: "string_subscript"{'e1; 'e2} =
   slot{'e1} string_subscript pushm slot{'e2} popm right_paren

(*
 * Lists, arrays, streams, records.
 * This is a recursive display form.
 *)
dform "list"{'e1} =
   left_brack pushm slot{list_expr; 'e1} popm right_brack

dform "array"{'e1} =
   left_array pushm slot{list_expr; 'e1} popm right_array

dform "stream"{'e1} =
   left_sream pushm slot{se_list; 'e1} popm right_stream

dform "record"{'e1} =
   left_record pushm slot{ee_list; 'e1} popm right_record

(*
 * Lists & arrays.
 *)
dform slot{list_expr; cons{'e1; 'e2}} =
   slot{list_expr; 'e1; 'e2}

dform slot{list_expr; 'e1; cons{'e2; 'e3}} =
   slot{'e1} space semicolon space slot{list_expr; cons{'e1; 'e3}}

dform slot{list_expr; 'e1; nil} =
   slot{'e1}

(*
 * Streams.
 *)
dform slot{se_list; nil} =
   ""

dform slot{se_list; cons{'e1; 'e2}} =
   slot{se_list; 'e1; 'e2}

dform slot{se_list; cons{'s; 'e}; nil}
   slot{'s} `"XXX" slot{'e}

dform slot{se_list; cons{'s; 'e}; cons{'e2; 'e3}} =
   slot{'s} `"XXX" slot{'e} semicolon space slot{se_list; 'e2; 'e3}

   
dform parens :: "prec"[prec_cons] :: "cons"{'e1; 'e2} =
   pushm slot{'e1} space cons slot{'e2} popm

dform "nil" = pushfont["bold"] "[]" popfont

(*
 * Records.
 *)
dform slot{ee_list; nil} =
   ""

dform slot{ee_list; cons{'e1; 'e2}} =
   slot{ee_list; 'e1; 'e2}

dform slot{ee_list; cons{'s; 'e}; nil}
   slot{'s} space equals space slot{'e}

dform slot{ee_list; cons{'s; 'e}; cons{'e2; 'e3}} =
   slot{'s} space equals space slot{'e} semicolon space slot{ee_list; 'e2; 'e3}

(*
 * Normal list elements.
 *)
dform parens :: "prec"[prec_cons] :: "cons"{'e1; 'e2} =
   pushm slot{'e1} space cons slot{'e2} popm

dform "nil" = pushfont["bold"] "[]" popfont

(*
 * Assignment.
 *)
dform parens :: "prec"[prec_assign] :: assign{'e1; 'e2} =
   push_indent slot{'e1} space assign slot{'e2} popm

(*
 * Conditional.
 *)
dform parens :: "prec"[prec_if] :: ifthenelse{'e1; 'e2; 'e3} =
   pushm szone push_indent "if" space slot{'e1} space "then" sbreak
   slot{'e2} popm sbreak
   push_indent "else" sbreak
   slot{'e3} popm popm

(*
 * Loops.
 *)
dform for_upto{'e1; 'e2; x. 'e3} =
   pushm push_indent
   "for" space slot{'x} space assign slot{'e2} space "to" slot{'e3} space "do" break
      slot{'e3} popm break
      "done" popm

dform for_downto{'e1; 'e2; x. 'e3} =
   pushm push_indentushm{3}
   "for" space slot{'x} space assign slot{'e2} space "downto" slot{'e3} space "do" break
      slot{'e3} popm break
      "done" popm

dform "while"{'e1; 'e2} =
   szone pushm push_indent "while" space slot{'e1} space "do" sbreak
   slot{'e2} popm sbreak
   "done" popm ezone

(*
 * Type casting.
 *)
dform cast{'e; 't} =
   left_paren slot{'e} space colon space slot{'t} right_paren

(*
 * Class coercion.
 *)
dform parens :: "prec"[prec_rel] :: class_coerce{'e1; 'e2} =
   push_indent slot{'e1} space class_coerce slot{'e2} popm

(*
 * New object.
 *)
declare "new"{'e1}

dform parens :: "prec"[prec_not] :: "new"{'e1} =
   "new" slot{'e1}

(*
 * "Match" forms.
 *)
dform parens :: "prec"[prec_fun] :: "fun"{'pwel} =
   szone push_indent "fun" space slot{patt_format; 'pwel; nil} popm ezone

dform parens :: "prec"[prec_fun] :: "match"{'e; 'pwel} =
   szone push_indent "match" space slot{'e} space "with" sbreak
   slot{patt_format; 'pwel; nil}
   popm ezone

dform parens :: "prec"[prec_fun] :: "try"{'e; 'pwel} =
   szone push_indent "try" space slot{'e} space "with" sbreak
   slot{patt_format; 'pwel; nil}
   popm ezone
   
(*
 * "Let" forms.  The real work is performed in the patterns.
 *)
dform parens :: "prec"[prec_let] :: "let"{'p} =
   szone pushm "let" slot{patt_format; 'p; nil} popm ezone

dform parens :: "prec"[prec_let] :: "fix"{x. 'p} =
   szone pushm "letrec" slot{patt_format; 'p; nil}

(*
 * $Log$
 * Revision 1.1  1998/02/13 16:02:11  jyh
 * Partially implemented semantics for caml.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
