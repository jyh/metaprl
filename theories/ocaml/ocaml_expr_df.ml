(*
 * This file contains the primitive syntax and display
 * for ocaml terms.
 *)

include Ocaml
include Ocaml_base_df

open Debug
open Printf

let _ =
   if !debug_load then
      eprintf "Loading Ocaml_expr_df%t" eflush

(*
 * Special flags.
 *)
declare list_expr
declare se_list
declare ee_list

(*
 * Precedences.
 *)
prec prec_proj
prec prec_apply
prec prec_cons
prec prec_assign
prec prec_equal
prec prec_if
prec prec_rel
prec prec_not
prec prec_fun
prec prec_let

(*
 * Constants.
 *)
dform char_df : "char"[@c:s] =
   "'" slot[@c:s] "'"

dform int_df : "int"[@i:s] =
   slot[@i:s]

dform string_df : "string"[@s:s] =
   "\"" slot[@s:s] "\""

dform float_df : "float"[@f:s] =
   slot[@f:s]

(*
 * Projection.
 *)
dform proj_df : parens :: "prec"[prec_proj] :: "proj"{'A; 'B} =
   pushm[0] slot{'A} proj slot{'B} popm

(*
 * Application.
 *)
dform apply_df : parens :: "prec"[prec_apply] :: "apply"{'e1; 'e2} =
   pushm[0] slot{'e1} space slot{'e2} popm

(*
 * Subscripting.
 *)
dform array_subscript_df : parens :: "prec"[prec_proj] :: "array_subscript"{'e1; 'e2} =
   slot{'e1} array_subscript pushm[0] slot{'e2} popm ")"

dform string_subscript_df : parens :: "prec"[prec_proj] :: "string_subscript"{'e1; 'e2} =
   slot{'e1} string_subscript pushm[0] slot{'e2} popm ")"

(*
 * Lists, arrays, streams, records.
 * This is a recursive display form.
 *)
dform list_df : "list"{'e1} =
   "[" pushm[0] slot{list_expr; 'e1} popm "]"

dform array_df : "array"{'e1} =
   "[|" pushm[0] slot{list_expr; 'e1} popm "|]"

dform stream_df : "stream"{'e1} =
   "[<" pushm[0] slot{se_list; 'e1} popm ">]"

dform record_df : "record"{'e1} =
   "{" pushm[0] slot{ee_list; 'e1} popm "}"

(*
 * Lists & arrays.
 *)
dform list_expr_cons_df1 : slot{list_expr; cons{'e1; 'e2}} =
   slot{list_expr; 'e1; 'e2}

dform list_expr_cons_df2 : slot{list_expr; 'e1; cons{'e2; 'e3}} =
   slot{'e1} space ";" space slot{list_expr; cons{'e1; 'e3}}

dform nil_df : slot{list_expr; 'e1; nil} =
   slot{'e1}

(*
 * Streams.
 *)
dform se_list_nil_df : slot{se_list; nil} =
   `""

dform se_list_cons_df1 : slot{se_list; cons{'e1; 'e2}} =
   slot{se_list; 'e1; 'e2}

dform se_list_cons_df2 : slot{se_list; cons{'s; 'e}; nil} =
   slot{'s} `"XXX" slot{'e}

dform se_list_cons_df3 : slot{se_list; cons{'s; 'e}; cons{'e2; 'e3}} =
   slot{'s} `"XXX" slot{'e} ";" space slot{se_list; 'e2; 'e3}

   
(*
 * Records.
 *)
dform ee_list_nil_df : slot{ee_list; nil} =
   `""

dform ee_list_nil_df1 : slot{ee_list; cons{'e1; 'e2}} =
   slot{ee_list; 'e1; 'e2}

dform ee_list_nil_df2 : slot{ee_list; cons{'s; 'e}; nil} =
   slot{'s} space "=" space slot{'e}

dform ee_list_nil_df3 : slot{ee_list; cons{'s; 'e}; cons{'e2; 'e3}} =
   slot{'s} space "=" space slot{'e} ";" space slot{ee_list; 'e2; 'e3}

(*
 * Assignment.
 *)
dform assign_df : parens :: "prec"[prec_assign] :: assign{'e1; 'e2} =
   push_indent slot{'e1} space assign slot{'e2} popm

(*
 * Conditional.
 *)
dform ifthenelse_df : parens :: "prec"[prec_if] :: ifthenelse{'e1; 'e2; 'e3} =
   pushm[0] szone push_indent "if" space slot{'e1} space "then" sbreak
   slot{'e2} popm sbreak
   push_indent "else" sbreak
   slot{'e3} popm popm

(*
 * Loops.
 *)
dform for_upto_df : for_upto{'e1; 'e2; x. 'e3} =
   pushm[0] push_indent
   "for" space slot{'x} space assign slot{'e2} space "to" slot{'e3} space "do" break
      slot{'e3} popm break
      "done" popm

dform for_downto_df : for_downto{'e1; 'e2; x. 'e3} =
   pushm[0] push_indent
   "for" space slot{'x} space assign slot{'e2} space "downto" slot{'e3} space "do" break
      slot{'e3} popm break
      "done" popm

dform while_df : "while"{'e1; 'e2} =
   szone pushm[0] push_indent "while" space slot{'e1} space "do" sbreak
   slot{'e2} popm sbreak
   "done" popm ezone

(*
 * Type casting.
 *)
dform cast_df : cast{'e; 't} =
   "(" slot{'e} space ":" space slot{'t} ")"

(*
 * Class coercion.
 *)
dform class_coerce_df : parens :: "prec"[prec_rel] :: class_coerce{'e1; 'e2} =
   push_indent slot{'e1} space class_coerce slot{'e2} popm

(*
 * New object.
 *)
declare "new"{'e1}

dform new_df2 : parens :: "prec"[prec_not] :: "new"{'e1} =
   "new" slot{'e1}

(*
 * "Match" forms.
 *)
dform fun_df : parens :: "prec"[prec_fun] :: "fun"{'pwel} =
   szone push_indent "fun" space slot{patt_format; 'pwel; nil} popm ezone

dform match_df : parens :: "prec"[prec_fun] :: "match"{'e; 'pwel} =
   szone push_indent "match" space slot{'e} space "with" sbreak
   slot{patt_format; 'pwel; nil}
   popm ezone

dform try_df : parens :: "prec"[prec_fun] :: "try"{'e; 'pwel} =
   szone push_indent "try" space slot{'e} space "with" sbreak
   slot{patt_format; 'pwel; nil}
   popm ezone
   
(*
 * "Let" forms.  The real work is performed in the patterns.
 *)
dform let_df : parens :: "prec"[prec_let] :: "let"{'p} =
   szone pushm[0] "let" slot{patt_format; 'p; nil} popm ezone

dform fix_df : parens :: "prec"[prec_let] :: "fix"{x. 'p} =
   szone pushm[0] "letrec" slot{patt_format; 'p; nil}

(*
 * $Log$
 * Revision 1.4  1998/04/29 20:54:03  jyh
 * Initial working display forms.
 *
 * Revision 1.3  1998/04/29 14:48:56  jyh
 * Added ocaml_sos.
 *
 * Revision 1.2  1998/02/18 18:47:13  jyh
 * Initial ocaml semantics.
 *
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
