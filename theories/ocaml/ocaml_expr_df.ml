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

dform string_df : Ocaml!"string"[@s:s] =
   "\"" slot[@s:s] "\""

dform float_df : "float"[@f:s] =
   slot[@f:s]

dform lid_df1 : "lid"{'v} =
   slot{'v}

dform lid_df2 : "lid"[@start:n, @finish:n]{'v} =
   "lid"{'v}

dform uid_df1 : "uid"{'v} =
   slot{'v}

dform uid_df2 : "uid"[@start:n, @finish:n]{'v} =
   "uid"{'v}

(*
 * Projection.
 *)
dform proj_df1 : parens :: "prec"[prec_proj] :: "proj"{'A; 'B} =
   pushm[0] slot{'A} "." slot{'B} popm

dform proj_df2 : "proj"[@start:n, @finish:n]{'A; 'B} =
   "proj"{'A; 'B}

(*
 * Application.
 *)
dform apply_df1 : parens :: "prec"[prec_apply] :: "apply"{'e1; 'e2} =
   pushm[0] slot{'e1} space slot{'e2} popm

dform apply_df2 : "apply"[@start:n, @finish:n]{'e1; 'e2} =
   "apply"{'e1; 'e2}

(*
 * Subscripting.
 *)
dform array_subscript_df1 : parens :: "prec"[prec_proj] :: "array_subscript"{'e1; 'e2} =
   slot{'e1} array_subscript pushm[0] slot{'e2} popm ")"

dform array_subscript_df2 : "array_subscript"[@start:n, @finish:n]{'e1; 'e2} =
   "array_subscript"{'e1; 'e2}

dform string_subscript_df1 : parens :: "prec"[prec_proj] :: "string_subscript"{'e1; 'e2} =
   slot{'e1} string_subscript pushm[0] slot{'e2} popm ")"

dform string_subscript_df2 : "string_subscript"[@start:n, @finish:n]{'e1; 'e2} =
   "string_subscript"{'e1; 'e2}

(*
 * Lists, arrays, streams, records.
 * This is a recursive display form.
 *)
dform list_df1 : "list"{'e1} =
   "[" pushm[0] slot{list_expr; 'e1} popm "]"

dform array_df1 : "array"{'e1} =
   "[|" pushm[0] slot{list_expr; 'e1} popm "|]"

dform stream_df1 : "stream"{'e1} =
   "[<" pushm[0] slot{se_list; 'e1} popm ">]"

dform record_df1 : "record"{'e1} =
   "{" pushm[0] slot{ee_list; 'e1} popm "}"

dform list_df2 : "list"[@start:n, @finish:n]{'e1} =
   "list"{'e1}

dform array_df2 : "array"[@start:n, @finish:n]{'e1} =
   "array"{'e1}

dform stream_df2 : "stream"[@start:n, @finish:n]{'e1} =
   "stream"{'e1}

dform record_df2 : "record"[@start:n, @finish:n]{'e1} =
   "record"{'e1}

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
   pushm[0] szone push_indent "if" space slot{'e1} space "then" space
   slot{'e2} popm space
   push_indent "else" space
   slot{'e3} popm popm

dform ifthenelse_df2 : ifthenelse[@start:n, @finish:n]{'e1; 'e2; 'e3} =
   ifthenelse{'e1; 'e2; 'e3}

(*
 * Loops.
 *)
dform for_upto_df1 : for_upto{'e1; 'e2; x. 'e3} =
   pushm[0] push_indent
   "for" space slot{'x} space assign slot{'e2} space "to" slot{'e3} space "do" break
      slot{'e3} popm break
      "done" popm

dform for_upto_df2 : for_upto[@start:n, @finish:n]{'e1; 'e2; x. 'e3} =
   for_upto{'e1; 'e2; x. 'e3}

dform for_downto_df1 : for_downto{'e1; 'e2; x. 'e3} =
   pushm[0] push_indent
   "for" space slot{'x} space assign slot{'e2} space "downto" slot{'e3} space "do" break
      slot{'e3} popm break
      "done" popm

dform for_downto_df2 : for_downto[@start:n, @finish:n]{'e1; 'e2; x. 'e3} =
   for_downto{'e1; 'e2; x. 'e3}

dform while_df1 : "while"{'e1; 'e2} =
   szone pushm[0] push_indent "while" space slot{'e1} space "do" space
   slot{'e2} popm space
   "done" popm ezone

dform while_df2 : "while"[@start:n, @finish:n]{'e1; 'e2} =
   "while"{'e1; 'e2}

(*
 * Type casting.
 *)
dform cast_df1 : cast{'e; 't} =
   "(" slot{'e} space ":" space slot{'t} ")"

dform cast_df2 : cast[@start:n, @finish:n]{'e; 't} =
   cast{'e; 't}

(*
 * Class coercion.
 *)
dform class_coerce_df1 : parens :: "prec"[prec_rel] :: class_coerce{'e1; 'e2} =
   push_indent slot{'e1} space class_coerce slot{'e2} popm

dform class_coerce_df2 : class_coerce[@start:n, @finish:n]{'e1; 'e2} =
   class_coerce{'e1; 'e2}

(*
 * New object.
 *)
declare "new"{'e1}

dform new_df1 : parens :: "prec"[prec_not] :: "new"{'e1} =
   "new" slot{'e1}

(*
 * "Match" forms.
 *)
dform fun_df1 : parens :: "prec"[prec_fun] :: "fun"{'pwel} =
   szone push_indent "fun" space slot{patt_format; 'pwel; nil} popm ezone

dform fun_df2 : "fun"[@start:n, @finish:n]{'pwel} =
   "fun"{'pwel}

dform match_df1 : parens :: "prec"[prec_fun] :: "match"{'e; 'pwel} =
   szone push_indent "match" space slot{'e} space "with" space
   slot{patt_format; 'pwel; nil}
   popm ezone

dform match_df2 : "match"[@start:n, @finish:n]{'e; 'pwel} =
   "match"{'e; 'pwel}

dform try_df1 : parens :: "prec"[prec_fun] :: "try"{'e; 'pwel} =
   szone push_indent "try" space slot{'e} space "with" space
   slot{patt_format; 'pwel; nil}
   popm ezone

dform try_df2 : "try"[@start:n, @finish:n]{'e; 'pwel} =
   "try"{'e; 'pwel}

(*
 * "Let" forms.  The real work is performed in the patterns.
 *)
dform let_df1 : parens :: "prec"[prec_let] :: "let"{'p} =
   szone pushm[0] "let" slot{patt_format; 'p; nil} popm ezone

dform let_df2 : "let"[@start:n, @finish:n]{'p} =
   "let"{'p}

dform fix_df1 : parens :: "prec"[prec_let] :: "fix"{x. 'p} =
   szone pushm[0] "letrec" slot{patt_format; 'p; nil}

dform fix_df2 : "fix"[@start:n, @finish:n]{x. 'p} =
   "fix"{x. 'p}

(*
 * $Log$
 * Revision 1.6  1998/05/01 18:43:42  jyh
 * Added raw display.
 *
 * Revision 1.5  1998/05/01 14:59:51  jyh
 * Updating display forms.
 *
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
