(*
 * Display forms for patterns are a problem, because the innermost term is the
 * term to be evaluated under all the pattern bindings.
 * We contruct the pattern term and extract the inner expression.
 * Patterns are collected on a stack.
 *
 * Here is how a "let" expression looks:
 *    1. let : (p1, e1), ..., (pn, en), e
 *       let{pl; el}, where
 *       pl = patt_arg{...; patt_end{... patt_in{e}}}
 *       el = cons{e1; cons{e2; ... nil}}
 *
 * Here is how a "match" expression looks:
 *    2. match e, (p1, w1, e1), ..., (pn, wn, en)
 *       match{patt_ifelse{pwe1; patt_ifelse{pwe2; ... patt_if{pwen}}}}
 *       where
 *          pwe = patt_* ... {we}
 *          we  = patt_with{w; e} | patt_body{e}
 *
 * Here is how a "let rec" expression looks:
 * The arguments are _inside_ the pattern.
 *    3. letrec (p1, e1), ..., (pn, en), e
 *       fix{x. let{pl; x}}, where
 *       pl = patt_arg{...; patt_end{... patt_match{e1; ... patt_in{e}}}}
 *
 * These three forms are different, but we can combine their
 * display forms somewhat.
 *
 * Display forms have three arguments.
 *    1. key: (patt_format usually)
 *    2. current pattern
 *    3. stack of terms representing the pattern being constructed
 *
 * For the "let" form, we initialize the stack with the list "el".
 *)

include Ocaml
include Ocaml_base_df

open Debug
open Printf

let _ =
   if !debug_load then
      eprintf "Loading Ocaml_patt_df%t" eflush

(*
 * Special forms.
 *)
declare "as"
declare wildcard
declare rcons
declare range
declare patt_let
declare patt_fix
declare patt_reverse

(*
 * Final form.
 *)
dform patt_null_df1 : slot{patt_format; nil; nil} =
   `""

dform patt_null_df2 : slot{patt_format; nil; patt_ifelse} =
   `""

(*
 * Constant.
 *)
dform patt_char_df1 : slot{patt_format; patt_char[@c:s]{'p1}; 'p2} =
   slot{patt_format; 'p1; .cons{."char"[@c:s]; 'p2}}

dform patt_int_df1 : slot{patt_format; patt_int[@i:n]{'p1}; 'p2} =
   slot{patt_format; 'p1; .cons{."int"[@i:s]; 'p2}}

dform patt_string_df1 : slot{patt_format; patt_string[@s:s]{'p1}; 'p2} =
   slot{patt_format; 'p1; .cons{."string"[@s:s]; 'p2}}

dform patt_float_df1 : slot{patt_format; patt_float[@f:s]{'p1}; 'p2} =
   slot{patt_format; 'p1; .cons{."float"[@f:s]; 'p2}}

dform patt_char_df2 : slot{patt_format; patt_char[@start:n, @finish:n, @c:s]{'p1}; 'p2} =
   slot{patt_format; patt_char[@c:s]{'p1}; 'p2}

dform patt_int_df2 : slot{patt_format; patt_int[@start:n, @finish:n, @i:n]{'p1}; 'p2} =
   slot{patt_format; patt_int[@i:n]{'p1}; 'p2}

dform patt_string_df2 : slot{patt_format; patt_string[@start:n, @finish:n, @s:s]{'p1}; 'p2} =
   slot{patt_format; patt_string[@s:s]{'p1}; 'p2}

dform patt_float_df2 : slot{patt_format; patt_float[@start:n, @finish:n, @x:s]{'p1}; 'p2} =
   slot{patt_format; patt_float[@x:s]{'p1}; 'p2}

(*
 * Binding.
 *)
dform patt_var_df1 : slot{patt_format; patt_var{x. 'p1}; 'p2} =
   slot{patt_format; 'p1; cons{'x; 'p2}}

dform patt_var_df2 : slot{patt_format; patt_var[@start:n, @finish:n]{x. 'p1}; 'p2} =
   slot{patt_format; patt_var{x. 'p1}; 'p2}

dform patt_uid_df1 : slot{patt_format; patt_uid{patt_uid[@name:s]; 'p1}; 'p2} =
   slot{patt_format; 'p1; cons{var[@name:v]; 'p2}}

dform patt_uid_df2 : slot{patt_format; patt_uid[@start:n, @finish:n]{'p1; 'p2}; 'p3} =
   slot{patt_format; patt_uid{'p1; 'p2}; 'p3}

dform patt_lid_df1 : slot{patt_format; patt_lid{patt_lid[@name:s]; 'p1}; 'p2} =
   slot{patt_format; 'p1; cons{var[@name:v]; 'p2}}

dform patt_lid_df2 : slot{patt_format; patt_lid[@start:n, @finish:n]{'p1; 'p2}; 'p3} =
   slot{patt_format; patt_lid{'p1; 'p2}; 'p3}

(*
 * Projection.
 *)
dform patt_proj_df1 : slot{patt_format; patt_proj{'p1}; 'p2} =
   slot{patt_format; 'p1; 'p2}

dform patt_proj_arg_df1 : slot{patt_format; patt_proj_arg{'p1}; 'p2} =
   slot{patt_format; 'p1; 'p2}

dform patt_proj_end_df1 : slot{patt_format; patt_proj_end{'p1}; cons{'p2; cons{'p3; 'p4}}} =
   slot{patt_proj; 'p1; cons{proj{'p2; 'p3}; 'p4}}

dform patt_proj_df2 : slot{patt_format; patt_proj[@start:n, @finish:n]{'p1}; 'p2} =
   slot{patt_format; patt_proj{'p1}; 'p2}

dform patt_proj_arg_df2 : slot{patt_format; patt_proj_arg[@start:n, @finish:n]{'p1}; 'p2} =
   slot{patt_format; patt_proj_arg{'p1}; 'p2}

dform patt_proj_end_df2 : slot{patt_format; patt_proj_end[@start:n, @finish:n]{'p1}; 'p2} =
   slot{patt_format; patt_proj_end{'p1}; 'p2}

(*
 * Simultaneous match.
 *)
dform patt_as_df1 : slot{patt_format; patt_as{'p1}; 'p2} =
   slot{patt_format; 'p1; 'p2}

dform patt_as_arg_df1 : slot{patt_format; patt_as_arg{'p1}; 'p2} =
   slot{patt_format; 'p1; 'p2}

dform patt_as_end_df1 : slot{patt_format; patt_as_end{'p1}; cons{'p2; cons{'p3; 'p4}}} =
   slot{patt_format; 'p1; .cons{."as"{'p2; 'p3}; 'p4}}

dform patt_as_df2 : slot{patt_format; patt_as[@start:n, @finish:n]{'p1}; 'p2} =
   slot{patt_format; patt_as{'p1}; 'p2}

dform patt_as_arg_df2 : slot{patt_format; patt_as_arg[@start:n, @finish:n]{'p1}; 'p2} =
   slot{patt_format; patt_as_arg{'p1}; 'p2}

dform patt_as_end_df2 : slot{patt_format; patt_as_end[@start:n, @finish:n]{'p1}; 'p2} =
   slot{patt_format; patt_as_end{'p1}; 'p2}

(*
 * Wildcard.
 *)
dform patt_wildcard_df1 : slot{patt_format; patt_wildcard{'p1}; 'p2} =
   slot{patt_format; 'p1; cons{wildcard; 'p2}}

dform patt_wildcard_df2 : slot{patt_format; patt_wildcard[@start:n, @finish:n]{'p1}; 'p2} =
   slot{patt_format; patt_wildcard{'p1}; 'p2}

dform patt_wildcard_df3 : wildcard =
   "_"

(*
 * Application.
 *)
dform patt_apply_df1 : slot{patt_format; patt_apply{'p1}; 'p2} =
   slot{patt_format; 'p1; 'p2}

dform patt_apply_arg_df1 : slot{patt_format; patt_apply_arg{'p1}; 'p2} =
   slot{patt_format; 'p1; 'p2}

dform patt_apply_end_df1 : slot{patt_format; patt_apply_end{'p1}; cons{'p2; cons{'p3; 'p4}}} =
   slot{patt_format; 'p1; cons{apply{'p3; 'p2}; 'p4}}

dform patt_apply_df2 : slot{patt_format; patt_apply[@start:n, @finish:n]{'p1}; 'p2} =
   slot{patt_format; patt_apply{'p1}; 'p2}

dform patt_apply_arg_df2 : slot{patt_format; patt_apply_arg[@start:n, @finish:n]{'p1}; 'p2} =
   slot{patt_format; patt_apply_arg{'p1}; 'p2}

dform patt_apply_end_df2 : slot{patt_format; patt_apply_end[@start:n, @finish:n]{'p1}; 'p2} =
   slot{patt_format; patt_apply_end{'p1}; 'p2}

(*
 * Alternates.
 *)
dform patt_choice_df1 : slot{patt_format; patt_choice{'p1}; 'p2} =
   slot{patt_format; 'p1; cons{nil; 'p2}}

dform patt_choice_arg_df1 : slot{patt_format; patt_choice_arg{'p1}; cons{'p2; 'p3}} =
   slot{patt_choice; 'p1; 'p2; 'p3}

dform patt_choice_end_df1 : slot{patt_format; patt_choice_end{'p1}; cons{'p2; cons{'p3; 'p4}}} =
   slot{patt_format; 'p1; cons{rcons{'p2; 'p3}; 'p4}}

dform patt_choice_df2 : slot{patt_format; patt_choice[@start:n, @finish:n]{'p1}; 'p2} =
   slot{patt_format; patt_choice{'p1}; 'p2}

dform patt_choice_arg_df2 : slot{patt_format; patt_choice_arg[@start:n, @finish:n]{'p1}; 'p2} =
   slot{patt_format; patt_choice_arg{'p1}; 'p2}

dform patt_choice_end_df2 : slot{patt_format; patt_choice_end[@start:n, @finish:n]{'p1}; 'p2} =
   slot{patt_format; patt_choice_end{'p1}; 'p2}

(*
 * Range of choices.
 *)
dform patt_range_df1 : slot{patt_format; patt_range{'p1}; 'p2} =
   slot{patt_format; 'p1; 'p2}

dform patt_range_arg_df1 : slot{patt_format; patt_range_arg{'p1}; 'p2} =
   slot{patt_format; 'p1; 'p2}

dform patt_range_end_df1 : slot{patt_format; patt_range_end{'p1}; cons{'p2; cons{'p3; 'p4}}} =
   slot{patt_format; 'p1; cons{range{'p2; 'p3}; 'p4}}

dform patt_range_df2 : slot{patt_format; patt_range[@start:n, @finish:n]{'p1}; 'p2} =
   slot{patt_format; patt_range{'p1}; 'p2}

dform patt_range_arg_df2 : slot{patt_format; patt_range_arg[@start:n, @finish:n]{'p1}; 'p2} =
   slot{patt_format; patt_range_arg{'p1}; 'p2}

dform patt_range_end_df2 : slot{patt_format; patt_range_end[@start:n, @finish:n]{'p1}; 'p2} =
   slot{patt_format; patt_range_end{'p1}; 'p2}

(*
 * List pattern.
 *)
dform patt_list_df1 : slot{patt_format; patt_list{'p1}; 'p2} =
   slot{patt_format; 'p1; 'p2}

dform patt_list_arg_df1 : slot{patt_format; patt_list_arg{'p1}; cons{'p2; 'p3}} =
   slot{patt_list; 'p1; 'p2; 'p3}

dform patt_list_end_df1 : slot{patt_format; patt_list_end{'p1}; cons{'p2; cons{'p3; 'p4}}} =
   slot{patt_format; 'p1; cons{rcons{'p2; 'p3}; 'p4}}

dform patt_list_df2 : slot{patt_format; patt_list[@start:n, @finish:n]{'p1}; 'p2} =
   slot{patt_format; patt_list{'p1}; 'p2}

dform patt_list_arg_df2 : slot{patt_format; patt_list_arg[@start:n, @finish:n]{'p1}; 'p2} =
   slot{patt_format; patt_list_arg{'p1}; 'p2}

dform patt_list_end_df2 : slot{patt_format; patt_list_end[@start:n, @finish:n]{'p1}; 'p2} =
   slot{patt_format; patt_list_end{'p1}; 'p2}

(*
 * Tuple pattern.
 *)
dform patt_tuple_df1 : slot{patt_format; patt_tuple{'p1}; 'p2} =
   slot{patt_format; 'p1; cons{nil; 'p2}}

dform patt_tuple_arg_df1 : slot{patt_format; patt_tuple_arg{'p1}; cons{'p2; cons{'p3; 'p4}}} =
   slot{patt_format; 'p1; cons{cons{'p2; 'p3}; 'p4}}

dform patt_tuple_end_df1 : slot{patt_format; patt_tuple_end{'p1}; cons{'p2; cons{'p3; 'p4}}} =
   slot{patt_tuple; 'p1; cons{'p2; nil}; 'p3; 'p4}

dform patt_tuple_rev_df1 : slot{patt_tuple; 'p1; 'p2; nil; 'p3} =
   slot{patt_format; 'p1; cons{tuple{'p2}; 'p3}}

dform patt_tuple_rev_df2 : slot{patt_tuple; 'p1; 'p2; cons{'p3; 'p4}; 'p5} =
   slot{patt_tuple; 'p1; cons{'p3; 'p2}; 'p4; 'p5}

dform patt_tuple_df2 : slot{patt_format; patt_tuple[@start:n, @finish:n]{'p1}; 'p2} =
   slot{patt_format; patt_tuple{'p1}; 'p2}

dform patt_tuple_arg_df2 : slot{patt_format; patt_tuple_arg[@start:n, @finish:n]{'p1}; 'p2} =
   slot{patt_format; patt_tuple_arg{'p1}; 'p2}

dform patt_tuple_end_df2 : slot{patt_format; patt_tuple_end[@start:n, @finish:n]{'p1}; 'p2} =
   slot{patt_format; patt_tuple_end{'p1}; 'p2}

(*
 * Records.
 *)
dform patt_record_df1 : slot{patt_format; patt_record{patt_record_proj[@start:n, @finish:n]{'e; 'p1}}; 'p2} =
    slot{patt_format; 'p1; cons{'e; cons{nil; 'p2}}}

dform patt_record_proj_df1 : slot{patt_format; patt_record_proj{'e1; 'p1}; cons{'p2; cons{'e2; cons{'ee; 'p3}}}} =
   slot{patt_format; 'p1; cons{'e1; cons{cons{ee{'e2; 'p2}; 'ee}; 'p3}}}

dform patt_record_end_df1 : slot{patt_format; patt_record_end{'p1}; cons{'p2; cons{'e2; cons{'ee; 'p3}}}} =
   slot{patt_format; 'p1; cons{record{cons{ee{'e2; 'p2}; 'ee}}; 'p3}}

dform patt_record_df2 : slot{patt_format; patt_record[@start:n, @finish:n]{'p1}; 'p2} =
   slot{patt_format; patt_record{'p1}; 'p2}

dform patt_record_proj_df2 : slot{patt_format; patt_record_proj[@start:n, @finish:n]{'e1; 'p1}; 'p2} =
   slot{patt_format; patt_record_proj{'e1; 'p1}; 'p2}

dform patt_record_end_df : slot{patt_format; patt_record_end[@start:n, @finish:n]{'p1}; 'p2} =
   slot{patt_format; patt_record_end{'p1}; 'p2}

(*
 * "Let" forms.
 * Clauses are delimited by patt_and.
 * The stack contains one of the following:
 *    patt_let: this is the first clause of a let
 *    patt_and: this is the second or greater clause of a let
 *    patt_fix: this is a clause of a fix
 *)
dform patt_and_df1 : slot{patt_format; patt_and{'p1}; cons{'p2; cons{'e; 'el}}} =
   pushm[0] slot{'p2} `" " "=" hspace slot{'e} popm
   slot{patt_format; 'p1; 'el}

dform patt_and_df2 : slot{patt_format; patt_and[@start:n, @finish:n]{'p1}; 'e1} =
   slot{patt_format; patt_and{'p1}; 'e1}

dform patt_done_df1 : slot{patt_format; patt_done; cons{'p; cons{'e; 'el}}} =
   pushm[0] slot{'p} `" " "=" hspace szone slot{'e} ezone popm

dform patt_done_df2 : slot{patt_format; patt_done[@start:n, @finish:n]; 'e1} =
   slot{patt_format; patt_done; 'e1}

dform patt_in_df1 : slot{patt_format; patt_in{'e1}; cons{'p; cons{'e2; 'el}}} =
   pushm[0] szone slot{'p} ezone `" " "=" hspace szone slot{'e2} ezone popm hspace "_in"
   szone hspace slot{'e1} ezone

dform patt_in_df2 : slot{patt_format; patt_in[@start:n, @finish:n]{'e1}; 'e2} =
   slot{patt_format; patt_in{'e1}; 'e2}

(*
 * "Fix" forms.
 *)
dform patt_fix_and_df1 : slot{patt_format; patt_fix_and{'p1}; 'p2} =
   slot{patt_format; 'p1; 'p2}

dform patt_fix_and_df2 : slot{patt_format; patt_fix_and[@start:n, @finish:n]{'p1}; 'p2} =
   slot{patt_format; patt_fix_and{'p1}; 'p2}

dform patt_fix_arg_df1 : slot{patt_format; patt_fix_arg{'e1; 'p1}; cons{'p2; 'p3}} =
   szone pushm[0] slot{'p2} `" " "=" hspace szone slot {'e1} ezone popm ezone
   slot{patt_format; 'p1; cons{patt_fix_arg; 'p3}}

dform patt_fix_arg_df2 : slot{patt_format; patt_fix_arg{'e1; 'p1}; cons{patt_fix_arg; cons{'p2; 'p3}}} =
   newline szone `"and " pushm[0] slot{'p2} `" " "=" hspace szone slot {'e1} ezone popm ezone
   slot{patt_format; 'p1; cons{patt_fix_arg; 'p3}}

dform patt_fix_arg_df3 : slot{patt_format; patt_fix_arg[@start:n, @finish:n]{'e1; 'p1}; 'p2} =
   slot{patt_format; patt_fix_arg{'e1; 'p1}; 'p2}

dform patt_done_df3 : slot{patt_format; patt_done; cons{patt_fix_arg; nil}} =
   `""

dform patt_in_df3 : slot{patt_format; patt_in{'e1}; cons{patt_fix_arg; nil}} =
   newline "_in" `" " hspace slot{'e1}

(*
 * "Match" forms.
 *)
dform patt_ifelse_df1 : slot{patt_format; patt_ifelse{'pwe; 'pwel}; nil} =
   slot{patt_format; 'pwe; 'pwel}

dform patt_if_df1 : slot{patt_format; patt_if{'pwe}; nil} =
   slot{patt_format; 'pwe; nil}

dform patt_with_df1 : slot{patt_format; patt_with{'e1; 'e2}; 'pwel} =
   "_with" `" " szone slot{'e1} ezone "->" `" " szone slot{'e2} ezone
   slot{patt_format; 'pwel; nil}

dform patt_ifelse_df2 : slot{patt_format; patt_ifelse{'pwe; 'pwel}; patt_ifelse} =
   hspace "|" `" " szone slot{patt_format; 'pwe; 'pwel} ezone

dform patt_if_df2 : slot{patt_format; patt_if{'pwe}; patt_ifelse} =
   hspace "|" `" " szone slot{patt_format; 'pwe; nil} ezone

dform patt_body_df1 : slot{patt_format; patt_body{'e1}; cons{'e2; 'pwel}} =
   szone slot{'e2} ezone `" " "->" hspace szone slot{'e1} ezone
   slot{patt_format; 'pwel; patt_ifelse}

dform patt_ifelse_df3 : slot{patt_format; patt_ifelse[@start:n, @finish:n]{'pwe; 'pwel}; 'e} =
   slot{patt_format; patt_ifelse{'pwe; 'pwel}; 'e}

dform patt_if_df3 : slot{patt_format; patt_if[@start:n, @finish:n]{'pwe}; 'e} =
   slot{patt_format; patt_if{'pwe}; 'e}

dform patt_with_df3 : slot{patt_format; patt_with[@start:n, @finish:n]{'pwe}; 'e} =
   slot{patt_format; patt_with{'pwe}; 'e}

dform patt_body_df3 : slot{patt_format; patt_body[@start:n, @finish:n]{'e}; 'pwel} =
   slot{patt_format; patt_body{'e}; 'pwel}

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
