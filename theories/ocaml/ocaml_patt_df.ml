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

(*
 * Binding.
 *)
dform patt_var_df1 : slot{patt_format; patt_var{x. 'p1}; 'p2} =
   slot{patt_format; 'p1; cons{'x; 'p2}}

(*
 * Projection.
 *)
dform patt_proj_df1 : slot{patt_format; patt_proj{'p1}; 'p2} =
   slot{patt_format; 'p1; 'p2}

dform patt_proj_arg_df1 : slot{patt_format; patt_proj_arg{'p1}; 'p2} =
   slot{patt_format; 'p1; 'p2}

dform patt_proj_end_df1 : slot{patt_format; patt_proj_end{'p1}; cons{'p2; 'p3}} =
   slot{patt_proj; 'p1; 'p2; 'p3}

dform patt_proj_cons_df1 : slot{patt_proj; 'p1; 'p2; cons{'p3; 'p4}} =
   slot{patt_proj; 'p1; cons{proj{'p2; 'p3}; 'p4}}

(*
 * Simultaneous match.
 *)
dform patt_as_df1 : slot{patt_format; patt_as{'p1}; 'p2} =
   slot{patt_format; 'p1; 'p2}

dform patt_as_arg_df1 : slot{patt_format; patt_as_arg{'p1}; 'p2} =
   slot{patt_format; 'p1; 'p2}

dform patt_as_end_df1 : slot{patt_format; patt_as_end{'p1}; cons{'p2; 'p3}} =
   slot{patt_as; 'p1; 'p2; 'p3}

dform patt_as_cons_df1 : slot{patt_as; 'p1; 'p2; cons{'p3; 'p4}} =
   slot{patt_format; 'p1; .cons{."as"{'p2; 'p3}; 'p4}}

(*
 * Wildcard.
 *)
dform patt_wildcard_df1 : slot{patt_format; patt_wildcard{'p1}; 'p2} =
   slot{patt_format; 'p1; cons{wildcard; 'p2}}

(*
 * Application.
 *)
dform patt_apply_df1 : slot{patt_format; patt_apply{'p1}; 'p2} =
   slot{patt_format; 'p1; 'p2}

dform patt_apply_arg_df1 : slot{patt_format; patt_apply_arg{'p1}; 'p2} =
   slot{patt_format; 'p1; 'p2}

dform patt_apply_end_df1 : slot{patt_format; patt_apply_end{'p1}; cons{'p2; 'p3}} =
   slot{patt_apply; 'p1; 'p2; 'p3}

dform patt_apply_cons_df1 : slot{patt_apply; 'p1; 'p2; cons{'p3; 'p4}} =
   slot{patt_format; 'p1; cons{apply{'p2; 'p3}; 'p4}}

(*
 * Alternates.
 *)
dform patt_choice_df1 : slot{patt_format; patt_choice{'p1}; 'p2} =
   slot{patt_format; 'p1; cons{nil; 'p2}}

dform patt_choice_arg_df1 : slot{patt_format; patt_choice_arg{'p1}; cons{'p2; 'p3}} =
   slot{patt_choice; 'p1; 'p2; 'p3}

dform patt_choice_end_df1 : slot{patt_format; patt_choice_end{'p1}; cons{'p2; 'p3}} =
   slot{patt_choice; 'p1; 'p2; 'p3}

dform patt_choice_cons_df1 : slot{patt_choice; 'p1; 'p2; cons{'p3; 'p4}} =
   slot{patt_format; 'p1; cons{rcons{'p2; 'p3}; 'p4}}

(*
 * Range of choices.
 *)
dform patt_range_df1 : slot{patt_format; patt_range{'p1}; 'p2} =
   slot{patt_format; 'p1; 'p2}

dform patt_range_arg_df1 : slot{patt_format; patt_range_arg{'p1}; 'p2} =
   slot{patt_format; 'p1; 'p2}

dform patt_range_end_df1 : slot{patt_format; patt_range_end{'p1}; cons{'p2; 'p3}} =
   slot{patt_range; 'p1; 'p2; 'p3}

dform patt_range_cond_df1 : slot{patt_range; 'p1; 'p2; cons{'p3; 'p4}} =
   slot{patt_format; 'p1; cons{range{'p2; 'p3}; 'p4}}

(*
 * List pattern.
 *)
dform patt_list_df1 : slot{patt_format; patt_list{'p1}; 'p2} =
   slot{patt_format; 'p1; 'p2}

dform patt_list_arg_df1 : slot{patt_format; patt_list_arg{'p1}; cons{'p2; 'p3}} =
   slot{patt_list; 'p1; 'p2; 'p3}

dform patt_list_end_df1 : slot{patt_format; patt_list_end{'p1}; cons{'p2; 'p3}} =
   slot{patt_list; 'p1; 'p2; 'p3}

dform patt_list_cons_df1 : slot{patt_list; 'p1; 'p2; cons{'p3; 'p4}} =
   slot{patt_format; 'p1; cons{rcons{'p2; 'p3}; 'p4}}
   
(*
 * Tuple pattern.
 *)
dform patt_tuple_df1 : slot{patt_format; patt_tuple{'p1}; 'p2} =
   slot{patt_format; 'p1; 'p2}

dform patt_tuple_arg_df1 : slot{patt_format; patt_tuple_arg{'p1}; cons{'p2; 'p3}} =
   slot{patt_tuple; 'p1; 'p2; 'p3}

dform patt_tuple_end_df1 : slot{patt_format; patt_tuple_end{'p1}; cons{'p2; 'p3}} =
   slot{patt_tuple; 'p1; 'p2; 'p3}

dform patt_tuple_cons_df1 : slot{patt_tuple; 'p1; 'p2; cons{'p3; 'p4}} =
   slot{patt_format; 'p1; cons{rcons{'p2; 'p3}; 'p4}}
   
(*
 * "Let" forms.
 * Clauses are delimited by patt_and.
 * The stack contains one of the following:
 *    patt_let: this is the first clause of a let
 *    patt_and: this is the second or greater clause of a let
 *    patt_fix: this is a clause of a fix
 *)
dform patt_and_df1 : slot{patt_format; patt_and{'p1}; cons{'p2; 'p3}} =
   slot{patt_and; 'p1; 'p2; 'p3}

dform patt_and_cons_df1 : slot{patt_and; 'p1; 'p2; cons{'p3; 'p4}} =
   slot{patt_and; 'p1; 'p2; 'p3; 'p4}

(* First clause of a let *)
dform patt_and_let_df1 : slot{patt_and; 'p1; 'p2; patt_let; cons{'e; 'el}} =
   slot{patt_let; 'p1; 'p2; 'e; 'el}

(* Second clause of a let *)
dform patt_and_and_cons_df1 : slot{patt_and; 'p1; 'p2; patt_and; cons{'e; 'el}} =
   "and" space slot{patt_let; 'p1; 'p2; 'e; 'el}

(* Next clause of a fix *)
dform patt_fix_df1 : slot{patt_and; 'p1; 'p2; patt_fix; 'p3} =
   slot{patt_format; 'p1; cons{patt_fix; cons{'p2; 'p3}}}

dform patt_let_df1 : slot{patt_let; 'p1; 'p2; 'e; 'el} =
   slot{'p2} space "=" space slot{'e}
   slot{patt_format; 'p1; cons{patt_and; 'el}}

(*
 * Match a fix expression.
 * The stack is a stack of patterns.
 *)
dform patt_match_df1 : slot{patt_format; patt_match{'e1; 'el}; cons{'p1; 'p2}} =
   slot{patt_match; patt_match{'e1; 'el}; 'p1; 'p2}

dform patt_match_cons_df1 : slot{patt_match; 'el; 'p1; cons{'p2; 'p3}} =
   slot{patt_match; 'el; 'p1; 'p2; 'p3}

dform patt_match_fix_df1 : slot{patt_match; 'el; 'p1; patt_fix; 'p2} =
   slot{patt_reverse; 'el; 'p1; 'p2}

dform patt_reverse_cons_df1 : slot{patt_reverse; 'el; 'p1; cons{'p2; 'p3}} =
   slot{patt_reverse; 'el; cons{'p2; 'p1}; 'p3}

dform patt_reverse_nil_df1 : slot{patt_reverse; 'el; 'p1; nil} =
   slot{patt_match; 'p1; 'el}

dform patt_match_match_df1 : slot{patt_match; cons{'p1; 'pl}; patt_match{'e1; 'el}} =
   slot{'p1} space "=" space slot{'e1}
   slot{patt_in; 'pl; 'el}

dform patt_in_match_df1 : slot{patt_in; cons{'p1; 'pl}; patt_match{'e1; 'el}} =
   slot{'p1} space "=" space slot{'e1}
   slot{patt_in; 'pl; 'el}

dform patt_in_in_df1 : slot{patt_in; nil; patt_in{'e}} =
   push_indent "in" sbreak slot{'e} popm

(*
 * "Match" forms.
 *)
dform patt_ifelse_df1 : slot{patt_format; patt_ifelse{'pwe; 'pwel}; nil} =
   slot{patt_format; 'pwe; 'pwel}

dform patt_ifelse_ifelse_df1 : slot{patt_format; patt_ifelse{'pwe; 'pwel}; patt_ifelse} =
   "|" space slot{patt_format; 'pwe; 'pwel}

dform patt_if_df1 : slot{patt_format; patt_if{'pwe}; nil} =
   slot{patt_format; 'pwe; nil}

dform patt_with_df1 : slot{patt_format; patt_with{'e1; 'e2}; 'pwel} =
   "with" space slot{'e1} space "->" sbreak slot{'e2}
   slot{patt_format; 'pwel; patt_ifelse}

dform patt_body_df1 : slot{patt_format; patt_body{'e}; 'pwel} =
   "->" sbreak slot {'e}
   slot{patt_format; 'pwel; patt_ifelse}

(*
 * $Log$
 * Revision 1.4  1998/04/29 20:54:08  jyh
 * Initial working display forms.
 *
 * Revision 1.3  1998/04/29 14:49:15  jyh
 * Added ocaml_sos.
 *
 * Revision 1.2  1998/02/18 18:47:36  jyh
 * Initial ocaml semantics.
 *
 * Revision 1.1  1998/02/13 16:02:19  jyh
 * Partially implemented semantics for caml.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
