(*
 * The semantics of all the expressions using patterns is given here.
 * Patterns are evaluated with respect to a program stack.  Mismatched
 * patterns raise an exception, which is always caught by the "match" form.
 *
 * To simplify the fix case, we don't handle pattern failures.
 * There are no constants.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
 *
 * Copyright (C) 1998 Jason Hickey, Cornell University
 * 
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 * 
 * Author: Jason Hickey
 * jyh@cs.cornell.edu
 *)

extends Ocaml
extends Ocaml_base_sos
extends Ocaml_expr_sos

(************************************************************************
 * NEW FORMS                                                            *
 ************************************************************************)

(*
 * Primitive form for matching.
 *)
declare match_apply{'el; 'p}

(*
 * Primitives.
 *)
declare prim_match_char[@c1:s, @c2:s]
declare prim_match_int[@n1:n, @n2:n]
declare prim_match_string[@s1:s, @s2:s]
declare prim_match_name{'n1; 'n2; 'p}
declare prim_match_fst{'e1}
declare prim_match_snd{'e1}
declare prim_match_hd{'e1}
declare prim_match_tl{'e1}

declare try_match_char[@c1:s, @c2:s]
declare try_match_int[@n1:n, @n2:n]
declare try_match_string[@s1:s, @s2:s]
declare try_match_name{'n1; 'n2; 'p}

(*
 * Control forms.
 *)
declare patt_skip{'flags; 'p}
declare patt_try{'flags; 'p}
declare skip_flag[@s:s]
declare match_skip_combine{'flags; 'p}

(************************************************************************
 * REDUCTION RULES                                                      *
 ************************************************************************)

(*
 * Pattern matching is functional, and we just look up the address
 * in the environment.
 *)
rewrite patt_address_reduce :
   process{'S; match_apply{cons{address[@addr:s]; 'e2}; 'p}} <-->
      process{'S; match_apply{cons{lookup{'S; address[@addr:s]}; 'e2}; 'p}}

(*
 * Constants.
 * We don't define constants in fix patterns.
 *)
rewrite patt_char_const_reduce :
   process{'S; match_apply{cons{."char"[@c1:s]; 'e2}; patt_char[@c2:s]{'p2}}} <-->
      process{'S; prim_match_char[@c1:s, @c2:s]{match_apply{'e2; 'p2}}}

rewrite patt_char_skip_reduce :
   process{'S; match_apply{cons{."char"[@c1:s]; 'e2}; patt_skip{'flags; patt_char[@c2:s]{'p2}}}} <-->
      process{'S; match_apply{'e2; 'p2}}

rewrite patt_char_try_reduce :
   process{'S; match_apply{cons{."char"[@c1:s]; 'e2}; patt_try{'flags; patt_char[@c2:s]{'p2}}}} <-->
      process{'S; try_match_char[@c1:s, @c2:s]{match_apply{'e2; 'p2}}}

rewrite patt_int_const_reduce :
   process{'S; match_apply{cons{."int"[@i1:n]; 'e2}; patt_int[@i2:n]{'p2}}} <-->
      process{'S; prim_match_int[@i1:n, @i2:n]{match_apply{'e2; 'p2}}}

rewrite patt_int_skip_reduce :
   process{'S; match_apply{cons{."int"[@i1:n]; 'e2}; patt_skip{'flags; patt_int[@i2:n]{'p2}}}} <-->
      process{'S; match_apply{'e2; 'p2}}

rewrite patt_char_try_reduce :
   process{'S; match_apply{cons{."char"[@c1:s]; 'e2}; patt_try{'flags; patt_char[@c2:s]{'p2}}}} <-->
      process{'S; try_match_char[@c1:s, @c2:s]{match_apply{'e2; 'p2}}}

rewrite patt_string_const_reduce :
   process{'S; match_apply{cons{."string"[@s1:s]; 'e2}; patt_string[@s2:s]{'p2}}} <-->
      process{'S; prim_match_string[@s1:s, @s2:s]{match_apply{'e2; 'p2}}}

rewrite patt_string_skip_reduce :
   process{'S; match_apply{cons{."string"[@s1:s]; 'e2}; patt_skip{'flags; patt_string[@s2:s]{'p2}}}} <-->
      process{'S; match_apply{'e2; 'p2}}

rewrite patt_string_try_reduce :
   process{'S; match_apply{cons{."string"[@s1:s]; 'e2}; patt_try{'flags; patt_string[@s2:s]{'p2}}}} <-->
      process{'S; try_match_string[@s1:s, @s2:s]{match_apply{'e2; 'p2}}}

(*
 * Variable binding binds the value on top of the stack.
 * Variables don't occur in choice patterns.
 *)
rewrite patt_var_reduce :
   process{'S; match_apply{cons{'e1; 'e2}; patt_var{x. 'p2['x]}}} <-->
      process{'S; match_apply{'e2; 'p2['e1]}}

rewrite patt_var_fix_reduce :
   process{'S; match_apply{cons{'e1; 'e2}; patt_var{y. 'p2['y]}}} <-->
      process{'S; match_apply{'e2; 'p2['e1]}}

(*
 * Wildcard pops the value on the stack.
 *)
rewrite patt_wildcard_reduce :
   process{'S; match_apply{cons{'e1; 'e2}; patt_wildcard{'p2}}} <-->
      process{'S; match_apply{'e2; 'p2}}

rewrite patt_wildcard_skip_reduce :
   process{'S; match_apply{cons{'e1; 'e2}; patt_skip{'flags; patt_wildcard{'p2}}}} <-->
      process{'S; match_apply{'e2; 'p2}}

rewrite patt_wildcard_try_reduce :
   process{'S; match_apply{cons{'e1; 'e2}; patt_try{'flags; patt_wildcard{'p2}}}} <-->
      process{'S; match_apply{'e2; 'p2}}

(*
 * Typed pattern.
 *)
rewrite patt_coerce_reduce :
   process{'S; match_apply{'e; patt_coerce{'p; 't}}} <-->
      process{'S; match_apply{'e; 'p}}

rewrite patt_coerce_skip_reduce :
   process{'S; match_apply{'e; patt_skip{'flags; patt_coerce{'p; 't}}}} <-->
      process{'S; match_apply{'e; patt_skip{'flags; 'p}}}

rewrite patt_coerce_try_reduce :
   process{'S; match_apply{'e; patt_try{'flags; patt_coerce{'p; 't}}}} <-->
      process{'S; match_apply{'e; patt_try{'flags; 'p}}}

(*
 * Duplicate pattern ("as" form).
 *)
rewrite patt_as_reduce :
   process{'S; match_apply{cons{'e1; 'e2}; patt_as{'p2}}} <-->
      process{'S; match_apply{cons{'e1; cons{'e1; 'e2}}; 'p2}}

rewrite patt_as_arg_reduce :
   process{'S; match_apply{'e; patt_as_arg{'p}}} <-->
      process{'S; match_apply{'e; 'p}}

rewrite patt_as_end_reduce :
   process{'S; match_apply{'e1; patt_as_end{'p1}}} <-->
      process{'S; match_apply{'e1; 'p1}}

rewrite patt_as_skip_reduce :
   process{'S; match_apply{cons{'e1; 'e2}; patt_skip{'flags; patt_as{'p2}}}} <-->
      process{'S; match_apply{cons{'e1; cons{'e1; 'e2}}; patt_skip{'flags; 'p2}}}

rewrite patt_as_arg_skip_reduce :
   process{'S; match_apply{'e; patt_skip{'flags; patt_as_arg{'p}}}} <-->
      process{'S; match_apply{'e; patt_skip{'flags; 'p}}}

rewrite patt_as_end_skip_reduce :
   process{'S; match_apply{'e1; patt_skip{'flags; patt_as_end{'p1}}}} <-->
      process{'S; match_apply{'e1; patt_skip{'flags; 'p1}}}

rewrite patt_as_try_reduce :
   process{'S; match_apply{cons{'e1; 'e2}; patt_try{'flags; patt_as{'p2}}}} <-->
      process{'S; match_apply{cons{'e1; cons{'e1; 'e2}}; patt_try{'flags; 'p2}}}

rewrite patt_as_arg_try_reduce :
   process{'S; match_apply{'e; patt_try{'flags; patt_as_arg{'p}}}} <-->
      process{'S; match_apply{'e; patt_try{'flags; 'p}}}

rewrite patt_as_end_try_reduce :
   process{'S; match_apply{'e; patt_try{'flags; patt_as_end{'p}}}} <-->
      process{'S; match_apply{'e; patt_try{'flags; 'p}}}

(*
 * Constructor application.
 * No fix rule: what do we do when the match fails?
 *)
rewrite patt_apply_reduce :
   process{'S; match_apply{cons{inj{'n1; 'e1}; 'e2}; patt_apply{'n2; 'p2}}} <-->
      process{'S; prim_match_name{'n1; 'n2; match_apply{cons{'e1; 'e2}; 'p2}}}

rewrite patt_apply_skip_reduce :
   process{'S; match_apply{cons{inj{'n1; 'e1}; 'e2}; patt_skip{'flags; patt_apply{'n2; 'p2}}}} <-->
      process{'S; match_apply{cons{'e1; 'e2}; patt_skip{'flags; 'p2}}}

rewrite patt_apply_try_reduce :
   process{'S; match_apply{cons{inj{'n1; 'e1}; 'e2}; patt_try{'flags; patt_apply{'n2; 'p2}}}} <-->
      process{'S; try_match_name{'n1; 'n2; match_apply{cons{'e1; 'e2}; patt_try{'flags; 'p2}}}}

(*
 * Tuple pattern.
 *)
rewrite patt_tuple_reduce :
   process{'S; match_apply{cons{tuple{cons{'e1; 'el1}}; 'e2}; patt_tuple{'p1}}} <-->
      process{'S; match_apply{cons{'e1; cons{tuple{'el1}; 'e2}}; 'p1}}

rewrite patt_tuple_arg_reduce :
   process{'S; match_apply{cons{tuple{cons{'e1; 'el1}}; 'e2}; patt_tuple_arg{'p1}}} <-->
      process{'S; match_apply{cons{'e1; cons{tuple{'el1}; 'e2}}; 'p1}}

rewrite patt_tuple_end_reduce :
   process{'S; match_apply{cons{tuple{nil}; 'e1}; patt_tuple_end{'p1}}} <-->
      process{'S; match_apply{'e1; 'p1}}

rewrite patt_tuple_fix_reduce :
   process{'S; match_apply{cons{'e1; 'e2}; patt_tuple{'p1}}} <-->
      process{'S; match_apply{cons{prim_match_fst{'e1}; cons{prim_match_snd{'e1}; 'e2}}; 'p1}}

rewrite patt_tuple_arg_fix_reduce :
   process{'S; match_apply{cons{'e1; 'e2}; patt_tuple_arg{'p1}}} <-->
      process{'S; match_apply{cons{prim_match_fst{'e1}; cons{prim_match_snd{'e1}; 'e2}}; 'p1}}

rewrite patt_tuple_end_fix_reduce :
   process{'S; match_apply{cons{'e1; 'e2}; patt_tuple_arg{'p1}}} <-->
      process{'S; match_apply{'e2; 'p1}}

rewrite patt_tuple_skip_reduce :
   process{'S; match_apply{cons{tuple{cons{'e1; 'el1}}; 'e2}; patt_skip{'flags; patt_tuple{'p1}}}} <-->
      process{'S; match_apply{cons{'e1; cons{tuple{'el1}; 'e2}}; patt_skip{'flags; 'p1}}}

rewrite patt_tuple_arg_skip_reduce :
   process{'S; match_apply{cons{tuple{cons{'e1; 'el1}}; 'e2}; patt_skip{'flags; patt_tuple_arg{'p1}}}} <-->
      process{'S; match_apply{cons{'e1; cons{tuple{'el1}; 'e2}}; patt_skip{'flags; 'p1}}}

rewrite patt_tuple_end_skip_reduce :
   process{'S; match_apply{cons{tuple{nil}; 'e1}; patt_skip{'flags; patt_tuple_end{'p1}}}} <-->
      process{'S; match_apply{'e1; patt_skip{'flags; 'p1}}}

rewrite patt_tuple_try_reduce :
   process{'S; match_apply{cons{tuple{cons{'e1; 'el1}}; 'e2}; patt_try{'flags; patt_tuple{'p1}}}} <-->
      process{'S; match_apply{cons{'e1; cons{tuple{'el1}; 'e2}}; patt_try{'flags; 'p1}}}

rewrite patt_tuple_arg_try_reduce :
   process{'S; match_apply{cons{tuple{cons{'e1; 'el1}}; 'e2}; patt_try{'flags; patt_tuple_arg{'p1}}}} <-->
      process{'S; match_apply{cons{'e1; cons{tuple{'el1}; 'e2}}; patt_try{'flags; 'p1}}}

rewrite patt_tuple_end_try_reduce :
   process{'S; match_apply{cons{tuple{nil}; 'e1}; patt_try{'flags; patt_tuple_end{'p1}}}} <-->
      process{'S; match_apply{'e1; patt_try{'flags; 'p1}}}

(*
 * List pattern.
 *)
rewrite patt_list_reduce :
   process{'S; match_apply{cons{list{cons{'e1; 'el1}}; 'e2}; patt_list{'p1}}} <-->
      process{'S; match_apply{cons{'e1; cons{list{'el1}; 'e2}}; 'p1}}

rewrite patt_list_arg_reduce :
   process{'S; match_apply{cons{list{cons{'e1; 'el1}}; 'e2}; patt_list_arg{'p1}}} <-->
      process{'S; match_apply{cons{'e1; cons{list{'el1}; 'e2}}; 'p1}}

rewrite patt_list_end_reduce :
   process{'S; match_apply{cons{list{nil}; 'e1}; patt_list_end{'p1}}} <-->
      process{'S; match_apply{'e1; 'p1}}

rewrite patt_list_fix_reduce :
   process{'S; match_apply{cons{'e1; 'e2}; patt_list{'p1}}} <-->
      process{'S; match_apply{cons{prim_match_hd{'e1}; cons{prim_match_tl{'e1}; 'e2}}; 'p1}}

rewrite patt_list_arg_fix_reduce :
   process{'S; match_apply{cons{'e1; 'e2}; patt_list_arg{'p1}}} <-->
      process{'S; match_apply{cons{prim_match_hd{'e1}; cons{prim_match_tl{'e1}; 'e2}}; 'p1}}

rewrite patt_list_arg_end_reduce :
   process{'S; match_apply{cons{'e1; 'e2}; patt_list_end{'p1}}} <-->
      process{'S; match_apply{'e2; 'p1}}

rewrite patt_list_skip_reduce :
   process{'S; match_apply{cons{list{cons{'e1; 'el1}}; 'e2}; patt_skip{'flags; patt_list{'p1}}}} <-->
      process{'S; match_apply{cons{'e1; cons{list{'el1}; 'e2}}; patt_skip{'flags; 'p1}}}

rewrite patt_list_arg_skip_reduce :
   process{'S; match_apply{cons{list{cons{'e1; 'el1}}; 'e2}; patt_skip{'flags; patt_list_arg{'p1}}}} <-->
      process{'S; match_apply{cons{'e1; cons{list{'el1}; 'e2}}; patt_skip{'flags; 'p1}}}

rewrite patt_list_end_skip_reduce :
   process{'S; match_apply{cons{list{nil}; 'e1}; patt_skip{'flags; patt_list_end{'p1}}}} <-->
      process{'S; match_apply{'e1; patt_skip{'flags; 'p1}}}

rewrite patt_list_try_reduce :
   process{'S; match_apply{cons{list{cons{'e1; 'el1}}; 'e2}; patt_try{'flags; patt_list{'p1}}}} <-->
      process{'S; match_apply{cons{'e1; cons{list{'el1}; 'e2}}; patt_try{'flags; 'p1}}}

rewrite patt_list_arg_try_reduce :
   process{'S; match_apply{cons{list{cons{'e1; 'el1}}; 'e2}; patt_try{'flags; patt_list_arg{'p1}}}} <-->
      process{'S; match_apply{cons{'e1; cons{list{'el1}; 'e2}}; patt_try{'flags; 'p1}}}

rewrite patt_list_end_try_reduce :
   process{'S; match_apply{cons{list{nil}; 'e1}; patt_try{'flags; patt_list_end{'p1}}}} <-->
      process{'S; match_apply{'e1; patt_try{'flags; 'p1}}}

(*
 * Record pattern.
 * We force all the labels to be in the same order.
 *)
rewrite patt_record_reduce :
   process{'S; match_apply{'e1; patt_record{'p1}}} <-->
      process{'S; match_apply{'e1; 'p1}}

rewrite patt_record_proj_reduce :
   process{'S; match_apply{cons{'e1; 'e2}; patt_record_proj{'n2; 'p2}}} <-->
      process{'S; match_apply{'S; cons{proj{'e1; 'n2}; cons{'e1; 'e2}}; 'p2}}

rewrite patt_record_end_reduce :
   process{'S; match_apply{cons{'e1; 'e2}; patt_record_end{'p1}}} <-->
      process{'S; match_apply{'e2; 'p1}}

rewrite patt_record_skip_reduce :
   process{'S; match_apply{'e1; patt_skip{'flags; patt_record{'p1}}}} <-->
      process{'S; match_apply{'e1; patt_skip{'flags; 'p1}}}

rewrite patt_record_proj_skip_reduce :
   process{'S; match_apply{cons{'e1; 'e2}; patt_skip{'flags; patt_record_proj{'n2; 'p2}}}} <-->
      process{'S; match_apply{'S; cons{proj{'e1; 'n2}; cons{'e1; 'e2}}; patt_skip{'flags; 'p2}}}

rewrite patt_record_end_skip_reduce :
   process{'S; match_apply{cons{'e1; 'e2}; patt_skip{'flags; patt_record_end{'p1}}}} <-->
      process{'S; match_apply{'e2; patt_skip{'flags; 'p1}}}

rewrite patt_record_try_reduce :
   process{'S; match_apply{'e1; patt_try{'flags; patt_record{'p1}}}} <-->
      process{'S; match_apply{'e1; patt_try{'flags; 'p1}}}

rewrite patt_record_proj_try_reduce :
   process{'S; match_apply{cons{'e1; 'e2}; patt_try{'flags; patt_record_proj{'n2; 'p2}}}} <-->
      process{'S; match_apply{'S; cons{proj{'e1; 'n2}; cons{'e1; 'e2}}; patt_try{'flags; 'p2}}}

rewrite patt_record_end_try_reduce :
   process{'S; match_apply{cons{'e1; 'e2}; patt_try{'flags; patt_record_end{'p1}}}} <-->
      process{'S; match_apply{'e2; patt_try{'flags; 'p1}}}

(*
 * Choice is handled specially.
 *)
rewrite patt_choice_reduce :
   process{'S; match_apply{cons{'e1; 'e2}; patt_choice{'p}}} <-->
      process{'S; match_apply{cons{'e1; cons{'e1; 'e2}}; patt_try{nil; 'p}}}

rewrite patt_choice_skip_reduce :
   process{'S; match_apply{cons{'e1; 'e2}; patt_skip{'flags; patt_choice{'p}}}} <-->
      process{'S; match_apply{cons{'e1; cons{'e1; 'e2}}; patt_try{'flags; 'p}}}

rewrite patt_choice_try_reduce :
   process{'S; match_apply{cons{'e1; 'e2}; patt_try{'flags; patt_choice{'p}}}} <-->
      process{'S; match_apply{cons{'e1; cons{'e1; 'e2}}; patt_try{cons{skip_flag["try"]; 'flags}; 'p}}}

rewrite patt_choice_arg_skip_failed_reduce :
   process{'S; match_apply{cons{'e1; 'e2}; patt_skip{cons{skip_flag["failed"]; 'flags}; patt_choice_arg{'p}}}} <-->
      process{'S; match_apply{cons{'e1; cons{'e1; 'e2}}; patt_try{'flags; 'p}}}

rewrite patt_choice_arg_skip_succeeded_reduce :
   process{'S; match_apply{cons{'e1; 'e2}; patt_skip{cons{skip_flag["succeeded"]; 'flags}; patt_choice_arg{'p}}}} <-->
      process{'S; match_apply{cons{'e1; cons{'e1; 'e2}}; patt_skip{cons{skip_flag["succeeded"]; 'flags}; 'p}}}

rewrite patt_choice_arg_try_reduce :
   process{'S; match_apply{cons{'e1; 'e2}; patt_try{'flags; patt_choice_arg{'p}}}} <-->
      process{'S; match_apply{cons{'e1; cons{'e1; 'e2}}; patt_skip{cons{skip_flag["succeeded"]; 'flags}; 'p}}}

rewrite patt_choice_end_skip_reduce :
   process{'S; match_apply{cons{'e1; 'e2}; patt_skip{'flags; patt_choice_end{'p}}}} <-->
      process{'S; match_apply{'e2; match_skip_combine{'flags; 'p}}}

rewrite patt_choice_end_try_reduce :
   process{'S; match_apply{cons{'e1; 'e2}; patt_try{'flags; patt_choice_end{'p}}}} <-->
      process{'S; match_apply{'e2; match_skip_combine{cons{skip_flag["succeeded"]; 'flags}; 'p}}}

(*
 * "Let" forms.
 *)
rewrite patt_and_reduce :
   process{'S; match_apply{cons{cons{'e1; 'el1}; 'e2}; patt_and{'p}}} <-->
      process{'S; match_apply{cons{'e1; cons{'el1}; 'e2}; 'p}}

rewrite patt_in_reduce :
   process{'S; match_apply{cons{nil; nil}; patt_in{'e}}} <-->
      process{'S; 'e}

rewrite patt_with_reduce :
   process{'S; match_apply{'e; patt_with{'e1; 'e2}}} <-->
      process{'S; ifthenelse{'e1; 'e2; raise{inj["match_failed"]}}}

(*
 * "Match" forms.
 *)
rewrite patt_ifelse_reduce :
   process{'S; ."match"{'e; patt_ifelse{'pwe; 'pwel}}} <-->
      process{'S; ."try"{."match"{'e; 'pwe}; inj["match_failed"]{."match"{'e; 'pwel}}}}

rewrite patt_body_reduce :
   process{'S; match_apply{nil; patt_body{'e1}}} <-->
      process{'S; 'e1}

(************************************************************************
 * EQUIVALENCE                                                          *
 ************************************************************************)

(*
 * No rules for equivalence right now.
 * The intent is that two patterns will be equal when the patterns
 * are syntactically equal, and when the bodies are equal.
 *)

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
