(*
 * Operational semantics for expressions.
 * In many forms, the order of evaluation is not specified,
 * so we force the sub-expressions to be values.  For instance,
 * the expressions "e1" and "e2" in (e1, e2) must be values,
 * because the compiler spec doesn't tell us which form is to
 * be evaluated first.
 *
 * Those who wish to write tuples with side-effects, should wrap them
 * in a "let" to force the order of side-effects.
 *     let x = e1 in
 *     let y = e2 in
 *        (x, y)
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/htmlman/default.html or visit http://metaprl.org/
 * for more information.
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
extends Ocaml_logic
extends Ocaml_base_sos

open Lm_debug
open Lm_printf

(************************************************************************
 * EXCEPTIONS                                                           *
 ************************************************************************)

(*
 * No exceptions are thrown.
 *)
declare type_void

(************************************************************************
 * PRIMITIVES                                                           *
 ************************************************************************)

(*
 * String operations.
 *)
declare prim_string_bounds{'s; 'i}
declare prim_string_subscript{'s; 'i}
declare prim_string_set{'s; 'i; 'c}

(*
 * Defined from the state.
 *)
declare string_bounds{'S; 'e1; 'e2}
declare string_subscript{'S; 'e1; 'e2}
declare string_set{'S; 'e1; 'e2; 'e3}

(*
 * Array operations.
 *)
declare prim_array_bounds{'s; 'i}
declare prim_array_subscript{'s; 'i}
declare prim_array_set{'s; 'i; 'c}

(*
 * Defined from the state.
 *)
declare array_bounds{'S; 'e1; 'e2}
declare array_subscript{'S; 'e1; 'e2}
declare array_set{'S; 'e1; 'e2; 'e3}

(*
 * Projection.
 *)
declare prim_record_proj{'r; 'n}
declare prim_record_set{'r; 'n; 'v}

(************************************************************************
 * CONSTANTS                                                            *
 ************************************************************************)

(*
 * Constants.
 *)
prim bool_equiv : :
   sequent { <H> >- value_equiv{'S; ."bool"[@f:s]; ."bool"[@f:s]; type_bool} }
   = it

prim bool_value : :
   sequent { <H> >- is_value{."bool"[@f:s]} }
   = it

prim char_equiv : :
   sequent { <H> >- value_equiv{'S; ."char"[@c:s]; ."char"[@c:s]; type_char} }
   = it

prim char_value : :
   sequent { <H> >- is_value{."char"[@c:s]} }
   = it

prim int_equiv : :
   sequent { <H> >- value_equiv{'S; ."int"[@i:n]; ."int"[@i:n]; type_int} }
   = it

prim int_value : :
   sequent { <H> >- is_value{'S; ."int"[@i:n]} }
   = it

(************************************************************************
 * CONTROL EXPRESSIONS                                                  *
 ************************************************************************)

(*
 * We just throw off the types in a type cast during reduction.
 * We <em>do</em> restrict the equivalence rule, but of course
 * the rule can be bypassed by performing the rewrite step.
 *)
prim cast_equiv :
   sequent { <H> >- equiv{'S; 'e1; 'e2; 't; 'exn} } -->
   sequent { <H> >- equiv{'S; cast{'e1; 't}; cast{'e2; 't}; 't; 'exn} }
   = it

prim cast_value_equiv :
   sequent { <H> >- value_equiv{'S; 'e1; 'e2; 't} } -->
   sequent { <H> >- value_equiv{'S; cast{'e1; 't}; cast{'e2; 't}; 't} }
   = it

prim_rw cast_eval :
   cast{'e; 't} <--> 'e

(*
 * Conditional.
 *)
prim ifthenelse_equiv :
   sequent { <H> >- equiv{'S; 'e1; 'e4; 't; 'exn} } -->
   sequent { <H> >- equiv{state{'S; 'e1}; 'e2; 'e5; 't; 'exn} } -->
   sequent { <H> >- equiv{state{'S; 'e1}; 'e3; 'e6; 't; 'exn} } -->
   sequent { <H> >- equiv{'S; ifthenelse{'e1; 'e2; 'e3}; ifthenelse{'e4; 'e5; 'e6}; 't; 'exn} }
   = it

prim ifthenelse_value_equiv :
   sequent { <H> >- value_equiv{'S; 'e1; 'e4; 't} } -->
   sequent { <H> >- value_equiv{'S; 'e2; 'e5; 't} } -->
   sequent { <H> >- value_equiv{'S; 'e3; 'e6; 't} } -->
   sequent { <H> >- value_equiv{'S; ifthenelse{'e1; 'e2; 'e3}; ifthenelse{'e4; 'e5; 'e6}; 't} }
   = it

prim_rw ifthenelse_eval :
   process{'S; ifthenelse{'e1; 'e2; 'e3}} <-->
      spread{process{'S; 'e1}; S2, flag.
         process{'S2; ifthenelse{'flag; 'e2; 'e3}}}

prim_rw ifthenelse_true :
   ifthenelse{bool["true":s]; 'e1; 'e2} <--> 'e1

prim_rw ifthenelse_false :
   ifthenelse{bool["false":s]; 'e1; 'e2} <--> 'e2

prim_rw ifthenelse_raise :
   ifthenelse{raise{'e}; 'e1; 'e2} <--> raise{'e}

(*
 * Loops.
 * We don't give equivalence rules for these terms.
 * Instead, we define unrollings.  We will rely on the
 * induction forms of the type theory to supply
 * reasoning about loops.
 *)
prim_rw for_upto_eval :
   is_value{'S; 'e1} -->
   is_value{'S; 'e2} -->
      (for_upto{'e1; 'e2; x. 'e3['x]} <-->
          ifthenelse{le_int{'e1; 'e2};
                     sequence{'e3['e1]; for_upto{add{'e1; ."int"[1]}; 'e2; x. 'e3['x]}};
                     unit})

prim_rw for_downto_eval :
   is_value{'S; 'e1} -->
   is_value{'S; 'e2} -->
      (for_downto{'e1; 'e2; x. 'e3['x]} <-->
          ifthenelse{ge_int{'e1; 'e2};
                     sequence{'e3['e1]; for_downto{sub{'e1; ."int"[1]}; 'e2; x. 'e3['x]}};
                     unit})

prim_rw while_eval :
   "while"{'e1; 'e2} <-->
      ifthenelse{'e1; sequence{'e2; ."while"{'e1; 'e2}}; unit}

(************************************************************************
 * ASSIGNMENT                                                           *
 ************************************************************************)

(*
 * Assignment.
 * Two cases:
 *    *1. lval is a value
 *    *2. rval is a value
 *)
prim assign_left_value_equiv 't :
   sequent { <H> >- value_equiv{'S; 'e1; 'e3; type_ref{'t}} } -->
   sequent { <H> >- equiv{'S; 'e2; 'e4; 't; 'exn} } -->
   sequent { <H> >- equiv{'S; assign{'e1; 'e2}; assign{'e3; 'e4}; type_unit; 'exn} }
   = it

prim assign_right_value_equiv 't :
   sequent { <H> >- equiv{'S; 'e1; 'e3; type_ref{'t}; 'exn} } -->
   sequent { <H> >- value_equiv{'S; 'e2; 'e4; 't} } -->
   sequent { <H> >- equiv{'S; assign{'e1; 'e2}; assign{'e3; 'e4}; type_unit; 'exn} }
   = it

prim_rw assign_eval :
   "or"{is_value{'S; 'e1}; is_value{'S; 'e2}} -->
      (process{'S; assign{'e1; 'e2}} <-->
          process{'S; assign{expr{'S; 'e1}; expr{'S; 'e2}}})

prim_rw assign_redex :
   is_value{'e2} -->
      (process{'S; assign{address[@name:s]; 'e2}} <-->
          "value"{replace{'S; address[@name:s]; expr_value{'S; 'e2}}; unit})

prim_rw assign_left_raise :
   is_value{'S; 'e2} -->
      (process{'S; assign{raise{'e1}; 'e2}} <--> process{'S; raise{'e1}})

prim_rw assign_right_raise :
   is_value{'S; 'e1} -->
      (process{'S; assign{'e1; raise{'e2}}} <--> process{'S; raise{'e2}})

(************************************************************************
 * LISTS                                                                *
 ************************************************************************)

(*
 * Lists are handled differently from other sequences because they
 * are not mutable.
 *
 * Three cases:
 *    *1. car val, cdr val
 *    *2. car arb, cdr val
 *    *3. car val, cdr arb
 *)
prim list_nil_equiv :
   sequent { <H> >- is_type{'t} } -->
   sequent { <H> >- value_equiv{'S; list{nil}; list{nil}; type_list{'t}} }
   = it

prim list_cons_equiv :
   sequent { <H> >- value_equiv{'S; 'e1; 'e2; 't} } -->
   sequent { <H> >- value_equiv{'S; list{'el1}; list{'el2}; type_list{'t}} } -->
   sequent { <H> >- value_equiv{'S; list{cons{'e1; 'el1}}; list{cons{'e2; 'el2}}; type_list{'t}} }
   = it

prim list_hd_equiv :
   sequent { <H> >- value_equiv{'S; 'e1; 'e2; 't} } -->
   sequent { <H> >- equiv{'S; list{'el1}; list{'el2}; type_list{'t}; 'exn} } -->
   sequent { <H> >- equiv{'S; list{cons{'e1; 'el1}}; list{cons{'e2; 'el2}}; type_list{'t}; 'exn} }
   = it

prim list_tl_equiv :
   sequent { <H> >- equiv{'S; 'e1; 'e2; 't; 'exn} } -->
   sequent { <H> >- value_equiv{'S; list{'el1}; list{'el2}; type_list{'t}} } -->
   sequent { <H> >- equiv{'S; list{cons{'e1; 'el1}}; list{cons{'e2; 'el2}}; type_list{'t}; 'exn} }
   = it

prim nil_equiv :
   sequent { <H> >- is_type{'t} } -->
   sequent { <H> >- value_equiv{'S; nil; nil; type_list{'t}} }
   = it

prim cons_equiv :
   sequent { <H> >- value_equiv{'S; 'e1; 'e3; 't} } -->
   sequent { <H> >- value_equiv{'S; 'e2; 'e4; type_list{'t}} } -->
   sequent { <H> >- value_equiv{'S; cons{'e1; 'e2}; cons{'e3; 'e4}; type_list{'t}} }
   = it

prim cons_hd_equiv :
   sequent { <H> >- value_equiv{'S; 'e1; 'e3; 't} } -->
   sequent { <H> >- equiv{'S; 'e2; 'e4; type_list{'t}; 'exn} } -->
   sequent { <H> >- equiv{'S; cons{'e1; 'e2}; cons{'e3; 'e4}; type_list{'t}; 'exn} }
   = it

prim cons_tl_equiv :
   sequent { <H> >- equiv{'S; 'e1; 'e3; 't; 'exn} } -->
   sequent { <H> >- value_equiv{'S; 'e2; 'e4; type_list{'t}} } -->
   sequent { <H> >- equiv{'S; cons{'e1; 'e2}; cons{'e3; 'e4}; type_list{'t}; 'exn} }
   = it

prim_rw list_cons_eval :
   "or"{is_value{'S; 'e}; is_value{'S; 'el}} -->
      (process{'S; list{cons{'e; 'el}}} <-->
          process{'S; list{cons{expr{'S; 'e}; expr{'S; list{'el}}}}})

prim_rw cons_eval :
   "or"{is_value{'S; 'e1}; is_value{'S; 'e2}} -->
      (process{'S; cons{'e1; 'e2}} <--> process{'S; cons{expr{'S; 'e1}; expr{'S; 'e2}}})

(************************************************************************
 * STRINGS                                                              *
 ************************************************************************)

(*
 * When a string is evaluated, it adds itself to the state.
 * This is a little different from standard ocaml, because
 * string constants are added to the state once--at load time.
 * Undoubtably, we will have to fix this at some point.
 *)
prim string_equiv : :
   sequent { <H> >- equiv{'S; string[@s:s]; string[@s:s]; type_string; type_void} }
   = it

prim_rw string_eval :
   process{'S; string[@s:s]} <--> allocate{'S; string[@s:s]}

(*
 * Subscripting.
 * It is also reasonable to add rules for when the
 * array is not a value, but the subscript is.
 *
 * Six cases:
 *     *1. array value, subscript value, in bounds
 *      2. array arb, subscript value, in bounds
 *      3. array value, subscript arb, in bounds
 *      + same three cases,but out-of-bounds
 *)
prim string_subscript_value_equiv :
   sequent { <H> >- value_equiv{'S; 'e1; 'e3; type_string} } -->
   sequent { <H> >- value_equiv{'S; 'e2; 'e4; type_int} } -->
   sequent { <H> >- string_bounds{'S; 'e1; 'e2} } -->
   sequent { <H> >- value_equiv{'S; string_subscript{'e1; 'e2}; string_subscript{'e3; 'e4}; type_char} }
   = it

prim_rw string_subscript_eval :
   "or"{is_value{'S; 'e1}; is_value{'S; 'e2}} -->
      (process{'S; string_subscript{'e1; 'e2}} <-->
          process{'S; string_subscript{expr{'S; 'e1}; expr{'S; 'e2}}})

prim_rw string_subscript_redex :
   process{'S; string_subscript{address[@name:s]; ."int"[@index:n]}} <-->
       process{'S; prim_string_subscript{lookup{'S; address[@name:s]}; ."int"[@index:n]}}

prim_rw string_subscript_left_raise :
   is_value{'S; 'e2} -->
      (process{'S; string_subscript{raise{'e1}; 'e2}} <--> process{'S; raise{'e1}})

prim_rw string_subscript_right_raise :
   is_value{'S; 'e1} -->
      (process{'S; string_subscript{'e1; raise{'e2}}} <--> process{'S; raise{'e2}})

(*
 * Set a character.
 * Eight cases:
 *    *1. all values
 *     2. array arb, subscript value, value value, in bounds
 *     3. array value, subscript arb, value value, in bounds
 *     4. array value, subscript value, value arb, in bounds
 *     + same four cases, but out-of-bounds
 *)
prim string_set_equiv :
   sequent { <H> >- value_equiv{'S; 'e1; 'e4; type_string} } -->
   sequent { <H> >- value_equiv{'S; 'e2; 'e5; type_int }} -->
   sequent { <H> >- value_equiv{'S; 'e3; 'e6; type_char }} -->
   sequent { <H> >- string_bounds{'S; 'e1; 'e2} } -->
   sequent { <H> >- equiv{'S; string_set{'e1; 'e2; 'e3}; string_set{'e4; 'e5; 'e6}; type_unit; 'exn} }
   = it

prim_rw string_set_eval :
   two_values{is_value{'S; 'e1}; is_value{'S; 'e2}; is_value{'S; 'e3}} -->
      (process{'S; string_set{'e1; 'e2; 'e3}} <-->
          process{'S; string_set{expr{'S; 'e1}; expr{'S; 'e2}; expr{'S; 'e3}}})

prim_rw string_set_redex :
   process{'S; address[@name:s]; ."int"[@index:n]; ."char"[@value:s]} <-->
      replace{'S; address[@name:s];
          prim_string_set{lookup{'S; address[@name:s]};
                          ."int"[@index:n];
                          ."char"[@value:s]}}

prim_rw string_set_array_raise :
   (is_value{'S; 'e1} & is_value{'S; 'e2} & is_value{'S; 'e3}) -->
      (process{'S; string_set{raise{'e1}; 'e2; 'e3}} <-->
          process{'S; raise{'e1}})

prim_rw string_set_index_raise :
   (is_value{'S; 'e1} & is_value{'S; 'e2} & is_value{'S; 'e3}) -->
      (process{'S; string_set{'e1; raise{'e2}; 'e3}} <-->
          process{'S; raise{'e2}})

prim_rw string_set_value_raise :
   (is_value{'S; 'e1} & is_value{'S; 'e2} & is_value{'S; 'e3}) -->
      (process{'S; string_set{'e1; 'e2; raise{'e3}}} <-->
          process{'S; raise{'e3}})

(************************************************************************
 * ARRAYS                                                               *
 ************************************************************************)

(*
 * Arrays.
 * We _could_ allow one entry not to be a value, but that's too hard.
 * Force all the entries to be values.
 *)
prim array_cons_equiv :
   sequent { <H> >- value_equiv{'S; 'e1; 'e2; 't} } -->
   sequent { <H> >- equiv{'S; array{'el1}; array{'el2}; type_array{'t}; 'exn} } -->
   sequent { <H> >- equiv{'S; array{cons{'e1; 'el1}}; array{cons{'e2; 'el2}}; type_array{'t}; 'exn} }
   = it

(*
 * The evaluation of an array performs an allocation.
 *)
prim_rw array_eval :
   is_value{'S; 'el} -->
      (process{'S; array{'el}} <-->
          spread{process{'S; 'el}; S2, l.
             allocate{'S2; array{'l}}})

(*
 * Get an element.
 * Six cases:
 *     *1. array value, index value, in bounds
 *      2. array arb, index value, in bounds
 *      3. array value, index arb, in bounds
 *      + same three cases but out-of-bounds
 *)
prim array_subscript_equiv :
   sequent { <H> >- value_equiv{'S; 'e1; 'e3; type_array{'t}} } -->
   sequent { <H> >- value_equiv{'S; 'e2; 'e4; type_int} } -->
   sequent { <H> >- array_bounds{'S; 'e1; 'e2} } -->
   sequent { <H> >- value_equiv{'S; array_subscript{'e1; 'e2}; array_subscript{'e3; 'e4}; 't}}
   = it

prim_rw array_subscript_eval :
   "or"{is_value{'S; 'e1}; is_value{'S; 'e2}} -->
      (process{'S; array_subscript{'e1; 'e2}} <-->
          process{'S; array_subscript{expr{'S; 'e1}; expr{'S; 'e2}}})

prim_rw array_subscript_redex :
   process{'S; array_subscript{address[@name:s]; int[@index:n]}} <-->
      value{'S; prim_array_subscript{lookup{'S; address[@name:s]}; int[@index:n]}}

prim_rw array_subscript_array_raise :
   is_value{'S; 'e2} -->
      (process{'S; array_subscript{raise{'e1}; 'e2}} <-->
          process{'S; raise{'e1}})

prim_rw array_subscript_subscript_raise :
   is_value{'S; 'e1} -->
      (process{'S; array_subscript{'e1; raise{'e2}}} <-->
          process{'S; raise{'e2}})

(*
 * Set an element.
 * Eight cases:
 *    *1. array val, subscript val, value val, in bounds
 *     2. array arb, subscript val, value val, in bounds
 *     3. array val, subscript arb, value val, in bounds
 *     4. array val, subscript val, value arb, in bounds
 *     + same four cases, but out-of-bounds
 *)
prim array_set_equiv 't :
   sequent { <H> >- value_equiv{'S; 'e1; 'e4; type_array{'t}} } -->
   sequent { <H> >- value_equiv{'S; 'e2; 'e5; type_int} } -->
   sequent { <H> >- value_equiv{'S; 'e3; 'e6; 't} } -->
   sequent { <H> >- equiv{'S; array_set{'e1; 'e2; 'e3}; array_set{'e4; 'e5; 'e6}; type_unit; 'exn} }
   = it

prim_rw array_set_eval :
   two_values{is_value{'S; 'e1}; is_value{'S; 'e2}; is_value{'S; 'e3}} -->
      (process{'S; array_set{'e1; 'e2; 'e3}} <-->
          process{'S; array_set{expr{'S; 'e1}; expr{'S; 'e2}; expr{'S; 'e3}}})

prim_rw array_set_redex :
   is_value{'S; 'e} -->
      (process{'S; array_set{address[@name:s]; int[@index:n]; 'e}} <-->
          process{'S; prim_array_set{address[@name:s]; int[@index:n]; expr_value{'S; 'e}}})

prim_rw array_set_array_raise :
   (is_value{'S; 'e2} & is_value{'S; 'e3}) -->
      (process{'S; array_set{raise{'exn}; 'e2; 'e3}} <-->
          process{'S; raise{'exn}})

prim_rw array_set_subscript_raise :
   (is_value{'S; 'e1} & is_value{'S; 'e3}) -->
      (process{'S; array_set{'e1; raise{'exn}; 'e3}} <-->
          process{'S; raise{'exn}})

prim_rw array_set_value_raise :
   (is_value{'S; 'e1} & is_value{'S; 'e2}) -->
      (process{'S; array_set{'e1; 'e2; raise{'exn}}} <-->
          process{'S; raise{'exn}})

(************************************************************************
 * RECORDS                                                              *
 ************************************************************************)

(*
 * Record creation.
 * Force all the entries to be values.
 *)
prim record_equiv :
   sequent { <H> >- value_equiv{'S; 'e1; 'e2; 't1} } -->
   sequent { <H> >- equiv{'S; record{'el1}; record{'el2}; type_record{'tl1}; 'exn} } -->
   sequent { <H> >- equiv{'S;
                         record{cons{cons{'n1; 'e1}; 'el1}};
                         record{cons{cons{'n1; 'e2}; 'el2}};
                         type_record{cons{'n1; 't1}; 'tl1};
                         'exn} }
   = it

prim_rw record_eval :
   is_value{'S; 'vl} -->
      (process{'S; record{'vl}} <-->
          allocate{'S; record{expr_value{'S; 'vl}}})

(*
 * Projection.
 * Two cases:
 *    *1. record val, label val
 *    *2. record arb, label val
 *)
prim proj_value_equiv :
   sequent { <H> >- value_equiv{'S; 'e1; 'e2; type_record{cons{cons{'n1; 't}; nil}}} } -->
   sequent { <H> >- name_equiv{'S; 'n1; 'n2} } -->
   sequent { <H> >- value_equiv{'S; proj{'e1; 'n1}; proj{'e2; 'n2}; 't} }
   = it

prim proj_equiv :
   sequent { <H> >- equiv{'S; 'e1; 'e2; type_record{cons{cons{'n1; 't}; nil}}; 'exn} } -->
   sequent { <H> >- name_equiv{'S; 'n1; 'n2} } -->
   sequent { <H> >- equiv{'S; proj{'e1; 'n1}; proj{'e2; 'n2}; 't; 'exn} }
   = it

prim_rw proj_eval :
      process{'S; proj{'e1; 'n1}} <-->
          process{'S; proj{expr{'S; 'e1}; 'n1}}

prim_rw proj_redex :
   process{'S; proj{address[@name:s]; 'n1}} <-->
      process{'S; prim_record_proj{lookup{'S; address[@name:s]}; 'n1}}

(*
 * Set a record field.
 * Three cases:
 *    *1. record val, label val, value val
 *    *2. record arb, label val, value val
 *    *3. record val, label val, value arb
 *)
prim record_set_value_equiv 't :
   sequent { <H> >- value_equiv{'S; 'e1; 'e3; type_record{cons{cons{'n1; 't}; nil}}} } -->
   sequent { <H> >- name_equiv{'S; 'n1; 'n2} } -->
   sequent { <H> >- value_equiv{'S; 'e2; 'e4; 't} } -->
   sequent { <H> >- value_equiv{'S;
                               record_set{'e1; 'n1; 'e2};
                               record_set{'e3; 'n2; 'e4};
                               type_unit} }
   = it

prim record_set_record_equiv 't :
   sequent { <H> >- equiv{'S; 'e1; 'e3; type_record{cons{cons{'n1; 't}; nil}}; 'exn} } -->
   sequent { <H> >- name_equiv{'S; 'n1; 'n2} } -->
   sequent { <H> >- value_equiv{'S; 'e2; 'e4; 't} } -->
   sequent { <H> >- equiv{'S;
                         record_set{'e1; 'n1; 'e2};
                         record_set{'e3; 'n2; 'e4};
                         type_unit;
                         'exn} }
   = it

prim record_set_arg_equiv 't :
   sequent { <H> >- value_equiv{'S; 'e1; 'e3; type_record{cons{cons{'n1; 't}; nil}}} } -->
   sequent { <H> >- name_equiv{'S; 'n1; 'n2} } -->
   sequent { <H> >- equiv{'S; 'e2; 'e4; 't; 'exn} } -->
   sequent { <H> >- equiv{'S;
                         record_set{'e1; 'n1; 'e2};
                         record_set{'e3; 'n2; 'e4};
                         type_unit;
                         'exn} }
   = it

prim_rw record_set_eval :
   por{is_value{'e1}; is_value{'e3}} -->
      (process{'S; record_set{'e1; 'n1; 'e3}} <-->
          process{'S; record_set{expr{'S; 'e1}; 'n1; expr{'S; 'e3}}})

prim_rw record_set_redex :
   is_value{'S; 'e} -->
      (process{'S; record_set{address[@name:s]; 'n1; 'e}} <-->
          replace{'S; address[@name:s];
              prim_record_set{lookup{'S; address[@name:s]};
                              'n1;
                              expr_value{'S; 'e}}})

(************************************************************************
 * FUNCTIONS                                                            *
 ************************************************************************)

(*
 * Intensional equivalence of functions.
 *)
prim fun_equiv : :
   sequent { <H> >- value_equiv{'S; ."fun"{'pwel1}; ."fun"{'pwel2}; type_fun{'t1; 't2}} }
   = it

(************************************************************************
 * LET                                                                  *
 ************************************************************************)

(*
prim let_equiv :
   sequent { <H> >- equiv{'S; 'el1; 'el2; 'tl} } -->
   sequent { <H> >- equiv{state{'S; 'el1}; 'p1; 'p2; type_fun{'tl; 't}} } -->
   sequent { <H> >- equiv{'S; ."let"{'p1; 'e1}; ."let"{'p2; 'e2}; 't} }

prim let_value_equiv :
   sequent { <H> >- value_equiv{'S; 'el1; 'el2; 'tl} } -->
   sequent { <H> >- value_equiv{'S; 'p1; 'p2; type_fun{'tl; 't}} } -->
   sequent { <H> >- value_equiv{'S; ."let"{'p1; 'e1}; ."let"{'p2; 'e2}; 't} }

prim_rw let_eval :
   process{'S; ."let"{'p; 'e}} <-->
      process{'S; ."match"{'e; 'p}}
*)

(************************************************************************
 * MATCH                                                                *
 ************************************************************************)

(*
prim match_equiv :
   sequent { <H> >- equiv{'S; 'e1; 'e2; 't2; 'exn} } -->
   sequent { <H> >- equiv{'S; 'p1; 'p2; type_fun{'t2; 't1}; 'exn} } -->
   sequent { <H> >- equiv{'S; ."match"{'e1; 'p1}; ."match"{'e2; 'p2}; 't; 'exn} }

prim match_value_equiv :
   sequent { <H> >- value_equiv{'S; 'e1; 'e2; 't2} } -->
   sequent { <H> >- value_equiv{'S; 'p1; 'p2; functional{'t2; 't1}} } -->
   sequent { <H> >- value_equiv{'S; ."match"{'e1; 'p1}; ."match"{'e2; 'p2}; 't} }
*)

(************************************************************************
 * FUNCTIONS                                                            *
 ************************************************************************)

(*
 * Application.
 *)
prim apply_equiv 't1 :
   sequent { <H> >- equiv{'S; 'f1; 'f2; type_fun{'t1; 't2}; 'exn} } -->
   sequent { <H> >- equiv{'S; 'a1; 'a2; 't1; 'exn} } -->
   sequent { <H> >- equiv{'S; apply{'f1; 'a1}; apply{'f2; 'a2}; 't2; 'exn}}
   = it

prim apply_value_equiv 't1 :
   sequent { <H> >- value_equiv{'S; 'f1; 'f2; functional{'t1; 't2}} } -->
   sequent { <H> >- value_equiv{'S; 'a1; 'a2; 't1} } -->
   sequent { <H> >- value_equiv{'S; apply{'f1; 'a1}; apply{'f2; 'a2}; 't2} }
   = it

prim_rw apply_eval :
   process{'S; apply{'e1; 'e2}} <-->
       spread{process{'S; 'e1}; f, S2.
          process{'S2; apply{'f; 'e2}}}

prim_rw apply_apply_eval :
   process{'S; apply{."fun"{'pwel}; 'e2}} <-->
      process{'S; ."match"{'e2; 'pwel}}

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
