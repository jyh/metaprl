(*
 * The semantics of all the expressions using patterns is given here.
 * Patterns are evaluated with respect to a program stack.  Mismatched
 * patterns raise an exception, which is always caught by the "match" form.
 *)

open Ocaml
open Ocaml_base_sos
open Ocaml_expr_sos

(************************************************************************
 * CONSTANTS                                                            *
 ************************************************************************)

(*
 * Constants.
 *)
rewrite patt_char_reduce :
   eval{'S; match_apply{cons{"char"[$c1:s]; 'e2}; patt_char[$c2:s]{'p2}}} <-->
      eval{'S; match_char[$c1:s; $c2:s]{match_apply{'e; 'p2}}}

rewrite patt_int_reduce :
   eval{'S; match_apply{cons{"int"[$i1:n]; 'e2}; patt_int[$i2:n]{'p2}}} <-->
      eval{'S; match_int[$i1:n; $i2:n]{match_apply{'e; 'p2}}}

(*
 * Address are just looked up in the environment.
 *)
rewrite patt_address_reduce :
   eval{'S; match_apply{cons{address[$addr:s]; 'e2}; 'p}} <-->
      eval{'S; match_apply{cons{lookup{'S; address[$addr:s]}; 'e2}; 'p}}

(*
 * Strings.
 *)
rewrite patt_string_reduce :
   eval{'S; match_apply{cons{string[$s1:s]; 'e2}; patt_string[$s2:s]{'p2}}} <-->
      eval{'S; match_string[$s1:s; $s2:s]{match_apply{'e2; 'p2}}}

(*
 * Variable binding binds the value on top of the stack.
 *)
rewrite patt_var_reduce :
   eval{'S; match_apply{cons{'e1; 'e2}; patt_var{x. 'p2['x]}}} <-->
      eval{'S; match_apply{'e2; 'p2['e1]}}

(*
 * Wildcard pops the value on the stack.
 *)
rewrite patt_wildcard_reduce :
   eval{'S; match_apply{cons{'e1; 'e2}; patt_wildcard{'p2}}} <-->
      eval{'S; match_apply{'e2; 'p2}}

(*
 * Typed pattern.
 *)
rewrite patt_coerce_reduce :
   eval{'S; match_apply{'e; patt_coerce{'p; 't}}} <-->
      eval{'S; match_apply{'e; 'p}}

(*
 * Duplicate pattern ("as" form).
 *)
rewrite patt_as_reduce :
   eval{'S; match_apply{cons{'e1; 'e2}; patt_as{'p2}}} <-->
      eval{'S; match_apply{cons{'e1; cons{'e1; 'e2}}; 'p2}}

rewrite patt_as_arg_reduce :
   eval{'S; match_apply{cons{'e1; 'e2}; patt_as_arg{'p2}}} <-->
      eval{'S; match_apply{'e2; 'p2}}

rewrite patt_as_end_reduce :
   eval{'S; match_apply{'e1; patt_as_end{'p1}}} <-->
      eval{'S; match_apply{'e1; 'p2}}

(*
 * Constructor application.
 *)
rewrite patt_apply_reduce :
   eval{'S; match_apply{cons{inj[$tag:s]{'e1}; 'e2};
                        patt_apply{patt_lid[$tag:s]{patt_apply_arg{'p1}}}}} <-->
      eval{'S; match_apply{cons{'e1; 'e2}; 'p1}}

rewrite patt_apply_end_reduce :
   eval{'S; match_apply{'e1; patt_apply_end{'p1}}} <-->
      eval{'S; match_apply{'e1; 'p1}}

(*
 * Tuple pattern.
 *)
rewrite patt_tuple_reduce :
   eval{'S; match_apply{cons{"tuple"{cons{'e1; 'el1}}; 'e2}; patt_tuple{'p1}}} <-->
      eval{'S; match_apply{cons{'e1; cons{"tuple"{'el1}; 'e2}}; 'p1}}

rewrite patt_tuple_arg_reduce :
   eval{'S; match_apply{cons{"tuple"{cons{'e1; 'el1}}; 'e2}; patt_tuple_arg{'p1}}} <-->
      eval{'S; match_apply{cons{'e1; cons{"tuple"{'el1}; 'e2}}; 'p1}}

rewrite patt_tuple_end_reduce :
   eval{'S; match_apply{cons{"tuple"{nil}; 'e1}; patt_tuple_end{'p1}}} <-->
      eval{'S; match_apply{'e1; 'p1}}

(*
 * List pattern.
 *)
rewrite patt_list_reduce :
   eval{'S; match_apply{cons{list{cons{'e1; 'el1}}; 'e2}; patt_list{'p1}}} <-->
      eval{'S; match_apply{cons{'e1; cons{list{'el1}; 'e2}}; 'p1}}

rewrite patt_list_arg_reduce :
   eval{'S; match_apply{cons{list{cons{'e1; 'el1}}; 'e2}; patt_list_arg{'p1}}} <-->
      eval{'S; match_apply{cons{'e1; cons{list{'el1}; 'e2}}; 'p1}}

rewrite patt_list_end_reduce :
   eval{'S; match_apply{cons{list{nil}; 'e1}; patt_list_end{'p1}}} <-->
      eval{'S; match_apply{'e1; 'p1}}

(*
 * Record pattern.
 *)

(************************************************************************
 * FUNCTIONS                                                            *
 ************************************************************************)

(*
 * Constants.
 *)
axiom patt_char_equiv :
   sequent { 'H >- equiv{'S; 'p1; 'p2} } -->
   sequent { 'H >- equiv{'S; patt_char[$c:s]{'p1}; patt_char[$c:s]{'p2}} }

axiom patt_int_equiv :
   sequent { 'H >- equiv{'S; 'p1; 'p2} } -->
   sequent { 'H >- equiv{'S; patt_int[$i:n]; patt_int[$i:n]} }

(*
 * Variables must be the same.
 *)
axiom patt_var_equiv :
   sequent { 'H; x: term >- equiv{'S; 'p1; 'p2} }
(*
 * $Log$
 * Revision 1.2  1998/02/13 22:10:26  jyh
 * Adding pattern semantics.
 *
 * Revision 1.1  1998/02/13 16:02:21  jyh
 * Partially implemented semantics for caml.
 *
 *
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
