(*!
 * @begin[doc]
 * @module[Mfir_tr_exp]
 *
 * The @tt[Mfir_tr_exp] module defines the typing rules for expressions.
 * @end[doc]
 *
 * ------------------------------------------------------------------------
 *
 * @begin[license]
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.  Additional
 * information about the system is available at
 * http://www.metaprl.org/
 *
 * Copyright (C) 2002 Brian Emre Aydemir, Caltech
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
 * Author: Brian Emre Aydemir
 * @email{emre@cs.caltech.edu}
 * @end[license]
 *)

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)

extends Mfir_ty
extends Mfir_exp
extends Mfir_sequent
extends Mfir_tr_base
extends Mfir_tr_types
extends Mfir_tr_atom
extends Mfir_tr_store


(**************************************************************************
 * Rules.
 **************************************************************************)

(*!
 * @begin[doc]
 * @rules
 * @modsubsection{Basic expressions}
 *
 * Operationally, the $<< letAtom{ 'ty1; 'atom; v. 'exp['v] } >>$ expression
 * binds $<< 'atom >>$ to $<< 'v >>$ in $<< 'exp >>$.  The expression has type
 * $<< 'ty2 >>$ if $<< 'atom >>$ has type $<< 'ty1 >>$, and $<< 'exp['v] >>$
 * has type $<< 'ty2 >>$ assuming that $<< 'v >>$ has type $<< 'ty1 >>$.
 * @end[doc]
 *)

prim ty_letAtom 'H 'a 'b :
   sequent [fir] { 'H >- has_type["atom"]{ 'atom; 'ty1 } } -->
   sequent [fir] { 'H; a: var_def{ 'b; 'ty1; no_def } >-
      has_type["exp"]{ 'exp['b]; 'ty2 } } -->
   sequent [fir] { 'H >-
      has_type["exp"]{ letAtom{ 'ty1; 'atom; v. 'exp['v] }; 'ty2 } }
   = it

(*!
 * @begin[doc]
 *
 * The expression $<< letExt[str:s]{ 'u; 'tyl; 'args; v. 'exp['v] } >>$ binds
 * the result of a call to an external (e.g.~standard library) function
 * $<< 'str >>$ to $<< 'v >>$ in $<< 'exp >>$.  We make no attempt to see that
 * the types in the expression correspond to the actual types for the function
 * @tt[str].
 * @end[doc]
 *)

prim ty_letExt 'H 'a 'b :
   sequent [fir] { 'H >- has_type["atom_list"]{ 'args; 'tyl } } -->
   sequent [fir] { 'H; a: var_def{ 'b; 'u; no_def } >-
      has_type["exp"]{ 'exp['b]; 't } } -->
   sequent [fir] { 'H >-
      has_type["exp"]{ letExt[str:s]{ 'u; 'tyl; 'args; v. 'exp['v] };
                       't } }
   = it

(*!
 * @begin[doc]
 *
 * The next three rules assume that FIR programs are written in continuation
 * passing style.  A function call is well-formed if the variable
 * $<< atomVar{'v} >>$ is a function, and if the arguments have the
 * appropriate types.  Note that the type of $<< atomVar{'v} >>$ must be a
 * function type that ``returns'' a value of type $<< tyEnum[0] >>$. Note
 * that in the two auxilary rules below (@tt[ty_tailCall_args1] and
 * @tt[ty_tailCall_args2]), the well-formedness of the types is ensured by the
 * sequent used in the application of the @tt[ty_tailCall] rule.
 * @end[doc]
 *)

prim ty_tailCall 'H 'J :
   sequent [fir] { 'H; a: var_def{ 'v; tyFun{'t1; 't2}; no_def }; 'J >-
      has_type["tailCall"]{ 'atoms; tyFun{ 't1; 't2 } } } -->
   sequent [fir] { 'H; a: var_def{ 'v; tyFun{'t1; 't2}; no_def }; 'J >-
      has_type["exp"]{ tailCall{ atomVar{'v}; 'atoms }; tyEnum[0] } }
   = it

prim ty_tailCall_args1 'H :
   sequent [fir] { 'H >- has_type["tailCall"]{ nil; tyEnum[0] } }
   = it

prim ty_tailCall_args2 'H :
   sequent [fir] { 'H >- has_type["atom"]{ 'h; 't1 } } -->
   sequent [fir] { 'H >- has_type["tailCall"]{ 't; 't2 } } -->
   sequent [fir] { 'H >-
      has_type["tailCall"]{ cons{ 'h; 't }; tyFun{ 't1; 't2 } } }
   = it

(*!
 * @docoff
 *)


(*
 * The term check_cases is used to check the cases of a match expression.
 *)

declare check_cases{ 'ty; 'cases }


(*!************************************
 * @begin[doc]
 * @modsubsection{Pattern matching}
 *
 * Match statements allow pattern matching on numbers, where each pattern
 * is a set of constant intervals.  Operationally, the first case for which
 * the number is a member of the cases's set is selected for execution.
 * One case must always match; that is, the list of cases for a match
 * expression cannot be empty, and the must cover all possible values
 * of the number (atom) being matched.
 *
 * The next two rules are used to check that the expression in each case
 * has the appropriate type.
 * @end[doc]
 *)

prim ty_check_cases_base 'H :
   sequent [fir] { 'H >- check_cases{ 'ty; nil } }
   = it

prim ty_check_cases_ind 'H :
   sequent [fir] { 'H >- has_type["exp"]{ 'exp; 'ty } } -->
   sequent [fir] { 'H >- check_cases{ 'ty; 'tail } } -->
   sequent [fir] { 'H >- check_cases{ 'ty; cons{ matchCase{ 'set; 'exp };
                                                 'tail } } }
   = it

(*!
 * @begin[doc]
 *
 * The next three rules are fairly straightforward.
 * @end[doc]
 *)

(*
prim ty_matchExp_tyInt 'H :
   (* The  atom being matched should be well-formed. *)
   sequent [fir] { 'H >- has_type["atom"]{ atomInt{'i}; tyInt } } -->

   (* The cases should cover all of tyInt. *)
   sequent [fir] { 'H >- set_eq{ intset_max[31, "signed"];
                                 union_cases{ intset[31, "signed"]{ nil };
                                              'cases } } } -->

   (* The cases should have the right type. *)
   sequent [fir] { 'H >- check_cases{ 't; 'cases } } -->

   (* Then the matchExp is well-typed. *)
   sequent [fir] { 'H >- has_type["exp"]{ matchExp{ atomInt{'i}; 'cases };
                                          't } }
   = it

prim ty_matchExp_tyEnum 'H :
   (* The  atom being matched should be well-formed. *)
   sequent [fir] { 'H >-
      has_type["atom"]{ atomEnum[i:n]{'j}; tyEnum[i:n] } } -->

   (* The cases should cover all of tyEnum. *)
   sequent [fir] { 'H >-
      set_eq{ intset[31, "signed"]{ cons{ interval{ 0; (number[i:n] -@ 1) };
                                          nil } };
              union_cases{ intset[31, "signed"]{ nil }; 'cases } } } -->

   (* The cases should have the right type. *)
   sequent [fir] { 'H >- check_cases{ 't; 'cases } } -->

   (* Then the matchExp is well-typed. *)
   sequent [fir] { 'H >-
      has_type["exp"]{ matchExp{ atomEnum[i:n]{'j}; 'cases };
                       't } }
   = it

prim ty_matchExp_tyRawInt {| intro [] |} 'H :
   (* The  atom being matched should be well-formed. *)
   sequent [fir] { 'H >-
      has_type["atom"]{ atomRawInt[p:n, s:s]{'i}; tyRawInt[p:n, s:s] } } -->

   (* The cases should cover all of tyRawInt. *)
   sequent [fir] { 'H >- set_eq{ intset_max[p:n, s:s];
                                 union_cases{ intset[p:n, s:s]{ nil };
                                              'cases } } } -->

   (* The cases should have the right type. *)
   sequent [fir] { 'H >- check_cases{ 't; 'cases } } -->

   (* Then the matchExp is well-typed. *)
   sequent [fir] { 'H >-
      has_type["exp"]{ matchExp{ atomRawInt[p:n, s:s]{'i}; 'cases };
                       't } }
   = it
*)


(*!
 * @begin[doc]
 *
 * The typing rules for matching a union values are the only difficult
 * cases for match statements.  The expression in each case must
 * have the given type, given the restricted type for the variable
 * being matched.
 * @end[doc]
 *)

(* NOTE: I'm using the technical report rule for union values here. *)

(*
prim ty_matchExp_tyUnion_start 'H 'J :
   sequent [mfir] { 'H; v: var_def{ tyUnion{ 'tv; 'tyl; 's }; 'd }; 'J['v] >-
      not{ set_eq{ intset[31, "signed"]{ nil }; 's } } } -->
   sequent [mfir] { 'H; v: var_def{ tyUnion{ 'tv; 'tyl; 's }; 'd }; 'J['v] >-
      set_eq{ 's; union_cases{ intset[31, "signed"]{ nil }; 'cases } } } -->
   sequent [hack] { 'H; v: var_def{ tyUnion{ 'tv; 'tyl; 's }; 'd }; 'J['v] >-
      has_type["exp"]{ matchExp{ atomVar{'v}; 'cases }; 't } } -->
   sequent [mfir] { 'H; v: var_def{ tyUnion{ 'tv; 'tyl; 's }; 'd }; 'J['v] >-
      has_type["exp"]{ matchExp{ atomVar{'v}; 'cases }; 't } }
   = it

prim ty_matchExp_tyUnion_cases_base 'H 'J :
   sequent [hack] { 'H; v: var_def{ tyUnion{ 'tv; 'tyl; 's }; 'd }; 'J['v] >-
      has_type["exp"]{ matchExp{ atomVar{'v}; nil }; 't } }
   = it
*)

(*
 * BUG: The following is just wrong given the current semantics
 * of sequents we're using.
 *)

(*
prim ty_matchExp_tyUnion_cases_ind 'H 'J :
   sequent [mfir] { 'H; v: var_def{ tyUnion{ 'tv; 'tyl; 'set}; 'd}; 'J['v] >-
      has_type["exp"]{ 'exp; 't } } -->
   sequent [hack] { 'H; v: var_def{ tyUnion{ 'tv; 'tyl; 's }; 'd }; 'J['v] >-
      has_type["exp"]{ matchExp{ atomVar{'v}; 'tail };
                       't } } -->
   sequent [hack] { 'H; v: var_def{ tyUnion{ 'tv; 'tyl; 's }; 'd }; 'J['v] >-
      has_type["exp"]{ matchExp{ atomVar{'v};
                                 cons{ matchCase{ 'set; 'exp }; 'tail } };
                       't } }
   = it
*)


(*!************************************
 * @begin[doc]
 * @modsubsection{Allocation}
 *
 * An offset atom should either be an integer or a raw integer.
 * Note that offsets cannot be negative, but in the case of variables,
 * this cannot be checked.
 * @end[doc]
 *)

(*
prim ty_offset_tyInt 'H :
   sequent [mfir] { 'H >- int_le{ 0; 'i } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ atomInt{'i}; tyInt } } -->
   sequent [mfir] { 'H >- has_type["offset"]{ atomInt{'i}; offset } }
   = it

prim ty_offset_tyInt_var 'H 'J :
   sequent [mfir] { 'H; v: var_def{ tyInt; 'd }; 'J['v] >-
      has_type["offset"]{ atomVar{'v}; offset } }
   = it

prim ty_offset_tyRawInt {| intro [] |} 'H :
   sequent [mfir] { 'H >- int_le{ 0; 'i } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ atomRawInt[32, "signed"]{'i};
                                            tyRawInt[32, "signed"] } } -->
   sequent [mfir] { 'H >- has_type["offset"]{ atomRawInt[32, "signed"]{'i};
                                              offset } }
   = it

prim ty_offset_tyRawInt_var 'H 'J :
   sequent [mfir] { 'H; v: var_def{ tyRawInt[32, "signed"]; 'd }; 'J['v] >-
      has_type["offset"]{ atomVar{'v}; offset } }
   = it
*)


(*!
 * @begin[doc]
 *
 * The rules for the expression $<< letAlloc{ 'op; v. 'exp['v] } >>$
 * defer, when possible, to the rules for the well-formedness of
 * the value allocated.  The result of the allocation is bound to $<< 'v >>$
 * in $<< 'exp >>$.
 * @end[doc]
 *)

(*
prim ty_letAlloc_tuple 'H 'a :
   sequent [mfir] { 'H >- has_type["store"]{'atoms; tyTuple[tc:s]{'tyl}} } -->
   sequent [mfir] { 'H; a: var_def{ tyTuple[tc:s]{'tyl}; no_def } >-
      has_type["exp"]{ 'exp['a]; 't } } -->
   sequent [mfir] { 'H >-
      has_type["exp"]{
         letAlloc{allocTuple[tc:s]{tyTuple[tc:s]{'tyl}; 'atoms}; v. 'exp['v]};
         't } }
   = it

prim ty_letAlloc_union 'H 'a :
   sequent [mfir] { 'H >-
      has_type["store"]{ union_val[i:n]{ 'tv; 'atoms }; 'ty } } -->
   sequent [mfir] { 'H; a: var_def{ 'ty; no_def } >-
      has_type["exp"]{ 'exp['a]; 't } } -->
   sequent [mfir] { 'H >-
      has_type["exp"]{
         letAlloc{ allocUnion[i:n]{ 'ty; 'tv; 'atoms }; v. 'exp['v] };
         't } }
   = it
*)


(*!
 * @begin[doc]
 *
 * For array and raw data allocation, we only validate the size
 * of the area allocated, and in the case of arrays, the initializer value.
 * @end[doc]
 *)

(*
prim ty_letAlloc_varray 'H 'a :
   sequent [mfir] { 'H >- has_type["offset"]{ 'a1; offset } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a2; 'u } } -->
   sequent [mfir] { 'H; a: var_def{ tyArray{'u}; no_def } >-
      has_type["exp"]{ 'exp['a]; 't } } -->
   sequent [mfir] { 'H >-
      has_type["exp"]{
         letAlloc{ allocVArray{tyArray{'u}; 'a1; 'a2 }; v. 'exp['v] };
         't } }
   = it

prim ty_letAlloc_malloc 'H 'a :
   sequent [mfir] { 'H >- has_type["offset"]{ 'atom; offset } } -->
   sequent [mfir] { 'H; a: var_def{ tyRawData; no_def } >-
      has_type["exp"]{ 'exp['a]; 't } } -->
   sequent [mfir] { 'H >-
      has_type["exp"]{
         letAlloc{ allocMalloc{ tyRawData; 'atom }; v. 'exp['v] };
         't } }
   = it
*)


(*!************************************
 * @begin[doc]
 * @modsubsection{Subscripting}
 *
 * XXX Some sort of documentation needs to go here.
 * @end[doc]
 *)

(*
prim ty_letSubscript_tyTuple 'H 'J 'a :
   sequent [mfir] { 'H; x: var_def{ tyTuple[s:s]{'tyl}; 'd }; 'J['x] >-
      type_eq{ 'u;
               nth_elt{ index_of_subscript{'a2}; 'tyl };
               large_type } } -->
   sequent [mfir] { 'H;
                    x: var_def{ tyTuple[s:s]{'tyl}; 'd };
                    'J['x];
                    a: var_def{ 'u; no_def } >-
      has_type["exp"]{ 'exp['a]; 't } } -->
   sequent [mfir] { 'H; x: var_def{ tyTuple[s:s]{'tyl}; 'd }; 'J['x] >-
      has_type["exp"]{letSubscript{'u; atomVar{'x}; 'a2; v. 'exp['v]}; 't} }
   = it

prim ty_setSubscript_tyTuple 'H 'J :
   sequent [mfir] { 'H; x: var_def{ tyTuple[s:s]{'tyl}; 'd }; 'J['x] >-
      type_eq{ 'u;
               nth_elt{ index_of_subscript{'a2}; 'tyl };
               large_type } } -->
   sequent [mfir] { 'H; x: var_def{ tyTuple[s:s]{'tyl}; 'd }; 'J['x] >-
      has_type["atom"]{ 'a3; 'u } } -->
   sequent [mfir] { 'H; x: var_def{ tyTuple[s:s]{'tyl}; 'd }; 'J['x] >-
      has_type["exp"]{ 'exp; 't } } -->
   sequent [mfir] { 'H; x: var_def{ tyTuple[s:s]{'tyl}; 'd }; 'J['x] >-
      has_type["exp"]{setSubscript{atomVar{'x}; 'a2; 'u; 'a3; 'exp}; 't} }
   = it
*)


(*!
 * @begin[doc]
 *
 * XXX arrays are easy!
 * @end[doc]
 *)

(*
prim ty_letSubsript_tyArray {| intro [] |} 'H 'a :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyArray{ 'u } } } -->
   sequent [mfir] { 'H >- has_type["offset"]{ 'a2; offset } } -->
   sequent [mfir] { 'H; a: var_def{ 'u; no_def } >-
      has_type["exp"]{ 'exp['a]; 't } } -->
   sequent [mfir] { 'H >-
      has_type["exp"]{ letSubscript{ 'u; 'a1; 'a2; v. 'exp['v] }; 't } }
   = it

prim ty_setSubscript_tyArray {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyArray{ 'u } } } -->
   sequent [mfir] { 'H >- has_type["offset"]{ 'a2; offset } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a3; 'u } } -->
   sequent [mfir] { 'H >- has_type["exp"]{ 'exp; 't } } -->
   sequent [mfir] { 'H >-
      has_type["exp"]{ setSubscript{ 'a1; 'a2; 'u; 'a3; 'exp }; 't } }
   = it
*)

(*!
 * @begin[doc]
 *
 * XXX unions are icky
 * @end[doc]
 *)

(* XXX union subscripting *)

(*!
 * @begin[doc]
 *
 * XXX rawdata is fun!
 * @end[doc]
 *)

(*
prim ty_letSubscript_rawData {| intro [] |} 'H 'a :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyRawData } } -->
   sequent [mfir] { 'H >- has_type["offset"]{ 'a2; offset } } -->
   sequent [mfir] { 'H; a: var_def{ 'u; no_def } >-
      has_type["exp"]{ 'exp['a]; 't } } -->
   sequent [mfir] { 'H >-
      has_type["exp"]{ letSubscript{ 'u; 'a1; 'a2; v. 'exp['v] }; 't } }
   = it

prim ty_setSubscript_rawdata {| intro [] |} 'H :
   sequent [mfir] { 'H >- has_type["atom"]{ 'a1; tyRawData } } -->
   sequent [mfir] { 'H >- has_type["offset"]{ 'a2; offset } } -->
   sequent [mfir] { 'H >- has_type["atom"]{ 'a3; 'u } } -->
   sequent [mfir] { 'H >- has_type["exp"]{ 'exp; 't } } -->
   sequent [mfir] { 'H >-
      has_type["exp"]{ setSubscript{ 'a1; 'a2; 'u; 'a3; 'exp };'t } }
   = it
*)


(*!************************************
 * @begin[doc]
 * @modsubsection{Globals}
 *
 * The expression $<< letGlobal{ 'ty1; 'label; v. 'exp['v] } >>$ is used to
 * read a global value, and the expression
 * $<< setGlobal{ 'label; 'ty1; 'atom; 'exp } >>$ is used to set a global
 * value.  There is no way to use global values directly.  The typing rules
 * for these expressions are straightforward.
 * @end[doc]
 *)

prim ty_label 'H 'J :
   sequent [fir] { 'H; a: global_def{ 'l; 'ty; 'd }; 'J >-
      has_type["label"]{ 'l; 'ty } }
   = it

prim ty_letGlobal 'H 'a 'b :
   sequent [fir] { 'H >- has_type["label"]{ 'label; 'ty1 } } -->
   sequent [fir] { 'H; a: var_def{ 'b; 'ty1; no_def } >-
      has_type["exp"]{ 'exp['b]; 'ty2 } } -->
   sequent [fir] { 'H >-
      has_type["exp"]{ letGlobal{ 'ty1; 'label; v. 'exp['v] }; 'ty2 } }
   = it

prim ty_setGlobal 'H :
   sequent [fir] { 'H >- has_type["label"]{ 'label; 'ty1 } } -->
   sequent [fir] { 'H >- has_type["atom"]{ 'atom; 'ty1 } } -->
   sequent [fir] { 'H >- has_type["exp"]{ 'exp; 'ty2 } } -->
   sequent [fir] { 'H >-
      has_type["exp"]{ setGlobal{ 'label; 'ty1; 'atom; 'exp }; 'ty2 } }
   = it

(*!
 * @docoff
 *)


(**************************************************************************
 * Display forms.
 **************************************************************************)

dform check_cases_df : except_mode[src] ::
   check_cases{ 'ty; 'cases } =
   bf["check_cases"] `"(" slot{'ty} `"," slot{'cases} `")"
