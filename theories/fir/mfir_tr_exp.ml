(*!
 * @begin[doc]
 * @module[Mfir_tr_exp]
 *
 * The @tt[Mfir_tr_exp] module defines the typing rules for FIR expressions.
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

prim ty_letAtom :
   sequent [fir] { 'H >- has_type["atom"]{ 'atom; 'ty1 } } -->
   sequent [fir] { 'H; b: variable; a: var_def{ 'b; 'ty1; no_def } >-
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

prim ty_letExt :
   sequent [fir] { 'H >- has_type["atom_list"]{ 'args; 'tyl } } -->
   sequent [fir] { 'H; b: variable; a: var_def{ 'b; 'u; no_def } >-
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
 * appropriate types.
 * @end[doc]
 *)

prim ty_tailCall 'H :
   sequent [fir] { 'H; a: var_def{ 'v; tyFun{'t1; 't2}; 'd }; 'J >-
      has_type["tailCall"]{ 'atoms; tyFun{ 't1; 't2 } } } -->
   sequent [fir] { 'H; a: var_def{ 'v; tyFun{'t1; 't2}; 'd }; 'J >-
      has_type["exp"]{ tailCall{ atomVar{'v}; 'atoms }; tyEnum[0] } }
   = it

prim ty_tailCall_args1 :
   sequent [fir] { 'H >- has_type["tailCall"]{ nil; tyEnum[0] } }
   = it

prim ty_tailCall_args2 :
   sequent [fir] { 'H >- has_type["atom"]{ 'h; 't1 } } -->
   sequent [fir] { 'H >- has_type["tailCall"]{ 't; 't2 } } -->
   sequent [fir] { 'H >-
      has_type["tailCall"]{ cons{ 'h; 't }; tyFun{ 't1; 't2 } } }
   = it

(*!
 * @docoff
 *)


(*!************************************
 * @begin[doc]
 * @modsubsection{Pattern matching}
 *
 * Match statements allow pattern matching on numbers, where each pattern
 * is a set of constant intervals.  Operationally, the first case for which
 * the number is a member of the cases's set is selected for execution.
 * One case must always match; that is, the list of cases for a match
 * expression cannot be empty, and they must cover all possible values
 * of the number (atom) being matched.
 *
 * (Documentation incomplete.)
 * @end[doc]
 *)

(* XXX: documentation needs to be completed. *)

prim ty_match_cases_base :
   sequent [fir] { 'H >- has_type["match_cases"]{ nil; 'ty } }
   = it

prim ty_match_cases_ind :
   sequent [fir] { 'H >- has_type["exp"]{ 'exp; 'ty } } -->
   sequent [fir] { 'H >- has_type["match_cases"]{ 'tail; 'ty } } -->
   sequent [fir] { 'H >-
      has_type["match_cases"]{ cons{ matchCase{ 'set; 'exp }; 'tail }; 'ty } }
   = it


(*!
 * @begin[doc]
 *
 * (Documentation incomplete.)
 * @end[doc]
 *)

(* XXX: documentation needs to be completed. *)

prim ty_matchExp_tyInt_atom :
   (* The  atom being matched should be well-formed. *)
   sequent [fir] { 'H >- has_type["atom"]{ atomInt{'i}; tyInt } } -->

   (* The cases should cover all of tyInt. *)
   sequent [fir] { 'H >- set_eq{ intset_max[31, "signed"];
                                 union_cases{ intset[31, "signed"]{ nil };
                                              'cases } } } -->

   (* The cases should have the right type. *)
   sequent [fir] { 'H >- has_type["match_cases"]{ 'cases; 't } } -->

   (* Then the matchExp is well-typed. *)
   sequent [fir] { 'H >-
      has_type["exp"]{ matchExp{ atomInt{'i}; 'cases }; 't } }
   = it

prim ty_matchExp_tyInt_var 'H :
   (* The cases should cover all of tyInt. *)
   sequent [fir] { 'H; a: var_def{ 'v; tyInt; 'd }; 'J >-
      set_eq{ intset_max[31, "signed"];
              union_cases{ intset[31, "signed"]{ nil }; 'cases } } } -->

   (* The cases should have the right type. *)
   sequent [fir] { 'H; a: var_def{ 'v; tyInt; 'd }; 'J >-
       has_type["match_cases"]{ 'cases; 't } } -->

   (* Then the matchExp is well-typed. *)
   sequent [fir] { 'H; a: var_def{ 'v; tyInt; 'd }; 'J >-
      has_type["exp"]{ matchExp{ atomVar{'v}; 'cases }; 't } }
   = it


(*!
 * @begin[doc]
 *
 * (Documentation incomplete.)
 * @end[doc]
 *)

(* XXX: documentation needs to be completed. *)

prim ty_matchExp_tyEnum_atom :
   (* The  atom being matched should be well-formed. *)
   sequent [fir] { 'H >-
      has_type["atom"]{ atomEnum[i:n]{'j}; tyEnum[i:n] } } -->

   (* The cases should cover all of tyEnum. *)
   sequent [fir] { 'H >-
      set_eq{ intset[31, "signed"]{ (interval{0; (number[i:n] -@ 1)} :: nil) };
              union_cases{ intset[31, "signed"]{ nil }; 'cases } } } -->

   (* The cases should have the right type. *)
   sequent [fir] { 'H >- has_type["match_cases"]{ 'cases; 't } } -->

   (* Then the matchExp is well-typed. *)
   sequent [fir] { 'H >-
      has_type["exp"]{ matchExp{ atomEnum[i:n]{'j}; 'cases }; 't } }
   = it

prim ty_matchExp_tyEnum_var 'H :
   (* The cases should cover all of tyEnum. *)
   sequent [fir] { 'H; a: var_def{ 'v; tyEnum[i:n]; 'd }; 'J >-
      set_eq{ intset[31, "signed"]{ (interval{0; (number[i:n] -@ 1)} :: nil) };
              union_cases{ intset[31, "signed"]{ nil }; 'cases } } } -->

   (* The cases should have the right type. *)
   sequent [fir] { 'H; a: var_def{ 'v; tyEnum[i:n]; 'd }; 'J >-
      has_type["match_cases"]{ 'cases; 't } } -->

   (* Then the matchExp is well-typed. *)
   sequent [fir] { 'H; a: var_def{ 'v; tyEnum[i:n]; 'd }; 'J >-
      has_type["exp"]{ matchExp{ atomVar{'v}; 'cases }; 't } }
   = it


(*!
 * @begin[doc]
 *
 * (Documentation incomplete.)
 * @end[doc]
 *)

prim ty_matchExp_tyRawInt_atom :
   (* The  atom being matched should be well-formed. *)
   sequent [fir] { 'H >-
      has_type["atom"]{ atomRawInt[p:n, s:s]{'i}; tyRawInt[p:n, s:s] } } -->

   (* The cases should cover all of tyRawInt. *)
   sequent [fir] { 'H >-
      set_eq{ intset_max[p:n, s:s];
              union_cases{ intset[p:n, s:s]{ nil }; 'cases } } } -->

   (* The cases should have the right type. *)
   sequent [fir] { 'H >- has_type["match_cases"]{ 'cases; 't } } -->

   (* Then the matchExp is well-typed. *)
   sequent [fir] { 'H >-
      has_type["exp"]{ matchExp{ atomRawInt[p:n, s:s]{'i}; 'cases }; 't } }
   = it

prim ty_matchExp_tyRawInt_var 'H :
   (* The cases should cover all of tyRawInt. *)
   sequent [fir] { 'H; a: var_def{ 'v; tyRawInt[p:n, s:s]; 'd }; 'J >-
      set_eq{ intset_max[p:n, s:s];
              union_cases{ intset[p:n, s:s]{ nil }; 'cases } } } -->

   (* The cases should have the right type. *)
   sequent [fir] { 'H; a: var_def{ 'v; tyRawInt[p:n, s:s]; 'd }; 'J >-
      has_type["match_cases"]{ 'cases; 't } } -->

   (* Then the matchExp is well-typed. *)
   sequent [fir] { 'H; a: var_def{ 'v; tyRawInt[p:n, s:s]; 'd }; 'J >-
      has_type["exp"]{ matchExp{ atomRawInt[p:n, s:s]{'i}; 'cases }; 't } }
   = it


(*!
 * @begin[doc]
 *
 * (Documentation incomplete.)
 * @end[doc]
 *)

(* XXX: documentation needs to be completed. *)

(*
 * BUG:  I'm not convinced that the three rules below are okay.
 * The problems stem from ty_matchExp_tyUnion_cases_ind.  Changing
 * the type of 'v seems like it could introduce quite a few problems.
 * Like what happens if there's multiple declarations/definitions for 'v?
 * What happens if 'v is defined with some concrete value?  Changing
 * its type could invalidate the well-formedness of the definition.
 *)

prim ty_matchExp_tyUnion_start 'H :
   sequent [fir] { 'H; a: var_def{ 'v; tyUnion{ 'tv; 'tyl; 's }; 'd }; 'J >-
      not{ set_eq{ intset[31, "signed"]{ nil }; 's } } } -->
   sequent [fir] { 'H; a: var_def{ 'v; tyUnion{ 'tv; 'tyl; 's }; 'd }; 'J >-
      set_eq{ 's; union_cases{ intset[31, "signed"]{ nil }; 'cases } } } -->
   sequent [fir] { 'H; a: var_def{ 'v; tyUnion{ 'tv; 'tyl; 's }; 'd }; 'J >-
      has_type["union_cases"]{ matchExp{ atomVar{'v}; 'cases }; 't } } -->
   sequent [fir] { 'H; a: var_def{ 'v; tyUnion{ 'tv; 'tyl; 's }; 'd }; 'J >-
      has_type["exp"]{ matchExp{ atomVar{'v}; 'cases }; 't } }
   = it

prim ty_matchExp_tyUnion_cases_base 'H :
   sequent [fir] { 'H; a: var_def{ 'v; tyUnion{ 'tv; 'tyl; 's }; 'd }; 'J >-
      has_type["union_cases"]{ matchExp{ atomVar{'v}; nil }; 't } }
   = it

prim ty_matchExp_tyUnion_cases_ind 'H :
   sequent [fir] { 'H; a: var_def{ 'v; tyUnion{ 'tv; 'tyl; 'set}; 'd}; 'J >-
      has_type["exp"]{ 'exp; 't } } -->
   sequent [fir] { 'H; a: var_def{ 'v; tyUnion{ 'tv; 'tyl; 's }; 'd }; 'J >-
      has_type["union_cases"]{ matchExp{ atomVar{'v}; 'tail }; 't } } -->
   sequent [fir] { 'H; a: var_def{ 'v; tyUnion{ 'tv; 'tyl; 's }; 'd }; 'J >-
      has_type["union_cases"]{ matchExp{ atomVar{'v};
                                         (matchCase{'set; 'exp} :: 'tail) };
                               't } }
   = it


(*!************************************
 * @begin[doc]
 * @modsubsection{Offsets}
 *
 * An offset atom should either be an integer or a raw integer.
 * Note that offsets cannot be negative, but in the case of variables,
 * this cannot be checked; variables are not defined (with some value)
 * during type checking.
 * @end[doc]
 *)

prim ty_offset_tyInt :
   sequent [fir] { 'H >- int_le{ 0; 'i } } -->
   sequent [fir] { 'H >- has_type["atom"]{ atomInt{'i}; tyInt } } -->
   sequent [fir] { 'H >- has_type["offset"]{ atomInt{'i}; offset } }
   = it

prim ty_offset_tyInt_var 'H :
   sequent [fir] { 'H; a: var_def{ 'v; tyInt; 'd }; 'J >-
      has_type["offset"]{ atomVar{'v}; offset } }
   = it

prim ty_offset_tyRawInt :
   sequent [fir] { 'H >- int_le{ 0; 'i } } -->
   sequent [fir] { 'H >- has_type["atom"]{ atomRawInt[32, "signed"]{'i};
                                           tyRawInt[32, "signed"] } } -->
   sequent [fir] { 'H >- has_type["offset"]{ atomRawInt[32, "signed"]{'i};
                                             offset } }
   = it

prim ty_offset_tyRawInt_var 'H :
   sequent [fir] { 'H; a: var_def{ 'v; tyRawInt[32, "signed"]; 'd }; 'J >-
      has_type["offset"]{ atomVar{'v}; offset } }
   = it


(*!************************************
 * @begin[doc]
 * @modsubsection{Allocation}
 *
 * The rules for the expression $<< letAlloc{ 'op; v. 'exp['v] } >>$
 * defer, when possible, to the rules for the well-formedness of
 * the value allocated.  The result of the allocation is bound to $<< 'v >>$
 * in $<< 'exp >>$.
 * @end[doc]
 *)


(*!
 * @begin[doc]
 *
 * (Documentation incomplete.)
 * @end[doc]
 *)

(* XXX: documentation needs to be completed. *)

prim ty_letAlloc_array :
   sequent [fir] { 'H >- has_type["store"]{ 'atoms; tyArray{'u} } } -->
   sequent [fir] { 'H; b: variable; a: var_def{ 'b; tyArray{'u}; no_def } >-
      has_type["exp"]{ 'exp['b]; 't } } -->
   sequent [fir] { 'H >-
      has_type["exp"]{
         letAlloc{ allocArray{ tyArray{'u}; 'atoms }; v. 'exp['v] }; 't } }
   = it


(*!
 * @begin[doc]
 *
 * (Documentation incomplete.)
 * @end[doc]
 *)

(* XXX: documentation needs to be completed. *)

prim ty_letAlloc_varray :
   sequent [fir] { 'H >- has_type["atom"]{ 'a1; tyRawInt[32, "signed"] } } -->
   sequent [fir] { 'H >- has_type["atom"]{ 'a2; 'u } } -->
   sequent [fir] { 'H; b: variable; a: var_def{ 'b; tyArray{'u}; no_def } >-
      has_type["exp"]{ 'exp['b]; 't } } -->
   sequent [fir] { 'H >-
      has_type["exp"]{
         letAlloc{ allocVArray{tyArray{'u}; 'a1; 'a2 }; v. 'exp['v] };
         't } }
   = it


(*!
 * @begin[doc]
 *
 * (Documentation incomplete.)
 * @end[doc]
 *)

(* XXX: documentation needs to be completed. *)

(*
 * NOTE: Going with the FIR type checker (version 1.56) for allocMalloc.
 *)

prim ty_letAlloc_malloc :
   sequent [fir] { 'H >-
      has_type["atom"]{ 'atom; tyRawInt[32, "signed"] } } -->
   sequent [fir] { 'H; b: variable; a: var_def{ 'b; tyRawData; no_def } >-
      has_type["exp"]{ 'exp['b]; 't } } -->
   sequent [fir] { 'H >-
      has_type["exp"]{
         letAlloc{ allocMalloc{ tyRawData; 'atom }; v. 'exp['v] };
         't } }
   = it


(*!
 * @begin[doc]
 *
 * (Documentation incomplete.)
 * @end[doc]
 *)

(* XXX: documentation needs to be completed. *)

prim ty_letAlloc_frame :
   sequent [fir] { 'H >-
      type_eq{ tyFrame{ 'tv; 'tyl }; tyFrame{ 'tv; 'tyl }; small_type } } -->
   sequent [fir] { 'H;
                   b: variable;
                   a: var_def{ 'b; tyFrame{'tv; 'tyl}; no_def } >-
      has_type["exp"]{ 'exp['b]; 't } } -->
   sequent [fir] { 'H >-
      has_type["exp"]{ letAlloc{ allocFrame{ 'tv; 'tyl }; v. 'exp['v] }; 't } }
   = it


(*!************************************
 * @begin[doc]
 * @modsubsection{Subscripting}
 *
 * (Documentation incomplete.)
 * @end[doc]
 *)

(* XXX: documentation needs to be completed. *)

prim ty_letSubscript_tyTuple 'H :
   sequent [fir] { 'H; y: var_def{ 'x; tyTuple[s:s]{'mtyl}; 'd }; 'J >-
      type_eq{ 'u;
               ty_of_mutable_ty{ nth_elt{ index_of_subscript{'a2}; 'mtyl } };
               large_type } } -->
   sequent [fir] { 'H;
                   y: var_def{ 'x; tyTuple[s:s]{'mtyl}; 'd };
                   'J;
                   p: variable;
                   q: var_def{ 'p; 'u; no_def } >-
      has_type["exp"]{ 'exp['p]; 't } } -->
   sequent [fir] { 'H; y: var_def{ 'x; tyTuple[s:s]{'mtyl}; 'd }; 'J >-
      has_type["exp"]{letSubscript{'u; atomVar{'x}; 'a2; v. 'exp['v]}; 't} }
   = it

prim ty_setSubscript_tyTuple 'H :
   sequent [fir] { 'H; y: var_def{ 'x; tyTuple[s:s]{'mtyl}; 'd }; 'J >-
      type_eq{ mutable_ty{ 'u; "true" };
               nth_elt{ index_of_subscript{'a2}; 'mtyl };
               large_type } } -->
   sequent [fir] { 'H; y: var_def{ 'x; tyTuple[s:s]{'mtyl}; 'd }; 'J >-
      has_type["atom"]{ 'a3; 'u } } -->
   sequent [fir] { 'H; y: var_def{ 'x; tyTuple[s:s]{'mtyl}; 'd }; 'J >-
      has_type["exp"]{ 'exp; 't } } -->
   sequent [fir] { 'H; y: var_def{ 'x; tyTuple[s:s]{'mtyl}; 'd }; 'J >-
      has_type["exp"]{setSubscript{atomVar{'x}; 'a2; 'u; 'a3; 'exp}; 't} }
   = it


(*!
 * @begin[doc]
 *
 * (Documentation incomplete.)
 * @end[doc]
 *)

(* XXX: documentation needs to be completed. *)

prim ty_letSubsript_tyArray :
   sequent [fir] { 'H >- has_type["atom"]{ 'a1; tyArray{ 'u } } } -->
   sequent [fir] { 'H >- has_type["offset"]{ 'a2; offset } } -->
   sequent [fir] { 'H; b: variable; a: var_def{ 'b; 'u; no_def } >-
      has_type["exp"]{ 'exp['b]; 't } } -->
   sequent [fir] { 'H >-
      has_type["exp"]{ letSubscript{ 'u; 'a1; 'a2; v. 'exp['v] }; 't } }
   = it

prim ty_setSubscript_tyArray :
   sequent [fir] { 'H >- has_type["atom"]{ 'a1; tyArray{ 'u } } } -->
   sequent [fir] { 'H >- has_type["offset"]{ 'a2; offset } } -->
   sequent [fir] { 'H >- has_type["atom"]{ 'a3; 'u } } -->
   sequent [fir] { 'H >- has_type["exp"]{ 'exp; 't } } -->
   sequent [fir] { 'H >-
      has_type["exp"]{ setSubscript{ 'a1; 'a2; 'u; 'a3; 'exp }; 't } }
   = it


(*!
 * @begin[doc]
 *
 * (Documentation incomplete.)
 * @end[doc]
 *)

(* XXX: documentation needs to be completed. *)
(* XXX: union subscripting rules need to be completed. *)

(*
prim ty_letSubscript_tyUnion 'H :
   sequent [fir] { 'H; y: var_def{ 'x;
   = it
*)


(*!
 * @begin[doc]
 *
 * (Documentation incomplete.)
 * @end[doc]
 *)

(* XXX: documentation needs to be completed. *)

prim ty_letSubscript_rawData :
   sequent [fir] { 'H >- has_type["atom"]{ 'a1; tyRawData } } -->
   sequent [fir] { 'H >- has_type["offset"]{ 'a2; offset } } -->
   sequent [fir] { 'H; b: variable; a: var_def{ 'b; 'u; no_def } >-
      has_type["exp"]{ 'exp['b]; 't } } -->
   sequent [fir] { 'H >-
      has_type["exp"]{ letSubscript{ 'u; 'a1; 'a2; v. 'exp['v] }; 't } }
   = it

prim ty_setSubscript_rawdata :
   sequent [fir] { 'H >- has_type["atom"]{ 'a1; tyRawData } } -->
   sequent [fir] { 'H >- has_type["offset"]{ 'a2; offset } } -->
   sequent [fir] { 'H >- has_type["atom"]{ 'a3; 'u } } -->
   sequent [fir] { 'H >- has_type["exp"]{ 'exp; 't } } -->
   sequent [fir] { 'H >-
      has_type["exp"]{ setSubscript{ 'a1; 'a2; 'u; 'a3; 'exp };'t } }
   = it


(*!
 * @begin[doc]
 *
 * (Documentation incomplete.)
 * @end[doc]
 *)

(* XXX: documentation needs to be completed. *)
(* XXX: frame subscripting rules need to be completed. *)


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

prim ty_label 'H :
   sequent [fir] { 'H; a: global_def{ 'l; 'ty; 'd }; 'J >-
      has_type["label"]{ 'l; 'ty } }
   = it

prim ty_letGlobal :
   sequent [fir] { 'H >- has_type["label"]{ 'label; 'ty1 } } -->
   sequent [fir] { 'H; b: global; a: var_def{ 'b; 'ty1; no_def } >-
      has_type["exp"]{ 'exp['b]; 'ty2 } } -->
   sequent [fir] { 'H >-
      has_type["exp"]{ letGlobal{ 'ty1; 'label; v. 'exp['v] }; 'ty2 } }
   = it

prim ty_setGlobal :
   sequent [fir] { 'H >- has_type["label"]{ 'label; 'ty1 } } -->
   sequent [fir] { 'H >- has_type["atom"]{ 'atom; 'ty1 } } -->
   sequent [fir] { 'H >- has_type["exp"]{ 'exp; 'ty2 } } -->
   sequent [fir] { 'H >-
      has_type["exp"]{ setGlobal{ 'label; 'ty1; 'atom; 'exp }; 'ty2 } }
   = it

(*!
 * @docoff
 *)
