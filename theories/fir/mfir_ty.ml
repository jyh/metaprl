(*!
 * @spelling{th ty tyRawInt tyFloat tyApply tyEnum var}
 *
 * @begin[doc]
 * @module[Mfir_ty]
 *
 * The @tt[Mfir_ty] module declares terms to represent the FIR type system.
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

extends Base_theory
extends Mfir_basic

(**************************************************************************
 * Declarations.
 **************************************************************************)

(*
 * DROPPED: TyPointer.        Not worrying about this optimization.
 * TODO:    TyFrame.          I'm confused.
 * DROPPED: TyCase.           Part of the (unsound) FIR object system.
 * DROPPED: TyObject.         Part of the (unsound) FIR object system.
 * DROPPED: TyDelayed.        Not doing type inference.
 * TODO:    frame.            I'm confused.
 * TODO:    TyDefLambda.      I'm lazy.
 * TODO:    TyDefUnion.       I'm lazy.
 * TODO:    union_class.      I'm lazy.
 *)

(*!
 * @begin[doc]
 * @terms
 * @modsubsection{Numbers}
 *
 * The type @tt[tyInt] refers to signed, 31-bit, ML-style integers.  The type
 * @tt{tyEnum[i:n]} includes the integers $@{0,@ldots,i-1@}$.  The native
 * integer type @tt{tyRawInt[precision:n, sign:s]} includes integers of
 * varying bit precisions (8, 16, 32, and 64) and signedness (``signed'' or
 * ``unsigned'').  The type @tt{tyFloat[precision:n]} includes floating-point
 * values of a specified bit-precision (32, 64, or 80).
 * @end[doc]
 *)

declare tyInt
declare tyEnum[i:n]
declare tyRawInt[precision:n, sign:s]
declare tyFloat[precision:n]

(*!
 * @begin[doc]
 * @modsubsection{Functions}
 *
 * If @tt[arg_type_list] is a list of types of length $n$, then @tt[tyFun] is
 * the type of functions taking $n$ arguments (with the types in
 * @tt[arg_type_list]), and returning a value of type @tt[res_type]. A
 * function may take no arguments.
 * @end[doc]
 *)

declare tyFun{ 'arg_type_list; 'res_type }

(*!
 * @begin[doc]
 * @modsubsection{Aggregate data}
 *
 * The type @tt[tyUnion] represents values in a polymorphic union type.  The
 * @tt[ty_var] subterm refers to a polymorphic union definition (see
 * @hrefterm[tyDefUnion]), which is instantiated at the types in @tt[ty_list].
 * The third subterm is an integer set that selects a subset of the union
 * cases.  Union cases are indexed starting at zero.
 * @end[doc]
 *)

declare tyUnion{ 'ty_var; 'ty_list; 'intset }

(*!
 * @begin[doc]
 *
 * The type @tt[tyTuple] represents tuples with arity $n$ if @tt[ty_list]
 * is a list of $n$ types. The parameter @tt[tc] is a tuple class, which
 * can either be ``normal'' or ``box''.  ``box'' tuples must always have
 * arity one, and are used pass arbitrary values (such as floating-point
 * values or raw integers) as polymorphic values.
 * @end[doc]
 *)

declare tyTuple[tc:s]{ 'ty_list }

(*!
 * @begin[doc]
 *
 * Arrays are similar to tuples, except all the elements of an array have the
 * same type, and arrays may have arbitrary, non-negative dimension.
 * @end[doc]
 *)

declare tyArray{ 'ty }

(*!
 * @begin[doc]
 *
 * The unsafe type @tt[tyRawData] represents arbitrary data.  It is commonly
 * used to represent data aggregates in imperative programming languages, such
 * as C, that allow assignment of values to a data area without regard for the
 * type.
 * @end[doc]
 *) declare tyRawData

(*!
 * @begin[doc]
 * @modsubsection{Polymorphism}
 *
 * The term @tt[tyVar] represents a type variable.
 * @end[doc]
 *)

declare tyVar{ 'ty_var }

(*!
 * @begin[doc]
 *
 * The term @tt{tyApply@{'ty_var@; 'ty_list@}} applies the types @tt[ty_list]
 * to a type function given by @tt[ty_var].
 * @end[doc]
 *)

declare tyApply{ 'ty_var; 'ty_list }

(*!
 * @begin[doc]
 *
 * The existential type @tt[tyExists] defines a type @tt[ty] abstracted over
 * the types in the list @tt[ty_var_list].  The term @tt[tyAll] defines a
 * polymorphic type, where @tt[ty] is restricted to be a function type. This
 * corresponds to value restriction @cite["ullman:sml"].
 * @end[doc]
 *)

declare tyExists{ 'ty_var_list; 'ty }
declare tyAll{ 'ty_var_list; 'ty }

(*!
 * @begin[doc]
 *
 * If @tt[var] is a ``packed'' existential value (see @hrefterm[atomTyPack]),
 * then the term @tt[tyProject] is the $i^{th}$ type in the packing, where
 * indexing starts at zero.
 * @end[doc]
 *)

declare tyProject[i:n]{ 'var }

(*!
 * @docoff
 *)

(**************************************************************************
 * Display forms.
 **************************************************************************)

(*
 * Numbers.
 *)

dform tyInt_df : except_mode[src] ::
   tyInt =
   mathbbZ sub{31}

dform tyEnum_df : except_mode[src] ::
   tyEnum[i:n] =
   bf["enum"] sub{slot[i:n]}

dform tyRawInt_df : except_mode[src] ::
   tyRawInt[precision:n, sign:s] =
   mathbbZ sub{slot[precision:n]} sup{slot[sign:s]}

dform tyFloat_df : except_mode[src] ::
   tyFloat[precision:n] =
   mathbbR sub{slot[precision:n]}

(*
 * Functions.
 *)

dform tyFun_df : except_mode[src] ::
   tyFun{ 'arg_type_list; 'res_type } =
   `"(" slot{'arg_type_list} rightarrow slot{'res_type} `")"

(*
 * Aggregate data.
 *)

dform tyUnion_df : except_mode[src] ::
   tyUnion{ 'ty_var; 'ty_list; 'intset } =
   bf["union"] `"(" slot{'ty_var} slot{'ty_list} `", " slot{'intset} `")"

dform tyTuple_df : except_mode[src] ::
   tyTuple[tc:s]{ 'ty_list } =
   slot{'ty_list} sub{bf[tc:s]}

dform tyArray_df : except_mode[src] ::
   tyArray{ 'ty } =
   `"(" slot{'ty} `" " bf["array"] `")"

dform tyRawData_df : except_mode[src] ::
   tyRawData =
   bf["data"]

(*
 * Polymorphism.
 *)

dform tyVar_df : except_mode[src] ::
   tyVar{ 'ty_var } =
   slot{'ty_var}

dform tyApply_df : except_mode[src] ::
   tyApply{ 'ty_var; 'ty_list } =
   slot{'ty_var} slot{'ty_list}

dform tyExists_df : except_mode[src] ::
   tyExists{ 'ty_var_list; 'ty } =
   exists slot{'ty_var_list} `". " slot{'ty}

dform tyAll_df : except_mode[src] ::
   tyAll{ 'ty_var_list; 'ty } =
   forall slot{'ty_var_list} `". " slot{'ty}

dform tyProject_df : except_mode[src] ::
   tyProject[i:n]{ 'var } =
   slot{'var} `"." slot[i:n]
