doc <:doc< 
   @spelling{rawdata th tyEnum}
  
   @begin[doc]
   @module[Mfir_ty]
  
   The @tt[Mfir_ty] module declares terms to represent the FIR type system.
   @end[doc]
  
   ------------------------------------------------------------------------
  
   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.  Additional
   information about the system is available at
   http://www.metaprl.org/
  
   Copyright (C) 2002 Brian Emre Aydemir, Caltech
  
   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License
   as published by the Free Software Foundation; either version 2
   of the License, or (at your option) any later version.
  
   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.
  
   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
  
   Author: Brian Emre Aydemir
   @email{emre@cs.caltech.edu}
   @end[license]
>>

doc <:doc< 
   @begin[doc]
   @parents
   @end[doc]
>>

extends Mfir_int
extends Mfir_list

doc <:doc< 
   @docoff
>>

open Top_conversionals


(**************************************************************************
 * Declarations.
 **************************************************************************)

doc <:doc< 
   @begin[doc]
   @terms
   @modsubsection{Mutable types}
  
   The fields in tuples, unions, and dependent tuples are allowed to be
   mutable.  (The fields in an array are always mutable.)  The flags
   @tt[mutable] and @tt[immutable] declare a field to be mutable and
   immutable, respectively.  The term @tt[mutable_ty] is used as the type
   of a field; it combines a type with a flag indicating the
   field's mutability.
   @end[doc]
>>

declare "mutable"
declare immutable
declare mutable_ty{ 'ty; 'flag }


doc <:doc< ************************************
   @begin[doc]
   @modsubsection{Type definitions}
  
   Type definitions define parameterized types, unions, frames, and dependent
   tuples.  The term @tt[tyDefPoly] abstracts a type @tt[ty] over @tt[t].
   @end[doc]
>>

declare tyDefPoly{ t. 'ty['t] }


doc <:doc< 
   @begin[doc]
  
   Frames are defined as records, where each field is a record whose data
   consists of @tt[frameSubField] terms.
   @end[doc]
>>

declare frameSubField{ 'ty; 'num }


doc <:doc< 
   @begin[doc]
  
   The term @tt[tyDefUnion] is used to define a disjoint union.  The subterm
   @tt[cases] is the list of cases in the union, and it should be a list of
   lists of @tt[mutable_ty] terms.  A union case can be viewed as a tuple
   space in which each field is tagged with a flag indicating its mutability.
   @end[doc]
>>

declare tyDefUnion{ 'cases }


doc <:doc< 
   @begin[doc]
  
   (Documentation incomplete.)
   @end[doc]
>>

(* XXX: documentation needs to be completed. *)

declare tyDefDTuple{ 'ty_var }


doc <:doc< ************************************
   @begin[doc]
   @modsubsection{Numbers}
  
   The type @tt[tyInt] includes all signed, 31-bit integers.  The type
   @tt{tyEnum[i:n]} includes the integers $@{0,@ldots,i-1@}$.  The
   type @tt[tyRawInt] includes integers of varying bit precisions (8, 16, 32,
   and 64) and signedness (``signed'' or ``unsigned'').  The type @tt[tyFloat]
   includes floating-point values of a specified bit-precision (32, 64, or
   80).
   @end[doc]
>>

declare tyInt
declare tyEnum[i:n]
declare tyRawInt[precision:n, sign:s]
declare tyFloat[precision:n]


doc <:doc< ************************************
   @begin[doc]
   @modsubsection{Functions}
  
   The type @tt[tyFun] represents functions that take an argument of
   type @tt[arg_type], and return a result of type @tt[res_type].
   @end[doc]
>>

declare tyFun{ 'arg_type; 'res_type }


doc <:doc< ************************************
   @begin[doc]
   @modsubsection{Tuples}
  
   The type @tt[tyUnion] represents values in a polymorphic union type.  The
   integer set @tt[intset] selects a subset of the cases of a polymorphic
   union definition given by @tt[ty_var].  Indexing of union cases starts
   at zero.  The union definition is instantiated at the types in the
   list @tt[ty_list].
   @end[doc]
>>

declare tyUnion{ 'ty_var; 'ty_list; 'intset }


doc <:doc< 
   @begin[doc]
  
   The type @tt[tyTuple] represents tuples with arity $n$ if @tt[ty_list] is a
   list of $n$ types. The parameter @tt[tc] is a tuple class, which can either
   be ``normal'', ``raw'', or ``box''.  Raw tuples can contain pointers and
   other rawdata.  They require a slightly different runtime representation,
   where the first field contains runtime type information.  Box tuples must
   always have arity one, and are used pass arbitrary values (such as
   floating-point values or raw integers) as polymorphic values.
   @end[doc]
>>

declare tyTuple[tc:s]{ 'mtyl }


doc <:doc< 
   @begin[doc]
  
   (Documentation incomplete.)
   @end[doc]
>>

(* XXX: documentation needs to be completed. *)

declare tyDTuple{ 'ty_var; 'mtyl_option }
declare tyTag{ 'ty_var; 'mtyl }


doc <:doc< ************************************
   @begin[doc]
   @modsubsection{Other aggregates}
  
   Arrays are similar to tuples, except all the elements of an array have the
   same type, and arrays may have arbitrary, non-negative dimension.
   @end[doc]
>>

declare tyArray{ 'ty }


doc <:doc< 
   @begin[doc]
  
   The type @tt[tyRawData] represents arbitrary data.  It is commonly
   used to represent data in imperative programming languages, such
   as C, where the types of the elements within are not known.  Runtime
   safety checks must be performed to guarantee safety.
   @end[doc]
>>

declare tyRawData


doc <:doc< 
   @begin[doc]
  
   The type @tt[tyFrame] is the frame given by @tt[ty_var] instantiated
   at the types in the list @tt[tyl].  Frames are not directly accessible
   to the programmer.
   @end[doc]
>>

declare tyFrame{ 'ty_var; 'tyl }


doc <:doc< ************************************
   @begin[doc]
   @modsubsection{Polymorphism}
  
   The term @tt[tyVar] represents a type variable.
   @end[doc]
>>

declare tyVar{ 'ty_var }


doc <:doc< 
   @begin[doc]
  
   The type @tt[tyApply] applies the types in the list @tt[ty_list] to a
   parametrized type given by @tt[ty_var].  The application must be
   complete; the resulting type cannot be a parametrized type.
   @end[doc]
>>

declare tyApply{ 'ty_var; 'ty_list }


doc <:doc< 
   @begin[doc]
  
   The existential type @tt[tyExists] defines a type @tt[ty] abstracted over a
   type variable @tt[t].  Similarly, the term @tt[tyAll] defines a universally
   quantified type.
   @end[doc]
>>

declare tyExists{ t. 'ty['t] }
declare tyAll{ t. 'ty['t] }


doc <:doc< 
   @begin[doc]
  
   If @tt[var] is a ``packed'' existential value (see @hrefterm[atomTyPack]),
   then the term @tt[tyProject] is the $i$th type in the packing, where
   indexing starts at zero.
   @end[doc]
>>

declare tyProject[i:n]{ 'var }

doc <:doc< 
   @docoff
>>


(**************************************************************************
 * Display forms.
 **************************************************************************)

(*
 * Mutable types.
 *)

dform mutable_df : except_mode[src] ::
   "mutable" =
   bf["mutable"]

dform immutable_df : except_mode[src] ::
   immutable =
   bf["immutable"]

dform mutable_ty_df : except_mode[src] ::
   mutable_ty{ 'ty; 'flag } =
   `"(" slot{'ty} `"," slot{'flag} `")"


(*
 * Type definitions.
 *)

dform tyDefPoly_df : except_mode[src] :: except_mode[tex] ::
   tyDefPoly{ t. 'ty } =
   lambda uparrow slot{'t} `". " slot{'ty}

dform tyDefPoly_df : mode[tex] ::
   tyDefPoly{ t. 'ty } =
   izone `"\\Lambda " ezone slot{'t} `". " slot{'ty}

dform frameSubField_df : except_mode[src] ::
   frameSubField{ 'ty; 'num } =
   `"(" slot{'ty} `"," slot{'num} `")"

dform tyDefUnion_df : except_mode[src] ::
   tyDefUnion{ 'cases } =
   bf["union"] "(" slot{'cases} `")"

dform tyDefDTuple_df : except_mode[src] ::
   tyDefDTuple{ 'ty_var } =
   bf["def_dtuple"] `"(" slot{'ty_var} `")"


(*
 * Numbers.
 *)

dform tyInt_df : except_mode[src] ::
   tyInt =
   mathbbZ sub{31}

dform tyEnum_df : except_mode[src] ::
   tyEnum[i:n] =
   bf["enum"] sub{slot[i:n]}

dform tyRawInt_df1 : except_mode[src] ::
   tyRawInt[precision:n, sign:s] =
   mathbbZ sub{slot[precision:n]} sup{it[sign:s]}

dform tyRawInt_df2 : except_mode[src] ::
   tyRawInt[precision:n, "signed"] =
   mathbbZ sub{slot[precision:n]} sup{bf["signed"]}

dform tyRawInt_df3 : except_mode[src] ::
   tyRawInt[precision:n, "unsigned"] =
   mathbbZ sub{slot[precision:n]} sup{bf["unsigned"]}

dform tyFloat_df : except_mode[src] ::
   tyFloat[precision:n] =
   mathbbR sub{slot[precision:n]}


(*
 * Functions.
 *)

dform tyFun_df : except_mode[src] ::
   tyFun{ 'arg_type; 'res_type } =
   `"(" slot{'arg_type} rightarrow slot{'res_type} `")"


(*
 * Tuples.
 *)

dform tyUnion_df : except_mode[src] ::
   tyUnion{ 'ty_var; 'ty_list; 'intset } =
   bf["union"] `"(" slot{'ty_var} `"," slot{'ty_list} `"," slot{'intset} `")"

dform tyTuple_df1 : except_mode[src] ::
   tyTuple[tc:s]{ 'mtyl } =
   bf["tuple"] sub{it[tc:s]} `"(" slot{'mtyl} `")"

dform tyTuple_df2 : except_mode[src] ::
   tyTuple["normal"]{ 'mtyl } =
   bf["tuple"] sub{bf["normal"]} `"(" slot{'mtyl} `")"

dform tyTuple_df3 : except_mode[src] ::
   tyTuple["raw"]{ 'mtyl } =
   bf["tuple"] sub{bf["raw"]} `"(" slot{'mtyl} `")"

dform tyTuple_df4 : except_mode[src] ::
   tyTuple["box"]{ 'mtyl } =
   bf["tuple"] sub{bf["box"]} `"(" slot{'mtyl} `")"

dform tyDTuple_df : except_mode[src] ::
   tyDTuple{ 'ty_var; 'mtyl_option } =
   bf["dtuple"] `"(" slot{'ty_var} `"," slot{'mtyl_option} `")"

dform tyTag_df : except_mode[src] ::
   tyTag{ 'ty_var; 'mtyl } =
   bf["tag"] `"(" slot{'ty_var} `"," slot{'mtyl} `")"


(*
 * Other aggregates.
 *)

dform tyArray_df : except_mode[src] ::
   tyArray{ 'ty } =
   `"(" slot{'ty} `" " bf["array"] `")"

dform tyRawData_df : except_mode[src] ::
   tyRawData =
   bf["data"]

dform tyFrame_df : except_mode[src] ::
   tyFrame{ 'ty_var; 'tyl } =
   bf["frame"] `"(" slot{'ty_var} `"," slot{'tyl} `")"


(*
 * Polymorphism.
 *)

dform tyVar_df : except_mode[src] ::
   tyVar{ 'ty_var } =
   bf["tvar"] `"(" slot{'ty_var} `")"

dform tyApply_df : except_mode[src] ::
   tyApply{ 'ty_var; 'ty_list } =
   slot{'ty_var} `"(" slot{'ty_list} `")"

dform tyExists_df : except_mode[src] ::
   tyExists{ t. 'ty } =
   exists slot{'t} `". " slot{'ty}

dform tyAll_df : except_mode[src] ::
   tyAll{ t. 'ty } =
   forall slot{'t} `". " slot{'ty}

dform tyProject_df : except_mode[src] ::
   tyProject[i:n]{ 'var } =
   slot{'var} `"." slot[i:n]
