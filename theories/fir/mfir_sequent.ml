doc <:doc<
   @module[Mfir_sequent]

   The @tt[Mfir_sequent] module declares terms used in FIR theory sequents.
   We take the following interpretation of sequents in the FIR theory.  If a
   sequent is not well-formed, then it holds trivially.  A well-formed
   sequent is closed, and the context (list of hypotheses) must be
   well-formed.

   @docoff
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
   @parents
>>

extends Base_theory


(**************************************************************************
 * Declarations.
 **************************************************************************)

doc <:doc<
   @terms
   @modsubsection{Sequent tags}

   The term @tt[sequent_arg] is used to tag FIR theory sequents.  The term @tt[default_extract]
   is a trivial term that has no meaning.
>>

declare sequent [sequent_arg] { Term : Term >- Term } : Judgment
declare default_extract

doc <:doc<
   @modsubsection{Kinds}

   Kinds are used to classify FIR types and type definitions.  Types may be
   @em[small] or @em[large].  The raw integers and floating point values are
   large; all other types are small.  The distinction between small and large
   types is necessary to assist the garbage collector in the Mojave compiler.
   Values of a small type can be tagged to distinguish them from pointers.
>>

declare small_type
declare large_type

doc <:doc<

   Union definitions (@hrefterm[tyDefUnion]) belong to the @tt[union_type]
   kind, where the parameter $i$ indicates the number of cases in the union.
>>

declare union_type[i:n]


doc <:doc<

   (Documentation incomplete.)
>>

(* XXX: documentation needs to be completed. *)

declare record_type
declare frame_type


doc <:doc<

   (Documentation incomplete.)
>>

(* XXX: documentation needs to be completed. *)

declare dtuple_type


doc <:doc<

   All types, including parametrized type definitions, belong to the
   @tt[polyKind] kind.  The subterm @tt[i] is the number of parameters in the
   definition, and the subterm @tt[k] is the kind of the type once all the
   parameters are instantiated.  We allow the case $i = 0$.
>>

declare polyKind{ 'i; 'k }


doc <:doc<
   @modsubsection{Contexts}

   (Documentation incomplete.)
>>

(* XXX: documentation needs to be completed. *)

declare frame
declare "fun"
declare global
declare "type"
declare variable


doc <:doc<

   The terms @tt[ty_def], @tt[var_def], and @tt[global_def] are used for
   definitions in the context.  The first subterm is the variable being
   declared/defined.  If the subterm @tt[def] is @tt[no_def], then the
   definition is considered to be a declaration only.  A declaration is
   well-formed if the second subterm is a well-formed kind/type, and the third
   subterm is @tt[no_def].  A definition is well-formed if the corresponding
   declaration is well-formed, and if the value/type in the definition has the
   specified kind or type.
>>

declare ty_def{ 'var; 'k; 'def }
declare var_def{ 'var; 'ty; 'def }
declare global_def{ 'var; 'ty; 'def }
declare no_def


doc <:doc<
   @modsubsection{Store values}

   The term @tt[polyFun] is a polymorphic function that takes one type
   argument.  The term @tt[lambda] is a non-polymorphic function that takes
   one argument.  The term @tt[union_val] is a value of case $i$ of some
   (polymorphic) union type @tt[ty_var], initialized with the atoms in the
   list @tt[atom_list].  The term @tt[raw_data] is an opaque representation of
   raw data (see @hrefterm[tyRawData]).
>>

declare polyFun{ t. 'f['t] }
declare lambda{ v. 'f['v] }
declare union_val[i:n]{ 'ty_var; 'atom_list }
declare raw_data

doc <:doc<
   @modsubsection{Judgments}

   The judgment @tt[wf_kind] says that the kind @tt[k] is well-formed.
>>

declare wf_kind{ 'k }


doc <:doc<

   A proof of @tt[type_eq] says that two types (or type definitions)
   @tt[ty1] and @tt[ty2] are equal in the kind @tt[k], and that @tt[k]
   is well-formed.  A proof of @tt[type_eq_list] says that two lists of types
   (or type definitions) are pointwise equal in the specified kind, and that
   the kind is well-formed.
>>

declare type_eq{ 'ty1; 'ty2; 'k }
declare type_eq_list{ 'tyl1; 'tyl2; 'k }


doc <:doc<

   A proof of @tt[has_type] says that a term @tt[t] has type @tt[ty],
   and that @tt[ty] is a well-formed type.  The string parameter is an
   annotation that is intended to describe some aspect of @tt[t] or
   the typing relation.
>>

declare has_type[str:s]{ 't; 'ty }

doc <:doc<
   @docoff
>>


(**************************************************************************
 * Display forms.
 **************************************************************************)

(*
 * Sequent tags.
 *)

dform it_df1 : except_mode[src] :: except_mode[tex] ::
   default_extract =
   cdot

dform it_df2 : mode[tex] ::
   default_extract =
   izone `"\\bullet" ezone

(*
 * Kinds.
 *)

dform small_type_df : except_mode[src] ::
   small_type =
   omega

dform large_type_df : except_mode[src] :: except_mode[tex] ::
   large_type  =
   `"(big " omega `")"

dform largeType_df : mode[tex] ::
   large_type  =
   izone `"\\Omega" ezone

dform union_type_df : except_mode[src] ::
   union_type[i:n] =
   bf["union"] `"[" slot[i:n] `"]"

dform record_type_df : except_mode[src] ::
   record_type =
   bf["record"]

dform frame_type_df : except_mode[src] ::
   frame_type =
   bf["frame"]

dform dtuple_type_df : except_mode[src] ::
   dtuple_type =
   bf["dtuple"]

dform polyKind_df : except_mode[src] ::
   polyKind{ 'i; 'k } =
   small_type sup{slot{'i}} rightarrow slot{'k}


(*
 * Store values.
 *)

dform polyFun_df1 : except_mode[src] :: except_mode[tex] ::
   polyFun{ t. 'f } =
   lambda uparrow slot{'t} `". " slot{'f}

dform polyFun_df2 : mode[tex] ::
   polyFun{ t. 'f } =
   izone `"\\Lambda " ezone slot{'t} `". " slot{'f}

dform lambda_df : except_mode[src] ::
   lambda{ v. 'f } =
   lambda slot{'v} `". " slot{'f}

dform union_val_df : except_mode[src] ::
   union_val[i:n]{ 'ty_var; 'atom_list } =
   slot{'ty_var} `"[" slot[i:n] `"](" slot{'atom_list} `")"

dform raw_data_df : except_mode[src] ::
   raw_data =
   bf["raw_data"]


(*
 * Contexts.
 *)

dform frame_df : except_mode[src] ::
   frame =
   tt["Frame"]

dform fun_df : except_mode[src] ::
   "fun" =
   tt["Fun"]

dform global_df : except_mode[src] ::
   global =
   tt["Global"]

dform type_df : except_mode[src] ::
   "type" =
   tt["Type"]

dform variable_df : except_mode[src] ::
   variable =
   tt["Variable"]

dform ty_def_df1 : except_mode[src] ::
   ty_def{ 'var; 'k; 'def } =
   slot{'var} `":" slot{'k} `"=" slot{'def}

dform ty_def_df2 : except_mode[src] ::
   ty_def{ 'var; 'k; no_def } =
   slot{'var} `":" slot{'k}

dform var_def_df1 : except_mode[src] ::
   var_def{ 'var; 'ty; 'def } =
   slot{'var} `":" slot{'ty} `"=" slot{'def}

dform var_def_df2 : except_mode[src] ::
   var_def{ 'var; 'ty; no_def } =
   slot{'var} `":" slot{'ty}

dform global_def_df1 : except_mode[src] ::
   global_def{ 'var; 'ty; 'def } =
   slot{'var} `":" slot{'ty} `"=" slot{'def}

dform global_def_df2 : except_mode[src] ::
   global_def{ 'var; 'ty; no_def } =
   slot{'var} `":" slot{'ty}

dform no_def_df1 : except_mode[src] :: except_mode[tex] ::
   no_def =
   cdot

dform no_def_df2 : mode[tex] ::
   no_def =
   izone `"\\bullet" ezone


(*
 * Judgments.
 *)

dform wf_kind_df : except_mode[src] ::
   wf_kind{ 'k } =
   bf["wf_kind"] `"(" slot{'k} `")"

dform type_eq_df : except_mode[src] ::
   type_eq{ 'ty1; 'ty2; 'k } =
   slot{'ty1} `"=" slot{'ty2} `":" slot{'k}

dform type_eq_list_df : except_mode[src] ::
   type_eq_list{ 'tyl1; 'tyl2; 'k } =
   slot{'tyl1} `"=" sub{it["list"]} slot{'tyl2} `":" slot{'k}

dform has_type_df : except_mode[src] ::
   has_type[str:s]{ 't; 'ty } =
   slot{'t} `":" slot{'ty} `" [" it[str:s] `"]"
