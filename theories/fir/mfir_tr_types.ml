doc <:doc<
   @begin[doc]
   @module[Mfir_tr_types]

   The @tt[Mfir_tr_types] module defines type equality judgments, which are
   used to determine the well-formedness of FIR types.
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

extends Mfir_option
extends Mfir_record
extends Mfir_int_set
extends Mfir_ty
extends Mfir_exp
extends Mfir_util
extends Mfir_sequent


(**************************************************************************
 * Rules.
 **************************************************************************)

doc <:doc<
   @begin[doc]
   @rules
   @modsubsection{Mutable types}

   The types must be equal, and the flags should be identical booleans.
   @end[doc]
>>

prim wf_mutable_ty :
   sequent { <H> >- "or"{ 'flag; "not"{ 'flag } } } -->
   sequent { <H> >- type_eq{ 'ty1; 'ty2; 'k } } -->
   sequent { <H> >- type_eq{ mutable_ty{ 'ty1; 'flag };
                                  mutable_ty{ 'ty2; 'flag };
                                  'k } }


doc <:doc< ************************************
   @begin[doc]
   @modsubsection{Numbers}

   The type << tyInt >> is well-formed.
   @end[doc]
>>

prim wf_tyInt :
   sequent { <H> >- type_eq{ tyInt; tyInt; small_type } }


doc <:doc<
   @begin[doc]

   Enumeration types are well-formed if the parameter $i$ is within the
   allowed range of values.  This latter restriction assists the Mojave
   compiler's garbage collector in differentiating between enumeration
   constants and pointers.
   @end[doc]
>>

prim wf_tyEnum :
   sequent { <H> >- member{ number[i:n]; enum_max } } -->
   sequent { <H> >- type_eq{ tyEnum[i:n]; tyEnum[i:n]; small_type } }


doc <:doc<
   @begin[doc]

   The types << tyRawInt[p:n, sign:s] >> and << tyFloat[p:n] >>
   are well-formed if their parameters are well-formed.  Note that
   << tyRawInt[p:n, sign:s] >> and << tyFloat[p:n] >> cannot be
   used as << small_type >> types.
   @end[doc]
>>

prim wf_tyRawInt1 :
   sequent { <H> >-
      "or"{ int_eq{ number[p:n]; 8 };
      "or"{ int_eq{ number[p:n]; 16 };
      "or"{ int_eq{ number[p:n]; 32 };
            int_eq{ number[p:n]; 64 } } } } } -->
   sequent { <H> >- type_eq{ tyRawInt[p:n, "signed"];
                                  tyRawInt[p:n, "signed"];
                                  large_type } }

prim wf_tyRawInt2 :
   sequent { <H> >-
      "or"{ int_eq{ number[p:n]; 8 };
      "or"{ int_eq{ number[p:n]; 16 };
      "or"{ int_eq{ number[p:n]; 32 };
            int_eq{ number[p:n]; 64 } } } } } -->
   sequent { <H> >- type_eq{ tyRawInt[p:n, "unsigned"];
                                  tyRawInt[p:n, "unsigned"];
                                  large_type } }

prim wf_tyFloat :
   sequent { <H> >-
      "or"{ int_eq{ number[p:n]; 32 };
      "or"{ int_eq{ number[p:n]; 64 };
            int_eq{ number[p:n]; 80 } } } } -->
   sequent { <H> >- type_eq{ tyFloat[p:n]; tyFloat[p:n]; large_type } }


doc <:doc< ************************************
   @begin[doc]
   @modsubsection{Functions}

   Function types are well-formed if the argument and result types
   are well-formed.
   @end[doc]
>>

prim wf_tyFun :
   sequent { <H> >- type_eq{ 'a1; 'a2; large_type } } -->
   sequent { <H> >- type_eq{ 'r1; 'r2; large_type } } -->
   sequent { <H> >- type_eq{ tyFun{ 'a1; 'r1 };
                                   tyFun{ 'a2; 'r2 };
                                   small_type } }


doc <:doc< ************************************
   @begin[doc]
   @modsubsection{Tuples}

   Two union types are equal if they name the same union definition, select
   the same subset of cases, and instantiate the definition at equal types.
   @end[doc]
>>

prim wf_tyUnion 'H :

   (* The types the unions are instantiated at should be equal. *)
   sequent { <H>; a: ty_def{'tv; polyKind{'i; union_type[j:n]}; 'd}; <J> >-
      type_eq_list{ 'tyl1; 'tyl2; small_type } } -->

   (* The subset of cases should be equal. *)
   sequent { <H>; a: ty_def{'tv; polyKind{'i; union_type[j:n]}; 'd}; <J> >-
      set_eq{ 'set1; 'set2 } } -->

   (* The subset of cases should actually be a subset. *)
   sequent { <H>; a: ty_def{'tv; polyKind{'i; union_type[j:n]}; 'd}; <J> >-
               'set1 subset
               intset[31, "signed"]{ interval{0; (number[j:n] -@ 1)} } }  -->

   (* Then the two tyUnion's are equal. *)
   sequent { <H>; a: ty_def{'tv; polyKind{'i; union_type[j:n]}; 'd}; <J> >-
      type_eq{ tyUnion{ 'tv; 'tyl1; 'set1 };
               tyUnion{ 'tv; 'tyl2; 'set2 };
               small_type } }


doc <:doc<
   @begin[doc]

   Two tuple types are equal if they are the same kind of tuple and their
   projections are pointwise equal.  Note that box tuples must have arity one.
   @end[doc]
>>

prim wf_tyTuple_normal :
   sequent { <H> >- type_eq_list{ 'tyl1; 'tyl2; small_type } } -->
   sequent { <H> >- type_eq{ tyTuple["normal"]{ 'tyl1 };
                                  tyTuple["normal"]{ 'tyl2 };
                                  small_type } }

prim wf_tyTuple_raw :
   sequent { <H> >- type_eq_list{ 'tyl1; 'tyl2; small_type } } -->
   sequent { <H> >- type_eq{ tyTuple["raw"]{ 'tyl1 };
                                  tyTuple["raw"]{ 'tyl2 };
                                  small_type } }

prim wf_tyTuple_box :
   sequent { <H> >- type_eq{ 't1; 't2; large_type } } -->
   sequent { <H> >- type_eq{ tyTuple["box"]{ cons{ 't1; nil } };
                                   tyTuple["box"]{ cons{ 't2; nil } };
                                   small_type } }


doc <:doc<
   @begin[doc]

   (Documentation incomplete.)
   @end[doc]
>>

(* XXX: documentation needs to be completed. *)

prim wf_tyDTuple_none 'H :
   sequent { <H>; a: ty_def{ 'tv; dtuple_type; 'd }; <J> >-
      type_eq{ tyDTuple{ 'tv; none }; tyDTuple{ 'tv; none }; small_type } }

prim wf_tyDTuple_some 'H :
   sequent { <H>; a: ty_def{ 'tv; dtuple_type; 'd }; <J> >-
      type_eq_list{ 'mtyl1; 'mtyl2; small_type } } -->
   sequent { <H>; a: ty_def{ 'tv; dtuple_type; 'd }; <J> >-
      type_eq{ tyDTuple{ 'tv; some{'mtyl1} };
               tyDTuple{ 'tv; some{'mtyl2} };
               small_type } }

prim wf_tyTag 'H :
   sequent { <H>; a: ty_def{ 'tv; dtuple_type; 'd }; <J> >-
      type_eq_list{ 'mtyl1; 'mtyl2; small_type } } -->
   sequent { <H>; a: ty_def{ 'tv; dtuple_type; 'd }; <J> >-
      type_eq{ tyTag{ 'tv; 'mtyl1 }; tyTag{ 'tv; 'mtyl2 }; small_type } }


doc <:doc< ************************************
   @begin[doc]
   @modsubsection{Other aggregates}

   Two array types are equal if their element types are equal.
   @end[doc]
>>

prim wf_tyArray :
   sequent { <H> >- type_eq{ 't1; 't2; large_type } } -->
   sequent { <H> >- type_eq{ tyArray{'t1}; tyArray{'t2}; small_type } }


doc <:doc<
   @begin[doc]

   The type << tyRawData >> is well-formed.
   @end[doc]
>>

prim wf_tyRawData :
   sequent { <H> >- type_eq{ tyRawData; tyRawData; small_type } }


doc <:doc<
   @begin[doc]

   (Documentation incomplete.)
   @end[doc]
>>

(* XXX: documentation needs to be completed. *)

prim wf_tyFrame 'H :
   sequent { <H>; a: ty_def{ 'tv; 'k; 'd }; <J> >-
      type_eq{apply_types{'d; 'tyl1}; apply_types{'d; 'tyl2}; frame_type} } -->
   sequent { <H>; a: ty_def{ 'tv; 'k; 'd }; <J> >-
      type_eq_list{ 'tyl1; 'tyl2; small_type } } -->
   sequent { <H>; a: ty_def{ 'tv; 'k; 'd }; <J> >-
      type_eq{ tyFrame{ 'tv; 'tyl1 }; tyFrame{ 'tv; 'tyl2 }; small_type } }


doc <:doc< ************************************
   @begin[doc]
   @modsubsection{Polymorphism}

   Two type variables are considered equal if they name the same variable
   and the variable is declared in the context with the specified kind.
   @end[doc]
>>

(*
 * BUG: Is exact equality really the way to go?  I believe that exact
 * equality is fine.  The Mojave FIR type checker (as of version 1.56)
 * uses alpha equality of type variables in a minimal fashion, and the
 * way I have written the typing rules in MetaPRL eliminates the need
 * to check for alpha equality.
 *)

prim wf_tyVar 'H :
   sequent { <H>; a: ty_def{ 'tv; 'k; 'd }; <J> >-
      type_eq{ tyVar{ 'tv }; tyVar{ 'tv }; 'k } }


doc <:doc<
   @begin[doc]

   Two type applications are equal if they name the same parametrized type
   and instantiate that type at equal types.
   @end[doc]
>>

(*
 * BUG: There's other rules that we can write down for tyApply,
 * such as the case in which one of the types has already been applied.
 *)

prim wf_tyApply1 'H :
   sequent { <H>; a: ty_def{ 'tv; polyKind{'i;  'k }; 'd }; <J> >-
      int_eq{ 'i; length{ 'tyl1 } } } -->
   sequent { <H>; a: ty_def{ 'tv; polyKind{'i;  'k }; 'd }; <J> >-
      type_eq_list{ 'tyl1; 'tyl2; small_type } } -->
   sequent { <H>; a: ty_def{ 'tv; polyKind{'i;  'k }; 'd }; <J> >-
      type_eq{ tyApply{ 'tv; 'tyl1 }; tyApply{ 'tv; 'tyl2 }; 'k } }

doc <:doc<
   @docoff
>>


doc <:doc<
   @begin[doc]

   Two existential types are equal if when instantiated at the same
   << small_type >> type, the resulting types are equal.
   @end[doc]
>>

prim wf_tyExists :
   sequent { <H>; tv: "type"; a: ty_def{ 'tv; small_type; no_def } >-
      type_eq{ 't1['tv]; 't2['tv]; large_type } } -->
   sequent { <H> >-
      type_eq{ tyExists{ x. 't1['x] }; tyExists{ y. 't2['y] }; small_type } }


doc <:doc<
   @begin[doc]

   Two universal types are equal if when instantiated at the same
   << small_type >> type, the resulting types are equal.
   @end[doc]
>>

prim wf_tyAll :
   sequent { <H>; tv: "type"; a: ty_def{ 'tv; small_type; no_def } >-
      type_eq{ 't1['tv]; 't2['tv]; large_type } } -->
   sequent { <H> >-
      type_eq{ tyAll{ x. 't1['x] }; tyAll{ y. 't2['y] }; small_type } }


doc <:doc<
   @begin[doc]

   Type projections are well-formed if $i$ is in bounds.
   @end[doc]
>>

(*
 * BUG: We might need another rule for tyProject since we can use
 * a definition from the context to test $v.i = u$.  Or we might
 * have variable aliasing $v1 = v2 = ...$.
 *)

prim wf_tyProject 'H :
   sequent { <H>;
                   a: var_def{ 'v; tyExists{t. 'ty['t]}; 'd };
                   <J> >-
      project_in_bounds{ number[i:n]; tyExists{t. 'ty['t]} } } -->
   sequent { <H>;
                   a: var_def{ 'v; tyExists{t. 'ty['t]}; 'd };
                   <J> >-
      type_eq{ tyProject[i:n]{ atomVar{'v} };
               tyProject[i:n]{ atomVar{'v} };
               small_type } }

doc <:doc<
   @docoff
>>


doc <:doc< ************************************
   @begin[doc]
   @modsubsection{Type definitions}

   Two parametrized types are equal if when instantiated at the same
   << small_type >>, the resulting types are equal.
   @end[doc]
>>

prim wf_tyDefPoly :
   sequent { <H>; tv: "type"; a: ty_def{ 'tv; small_type; no_def } >-
      type_eq{ 'ty1['tv]; 'ty2['tv]; polyKind{ ('i -@ 1); 'k } } } -->
   sequent { <H> >- type_eq{ tyDefPoly{ x. 'ty1['x] };
                                  tyDefPoly{ y. 'ty2['y] };
                                  polyKind{ 'i; 'k } } }


doc <:doc<
   @begin[doc]

   Well-formedness of frames and records is straightforward.
   @end[doc]
>>

prim wf_recordEnd_record :
   sequent { <H> >- type_eq{ recordEnd; recordEnd; record_type } }

prim wf_recordEnd_frame :
   sequent { <H> >- type_eq{ recordEnd; recordEnd; frame_type } }


prim wf_record_record :
   sequent { <H> >- type_eq{ 'data1; 'data2; large_type } } -->
   sequent { <H> >- type_eq{ 'rest1; 'rest2; record_type } } -->
   sequent { <H> >- type_eq{ record[tag:s]{ 'data1; 'rest1 };
                                  record[tag:s]{ 'data2; 'rest2 };
                                  record_type } }

prim wf_record_frame :
   sequent { <H> >- type_eq{ 'data1; 'data2; record_type } } -->
   sequent { <H> >- type_eq{ 'rest1; 'rest2; frame_type } } -->
   sequent { <H> >- type_eq{ record[tag:s]{ 'data1; 'rest1 };
                                  record[tag:s]{ 'data2; 'rest2 };
                                  frame_type } }

doc <:doc<
   @docoff
>>


(*
 * The term union_type_eq is used to test the equality of two union case
 * definitions.  The term unino_type_eq_list tests the pointwise equality
 * of the lists used in defining union types.
 *)

declare union_type_eq_list{ 'cases1; 'cases2 }


doc <:doc<
   @begin[doc]

   Two union definitions are equal if the cases they define are equal, and if
   they define the same kind of union.  Note that a union definition may
   define zero cases.
   @end[doc]
>>

prim wf_tyDefUnion :
   sequent { <H> >- int_eq{ length{ 'cases1 }; number[i:n] } } -->
   sequent { <H> >- union_type_eq_list{ 'cases1; 'cases2 } } -->
   sequent { <H> >- type_eq{ tyDefUnion{ 'cases1 };
                                  tyDefUnion{ 'cases2 };
                                  polyKind{0; union_type[i:n]} } }


doc <:doc<
   @begin[doc]

   Equality of union case definitions is straightforward.
   @end[doc]
>>

prim wf_tyDefUnion_cases1 :
   sequent { <H> >- union_type_eq_list{ nil; nil } }

prim wf_tyDefUnion_cases2 :
   sequent { <H> >- type_eq_list{ 'h1; 'h2; large_type } } -->
   sequent { <H> >- union_type_eq_list{ 't1; 't2 } } -->
   sequent { <H> >- union_type_eq_list{cons{'h1; 't1}; cons{'h2; 't2}} }


doc <:doc<
   @begin[doc]

   (Documentation incomplete.)
   @end[doc]
>>

(* XXX: documentation needs to be completed. *)

prim wf_tyDefDTuple 'H :
   sequent { <H>; a: ty_def{ 'tv; dtuple_type; tyDefDTuple{'tv} }; <J> >-
      type_eq{ tyDefDTuple{ 'tv }; tyDefDTuple{ 'tv }; dtuple_type } }

doc <:doc<
   @docoff
>>


(**************************************************************************
 * Display forms.
 **************************************************************************)

dform union_type_eq_list_df : except_mode[src] ::
   union_type_eq_list{ 'cases1; 'cases2 } =
   slot{'cases1} `"=" sub{it["union_cases"]} slot{'cases2}
      `":(" bf["union def"] `")"
