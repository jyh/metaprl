doc <:doc<
   @module[Mfir_tr_store]

   The @tt[Mfir_tr_store] module defines the typing rules for store values.

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

extends Mfir_list
extends Mfir_ty
extends Mfir_exp
extends Mfir_sequent
extends Mfir_tr_base
extends Mfir_tr_types
extends Mfir_tr_atom


(**************************************************************************
 * Rules.
 **************************************************************************)

doc <:doc<
   @rules
   @modsubsection{Tuple and array values}

   Store values of a tuple types are represented as lists of atoms.
>>

prim ty_store_tuple_normal :
   sequent { <H> >- has_type["atom_list"]{ 'elts; 'types } } -->
   sequent { <H> >- has_type["store"]{'elts; tyTuple["normal"]{'types}} }

prim ty_store_tuple_raw :
   sequent { <H> >- has_type["atom_list"]{ 'elts; 'types } } -->
   sequent { <H> >- has_type["store"]{'elts; tyTuple["raw"]{'types}} }

prim ty_store_tuple_box :
   sequent { <H> >- has_type["atom"]{ 'elt; 't } } -->
   sequent { <H> >-
      has_type["store"]{ ('elt :: nil); tyTuple["box"]{ ('t :: nil) } } }


doc <:doc<

   Store values of array types are also represented as lists of atoms.
>>

prim ty_store_array1 :
   sequent { <H> >- has_type["store"]{ nil; tyArray{'t} } }

prim ty_store_array2 :
   sequent { <H> >- has_type["atom"]{ 'elt; 't } } -->
   sequent { <H> >- has_type["store"]{ 'tail; tyArray{'t} } } -->
   sequent { <H> >- has_type["store"]{cons{'elt; 'tail}; tyArray{'t}} }


doc <:doc<
   @modsubsection{Functions}

   The typing rules for functions are straightforward.  These rules use the
   ``@tt[exp]'' tag since in << polyFun{ x. 'f['x] } >> and
   << lambda{ x. 'f['x] } >>, $f$ may be an expression.
>>

prim ty_store_lambda :
   sequent { <H> >- type_eq{ 'u; 'u; large_type } } -->
   sequent { <H>; v: variable; a: var_def{ 'v; 'u; no_def } >-
      has_type["exp"]{ 'f['v]; 't } } -->
   sequent { <H> >-
      has_type["exp"]{ lambda{ x. 'f['x] }; tyFun{ 'u; 't } } }

prim ty_store_polyFun :
   sequent { <H>; tv: "type"; a: ty_def{ 'tv; small_type; no_def } >-
      has_type["exp"]{ 'f['tv]; 'ty['tv] } } -->
   sequent { <H> >-
      has_type["exp"]{ polyFun{ x. 'f['x] }; tyAll{ t. 'ty['t] } } }


doc <:doc<
   @modsubsection{Union values}

   A value << union_val[i:n]{ 'tv; 'atom_list } >> belongs to a union type
   if the union type is well-formed, and if the atoms belong to the specific
   case of the union definition given by the union type.
>>

prim ty_store_union 'H :
   (* well-formedness of the union type. *)
   sequent { <H>; a: ty_def{ 'tv; polyKind{'j; 'k}; 'tyd }; <J> >-
      type_eq{ tyUnion{'tv; 'tyl; intset[31, "signed"]{
                  (interval{number[i:n]; number[i:n]} :: nil) }};
               tyUnion{'tv; 'tyl; intset[31, "signed"]{
                  (interval{number[i:n]; number[i:n]} :: nil) }};
               small_type } } -->

   (* check that the atoms have the right types. *)
   sequent { <H>; a: ty_def{ 'tv; polyKind{'j; 'k}; 'tyd }; <J> >-
      has_type["union_atoms"]{
         'atoms;
          nth_elt{number[i:n]; apply_types{ 'tyd; 'tyl }}}} -->

   (* then the union value is well-typed. *)
   sequent { <H>; a: ty_def{ 'tv; polyKind{'j; 'k}; 'tyd }; <J> >-
      has_type["store"]{
         union_val[i:n]{ 'tv; 'atoms };
         tyUnion{ 'tv; 'tyl; intset[31, "signed"]{
            (interval{number[i:n]; number[i:n]} :: nil) } } } }


doc <:doc<

   The next two rules check that the atoms used to initialize a union value
   have the appropriate types.
>>

prim ty_store_union_atoms1 :
   sequent { <H> >- has_type["union_atoms"]{ nil; nil } }

prim ty_store_union_atoms2 :
   sequent { <H> >- has_type["atom"]{ 'elt; 'ty } } -->
   sequent { <H> >- has_type["union_atoms"]{ 'tail; 'rest } } -->
   sequent { <H> >-
      has_type["union_atoms"]{ cons{ 'elt; 'tail };
                               cons{ mutable_ty{'ty; 'flag}; 'rest } } }


doc <:doc<
   @modsubsection{Raw data values}

   Raw data is represented abstractly as the value << raw_data >>.
>>

prim ty_store_raw_data :
   sequent { <H> >- has_type["store"]{ raw_data; tyRawData } }
