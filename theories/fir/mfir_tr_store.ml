doc <:doc< 
   @begin[doc]
   @module[Mfir_tr_store]
  
   The @tt[Mfir_tr_store] module defines the typing rules for store values.
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
   @begin[doc]
   @rules
   @modsubsection{Tuple and array values}
  
   Store values of a tuple types are represented as lists of atoms.
   @end[doc]
>>

prim ty_store_tuple_normal :
   sequent [fir] { <H> >- has_type["atom_list"]{ 'elts; 'types } } -->
   sequent [fir] { <H> >- has_type["store"]{'elts; tyTuple["normal"]{'types}} }
   = it

prim ty_store_tuple_raw :
   sequent [fir] { <H> >- has_type["atom_list"]{ 'elts; 'types } } -->
   sequent [fir] { <H> >- has_type["store"]{'elts; tyTuple["raw"]{'types}} }
   = it

prim ty_store_tuple_box :
   sequent [fir] { <H> >- has_type["atom"]{ 'elt; 't } } -->
   sequent [fir] { <H> >-
      has_type["store"]{ ('elt :: nil); tyTuple["box"]{ ('t :: nil) } } }
   = it


doc <:doc< 
   @begin[doc]
  
   Store values of array types are also represented as lists of atoms.
   @end[doc]
>>

prim ty_store_array1 :
   sequent [fir] { <H> >- has_type["store"]{ nil; tyArray{'t} } }
   = it

prim ty_store_array2 :
   sequent [fir] { <H> >- has_type["atom"]{ 'elt; 't } } -->
   sequent [fir] { <H> >- has_type["store"]{ 'tail; tyArray{'t} } } -->
   sequent [fir] { <H> >- has_type["store"]{cons{'elt; 'tail}; tyArray{'t}} }
   = it


doc <:doc< ************************************
   @begin[doc]
   @modsubsection{Functions}
  
   The typing rules for functions are straightforward.  These rules use the
   ``@tt[exp]'' tag since in $<< polyFun{ x. 'f['x] } >>$ and
   $<< lambda{ x. 'f['x] } >>$, $f$ may be an expression.
   @end[doc]
>>

prim ty_store_lambda :
   sequent [fir] { <H> >- type_eq{ 'u; 'u; large_type } } -->
   sequent [fir] { <H>; v: variable; a: var_def{ 'v; 'u; no_def } >-
      has_type["exp"]{ 'f['v]; 't } } -->
   sequent [fir] { <H> >-
      has_type["exp"]{ lambda{ x. 'f['x] }; tyFun{ 'u; 't } } }
   = it

prim ty_store_polyFun :
   sequent [fir] { <H>; tv: "type"; a: ty_def{ 'tv; small_type; no_def } >-
      has_type["exp"]{ 'f['tv]; 'ty['tv] } } -->
   sequent [fir] { <H> >-
      has_type["exp"]{ polyFun{ x. 'f['x] }; tyAll{ t. 'ty['t] } } }
   = it


doc <:doc< ************************************
   @begin[doc]
   @modsubsection{Union values}
  
   A value $<< union_val[i:n]{ 'tv; 'atom_list } >>$ belongs to a union type
   if the union type is well-formed, and if the atoms belong to the specific
   case of the union definition given by the union type.
   @end[doc]
>>

prim ty_store_union 'H :
   (* well-formedness of the union type. *)
   sequent [fir] { <H>; a: ty_def{ 'tv; polyKind{'j; 'k}; 'tyd }; <J> >-
      type_eq{ tyUnion{'tv; 'tyl; intset[31, "signed"]{
                  (interval{number[i:n]; number[i:n]} :: nil) }};
               tyUnion{'tv; 'tyl; intset[31, "signed"]{
                  (interval{number[i:n]; number[i:n]} :: nil) }};
               small_type } } -->

   (* check that the atoms have the right types. *)
   sequent [fir] { <H>; a: ty_def{ 'tv; polyKind{'j; 'k}; 'tyd }; <J> >-
      has_type["union_atoms"]{
         'atoms;
          nth_elt{number[i:n]; apply_types{ 'tyd; 'tyl }}}} -->

   (* then the union value is well-typed. *)
   sequent [fir] { <H>; a: ty_def{ 'tv; polyKind{'j; 'k}; 'tyd }; <J> >-
      has_type["store"]{
         union_val[i:n]{ 'tv; 'atoms };
         tyUnion{ 'tv; 'tyl; intset[31, "signed"]{
            (interval{number[i:n]; number[i:n]} :: nil) } } } }
   = it


doc <:doc< 
   @begin[doc]
  
   The next two rules check that the atoms used to initialize a union value
   have the appropriate types.
   @end[doc]
>>

prim ty_store_union_atoms1 :
   sequent [fir] { <H> >- has_type["union_atoms"]{ nil; nil } }
   = it

prim ty_store_union_atoms2 :
   sequent [fir] { <H> >- has_type["atom"]{ 'elt; 'ty } } -->
   sequent [fir] { <H> >- has_type["union_atoms"]{ 'tail; 'rest } } -->
   sequent [fir] { <H> >-
      has_type["union_atoms"]{ cons{ 'elt; 'tail };
                               cons{ mutable_ty{'ty; 'flag}; 'rest } } }
   = it


doc <:doc< ************************************
   @begin[doc]
   @modsubsection{Raw data values}
  
   Raw data is represented abstractly as the value $<< raw_data >>$.
   @end[doc]
>>

prim ty_store_raw_data :
   sequent [fir] { <H> >- has_type["store"]{ raw_data; tyRawData } }
   = it

doc <:doc< 
   @docoff
>>
