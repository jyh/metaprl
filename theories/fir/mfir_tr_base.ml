doc <:doc< 
   @begin[doc]
   @module[Mfir_tr_base]
  
   The @tt[Mfir_tr_base] module defines the basic axioms of the FIR type
   system.
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

extends Mfir_bool
extends Mfir_int
extends Mfir_list
extends Mfir_sequent


(**************************************************************************
 * Rules.
 **************************************************************************)

doc <:doc< 
   @begin[doc]
   @rules
   @modsubsection{Basic axioms}
  
   The @tt[truth_intro] rule allows proofs of side-conditions to be completed.
   @end[doc]
>>

prim truth_intro :
   sequent { <H> >- "true" }
   = it


doc <:doc< 
   @begin[doc]
  
   The next two rules are convenient for making sure that the atoms in a list each
   have the appropriate type (given by a list of types).
   @end[doc]
>>

prim ty_atom_list1 :
   sequent { <H> >- has_type["atom_list"]{ nil; nil } }
   = it

prim ty_atom_list2 :
   sequent { <H> >- has_type["atom"]{ 'elt; 't } } -->
   sequent { <H> >- has_type["atom_list"]{ 'tail; 'rest } } -->
   sequent { <H> >-
      has_type["atom_list"]{ cons{ 'elt; 'tail }; cons{ 't; 'rest } } }
   = it


doc <:doc< 
   @begin[doc]
  
   Two lists of types are equal if they are pointwise equal.
   @end[doc]
>>

prim wf_ty_list1 :
   sequent { <H> >- wf_kind{ 'k } } -->
   sequent { <H> >- type_eq_list{ nil; nil; 'k } }
   = it

prim wf_ty_list2 :
   sequent { <H> >- type_eq{ 'h1; 'h2; 'k } } -->
   sequent { <H> >- type_eq_list{ 't1; 't2; 'k } } -->
   sequent { <H> >- type_eq_list{ cons{'h1; 't1}; cons{'h2; 't2}; 'k } }
   = it


doc <:doc< ************************************
   @begin[doc]
   @modsubsection{Kind well-formedness}
  
   The kind well-formedness rules specify how kinds may be used
   in classifying FIR types.  Specifically, some kinds << 'k >>
   may only appear as << polyKind{ 'i; 'k } >>.
   @end[doc]
>>

prim wf_small_type :
   sequent { <H> >- wf_kind{ small_type } }
   = it

prim wf_large_type :
   sequent { <H> >- wf_kind{ large_type } }
   = it

prim wf_record_type :
   sequent { <H> >- wf_kind{ record_type } }
   = it

prim wf_dtuple_type :
   sequent { <H> >- wf_kind{ dtuple_type } }
   = it

prim wf_polyKind_small :
   sequent { <H> >- int_lt{ 0; 'i } } -->
   sequent { <H> >- wf_kind{ polyKind{ 'i; small_type } } }
   = it

prim wf_polyKind_large :
   sequent { <H> >- int_lt{ 0; 'i } } -->
   sequent { <H> >- wf_kind{ polyKind{ 'i; large_type } } }
   = it

prim wf_polyKind_union :
   sequent { <H> >- "and"{ int_le{ 0; 'i };
                                int_le{ 0; number[j:n] } } } -->
   sequent { <H> >- wf_kind{ polyKind{ 'i; union_type[j:n] } } }
   = it

prim wf_polyKind_frame :
   sequent { <H> >- int_le{ 0; 'i } } -->
   sequent { <H> >- wf_kind{ polyKind{ 'i; frame_type } } }
   = it


doc <:doc< ************************************
   @begin[doc]
   @modsubsection{Kind equivalence}
  
   The @tt[wf_small_type] rule allows any << small_type >> type
   to be used as a << large_type >> type.
   @end[doc]
>>

prim ty_small_as_large :
   sequent { <H> >- type_eq{ 't1; 't2; small_type } } -->
   sequent { <H> >- type_eq{ 't1; 't2; large_type } }
   = it


doc <:doc< 
   @begin[doc]
  
   If two types are equal in some kind << 'k >>,
   then they are equal equal in << polyKind{ 0; 'k } >>.
   @end[doc]
>>

prim ty_polyKind_as_normal_kind :
   sequent { <H> >- type_eq{ 't1; 't2; 'k } } -->
   sequent { <H> >- type_eq{ 't1; 't2; polyKind{ 0; 'k } } }
   = it

doc <:doc< 
   @docoff
>>
