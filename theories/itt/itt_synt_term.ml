doc <:doc<
   @begin[doc]
   @module[Itt_synt_bterm]

   @end[doc]

   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/index.html for information on Nuprl,
   OCaml, and more information about this system.

   Copyright (C) 2005, MetaPRL Group

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

   Authors: Aleksey Nogin @email{nogin@cs.caltech.edu}
            Alexei Kopylov @email{kopylov@cs.caltech.edu}
            Xin Yu @email{xiny@cs.caltech.edu}

   @end[license]
>>

doc "doc"{parents}

extends Itt_synt_var
extends Itt_synt_operator
extends Itt_prec

open Basic_tactics

doc "doc"{terms}


define  Pi{'l} <--> {'bts: list{BTerm}

define unfold_BTerm:  BTerm{'n} <--> "prec"{BTerm,n.
                                               if 'n<0 then void
                                               else Var{'n} + op: Operator * Pi{map {lambda{i.'BTerm{'n -@ 'i}}; arity{'op} }}
                                           ; 'n}

declare BTerm{'n}        (* Type of bterms with binding variable n *)
declare make_bterm{'op; 'subterms}
declare bterm_ind{'bt; v.'var_case['v];
                       op,subterms,rec. 'op_case['op; 'subterms; 'rec] }

prim_rw bterm_ind_reduce:
      bterm_ind{make_bterm{'op; 'subterms};
                v.'var_case['v];
                op,subterms,rec. 'op_case['op; 'subterms; 'rec] } <-->
         'op_case{'op;'subterms; 'bterm_ind{


doc "doc"{rules}

interactive

prim op_univ {| intro [] |}:
   sequent { <H> >- Operator in univ[l:l] } = it

interactive op_type {| intro [] |}:
   sequent { <H> >- Operator Type }

prim bop_univ {| intro [] |}:
   sequent { <H> >- BOperator in univ[l:l] } = it

interactive bop_type {| intro [] |}:
   sequent { <H> >- BOperator Type }


prim bop_subtype_op {| intro [] |}:
   sequent { <H> >- 'op in BOperator } -->
   sequent { <H> >- 'op in Operator }
   = it

prim same_op_wf {| intro [] |} :
   sequent { <H> >- 'op_1 in BOperator } -->
   sequent { <H> >- 'op_2 in BOperator } -->
   sequent { <H> >- same_op{'op_1;'op_2} in bool }
   = it

prim same_op_eq {| intro [] |} :
   sequent { <H> >- 'op_1 in BOperator } -->
   sequent { <H> >- 'op_2 in BOperator } -->
   sequent { <H> >- iff{'op_1 = 'op_2 in Operator; "assert"{same_op{'op_1;'op_2}}} }
   = it

prim binding_depth_wf {| intro [] |} :
   sequent { <H> >- 'op in BOperator } -->
   sequent { <H> >- binding_depth{'op} in nat }
   = it

prim arity_wf {| intro [] |} :
   sequent { <H> >- 'op in Operator } -->
   sequent { <H> >- arity{'op} in list{nat} }
   = it

prim down_wf {| intro [] |} :
   sequent { <H> >- 'op in BOperator } -->
   sequent { <H> >- binding_depth{'op} > 0 } -->
   sequent { <H> >- down{'op} in  BOperator }
   = it

prim down_red {| intro [] |} :
   sequent { <H> >- 'op in BOperator } -->
   sequent { <H> >- binding_depth{'op} > 0 } -->
   sequent { <H> >- binding_depth{down{'op}} =  binding_depth{'op} -@ 1 in nat }
   = it



doc <:doc< @docoff >>
