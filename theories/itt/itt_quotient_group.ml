doc <:doc< 
   @begin[doc]
   @module[Itt_quotient_group]
  
   This theory defines quotient groups.
   @end[doc]
  
   ----------------------------------------------------------------
  
   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.
  
   See the file doc/index.html for information on Nuprl,
   OCaml, and more information about this system.
  
   Copyright (C) 1998 Jason Hickey, Cornell University
  
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
  
   Author: Xin Yu @email{xiny@cs.caltech.edu}
   @end[license]
>>

doc <:doc< @doc{@parents} >>
extends Itt_group
extends Itt_quotient
extends Itt_subset
extends Itt_subset2
doc docoff

open Printf
open Mp_debug
open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermAddr
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.Refine
open Refiner.Refiner.RefineError
open Mp_resource
open Simple_print

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Sequent
open Tactic_type.Conversionals
open Mptop
open Var

open Base_dtactic
open Base_auto_tactic

open Itt_struct
open Itt_record
open Itt_grouplikeobj
open Itt_squash
open Itt_fun
open Itt_equal
open Itt_subtype

let _ =
   show_loading "Loading Itt_quotient_group%t"

(************************************************************************
 * QUOTIENT GROUP                                                       *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @modsection{Quotient Group}
   @modsubsection{Rewrites}
  
   @end[doc]
>>
define unfold_quotGroup : quotGroup{'A; 'B} <-->
   {car=quot x, y: 'B^car // ('x *['B] ('B^inv 'y) in 'A^car subset 'B^car); "*"='B^"*"; "1"='B^"1"; inv='B^inv}

doc docoff

let fold_quotGroup = makeFoldC << quotGroup{'A; 'B} >> unfold_quotGroup

interactive quotG_equiv_type {| intro [intro_typeinf <<'B>>] |} group[i:l] :
   [wf] sequent [squash] { <H> >- subgroup[i:l]{'A; 'B} } -->
   sequent ['ext] { <H> >- "type"{quot x, y: 'B^car // ('x *['B] ('B^inv 'y) in 'A^car subset 'B^car)} }

doc <:doc< 
   @begin[doc]
   @modsubsection{Introduction}
  
   @end[doc]
>>
interactive quotGroup_intro {| intro [] |} :
   sequent ['ext] { <H> >- normalSubg[i:l]{'A; 'B} } -->
   sequent ['ext] { <H> >- quotGroup{'A; 'B} in group[i:l] }

doc <:doc< 
   @begin[doc]
   @modsubsection{Rules}
  
   @end[doc]
>>

doc docoff

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform quotGroup_df1 : except_mode[src] :: except_mode[prl] :: quotGroup{'A; 'B} =
   slot{'A} `" // " slot{'B}

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
