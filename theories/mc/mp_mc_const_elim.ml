doc <:doc< 
   @begin[doc]
   @module[Mp_mc_const_elim]
  
   The @tt[Mp_mc_const_elim] module provides rewrites to perform
   constant elimination (folding) in FIR programs.
   @end[doc]
  
   ----------------------------------------------------------------
  
   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.
  
   See the file doc/index.html for information on Nuprl,
   OCaml, and more information about this system.
  
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
   @email{emre@its.caltech.edu}
   @end[license]
>>

doc <:doc< 
   @begin[doc]
   @parents
   @end[doc]
>>
extends Itt_int_base
extends Mp_mc_fir_ty
extends Mp_mc_fir_exp
doc <:doc< @docoff >>

open Mp_mc_fir_eval
open Top_conversionals

(*************************************************************************
 * Rewrites.
 *************************************************************************)

(*
 * Basic facts about multiplication.
 *)

prim_rw reduce_mulRawIntOp_opt1 :
   letBinop{ tyRawInt{'p;'s}; mulRawIntOp{'p;'s};
             atomRawInt{'p;'s;1}; atomVar{ 'v }; v. 'exp['v] } <-->
   'exp[ 'v ]

prim_rw reduce_mulRawIntOp_opt2 :
   letBinop{ tyRawInt{'p;'s}; mulRawIntOp{'p;'s};
             atomVar{ 'v }; atomRawInt{'p;'s;1}; v. 'exp['v] } <-->
   'exp[ 'v ]

prim_rw reduce_mulRawIntOp_opt3 :
   letBinop{ tyRawInt{'p;'s}; mulRawIntOp{'p;'s};
             atomRawInt{'p;'s;0}; atomVar{ 'v }; v. 'exp['v] } <-->
   'exp[ atomRawInt{'p;'s;0} ]

prim_rw reduce_mulRawIntOp_opt4 :
   letBinop{ tyRawInt{'p;'s}; mulRawIntOp{'p;'s};
             atomVar{ 'v }; atomRawInt{'p;'s;0}; v. 'exp['v] } <-->
   'exp[ atomRawInt{'p;'s;0} ]

(*************************************************************************
 * Automation
 *************************************************************************)

let firConstElimC =
   repeatC (higherC (applyAllC [

      reduce_mulRawIntOp_opt1;
      reduce_mulRawIntOp_opt2;
      reduce_mulRawIntOp_opt3;
      reduce_mulRawIntOp_opt4

   ] ))
