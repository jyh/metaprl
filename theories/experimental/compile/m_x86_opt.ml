doc <:doc<
   @begin[doc]
   @module[M_x86_opt]

   This module implements some easy assembly optimizations, including
   dead instruction elimination and removal of null reserves.
   @end[doc]

   ----------------------------------------------------------------

   @begin[license]
   Copyright (C) 2003 Jason Hickey, Caltech

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

   Author: Jason Hickey
   @email{jyh@cs.caltech.edu}
   @end[license]
>>

doc <:doc< @doc{@parents} >>
extends Base_theory
extends M_x86_asm
doc docoff

open Basic_tactics

open M_util

(************************************************************************
 * Resources.
 *)

doc <:doc<
   @begin[doc]
   @resources

   The @tt[before_ra] resource provides a generic method for defining
   rewrites that may be applied before register allocation.  The
   @conv[before_raC] conversion can be used to apply this evaluator.

   The implementation of the @tt[before_ra_resource] and the @tt[before_raC]
   conversion rely on tables to store the shape of redices, together with the
   conversions for the reduction.

   The @tt[after_ra] resource and corresponding conversion @tt[after_raC]
   are similar.

   @docoff
   @end[doc]
>>
let resource (term * conv, conv) before_ra =
   table_resource_info extract_data

let before_raTopC_env e =
   get_resource_arg (env_arg e) get_before_ra_resource

let before_raTopC = funC before_raTopC_env

let before_raC =
   repeatC (higherC before_raTopC)

let resource (term * conv, conv) after_ra =
   table_resource_info extract_data

let after_raTopC_env e =
   get_resource_arg (env_arg e) get_after_ra_resource

let after_raTopC = funC after_raTopC_env

let after_raC =
   repeatC (higherC after_raTopC)

(************************************************************************
 * Optimizations for before (and after) register allocation.
 *)

doc <:doc<
   @begin[doc]
   @rewrites
   @modsubsection{Dead instruction elimination}

   Dead instructions, i.e. those instructions that define a variable that is
   not used in the rest of the program, may be eliminated.  The rewrites
   below are aggressive;  the program's semantics could change if an
   instruction that can raise an exception is eliminated.  These rewrites
   are added to the @tt[before_ra] resource, although they may be applied
   after register allocation as well.
   @end[doc]
>>
prim_rw dead_mov :
   Mov{'src; dst. 'e}
   <-->
   'e

prim_rw dead_inst1 :
   Inst1[opcode:s]{'src; dst. 'e}
   <-->
   'e

prim_rw dead_inst2 :
   Inst2[opcode:s]{'src1; 'src2; dst. 'e}
   <-->
   'e

prim_rw dead_inst3 :
   Inst3[opcode:s]{'src1; 'src2; 'src3; dst2, dst3. 'e}
   <-->
   'e

prim_rw dead_shift :
   Shift[opcode:s]{'src1; 'src2; dst. 'e}
   <-->
   'e

prim_rw dead_set :
   Set[opcode:s]{'cc; 'src; dst. 'e}
   <-->
   'e

(************************************************************************
 * Optimizations that are only valid after register allocation.
 *)

doc <:doc<
   @begin[doc]
   @modsubsection{Null reserve elimination}

   Null reserves may be eliminated from the program.  The rewrite below is
   added to the @tt[after_ra] resource since it is valid only after register
   allocation.
   @end[doc]
>>
prim_rw delete_null_reserve :
   Cmp["cmp"]{'a1; 'a2;
   Jcc[opcode:s]{'cc; AsmReserve[0:n]{'params};
   'rest}}
   <-->
   'rest

doc <:doc< @docoff >>

(************************************************************************
 * Resources.
 *)
let resource before_ra +=
   [<< Mov{'src; dst. 'e} >>, dead_mov;
    << Inst1[opcode:s]{'src; dst. 'e} >>, dead_inst1;
    << Inst2[opcode:s]{'src1; 'src2; dst. 'e} >>, dead_inst2;
    << Inst3[opcode:s]{'src1; 'src2; 'src3; dst2, dst3. 'e} >>, dead_inst3;
    << Shift[opcode:s]{'src1; 'src2; dst. 'e} >>, dead_shift;
    << Set[opcode:s]{'cc; 'src; dst. 'e} >>, dead_set]

let resource after_ra +=
    [<< Cmp["cmp"]{'a1; 'a2; Jcc[opcode:s]{'cc; AsmReserve[0:n]{'params}; 'rest}} >>, delete_null_reserve]

(*
 * Main optimizers.
 *)
let opt_before_raT =
   rw (repeatC (before_raC thenC reduceC)) 0

let opt_after_raT =
   rw (repeatC (after_raC thenC before_raC thenC reduceC)) 0

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
