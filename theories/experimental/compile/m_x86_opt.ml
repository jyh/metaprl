(*!
 * @begin[spelling]
 * CPS ra
 * @end[spelling]
 *
 * Some easy assembly optimizations.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2003 Jason Hickey, Caltech
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 *
 * Author: Jason Hickey
 * @email{jyh@cs.caltech.edu}
 * @end[license]
 *)
extends M_x86_asm
extends M_util

open M_util

open Refiner.Refiner.TermType

open Mp_resource
open Term_match_table

open Tactic_type.Conversionals
open Tactic_type.Sequent

open Top_conversionals

(************************************************************************
 * REDUCTION RESOURCES                                                   *
 ************************************************************************)

(*!
 * @begin[doc]
 * @resources
 *
 * @bf{The @Comment!resource[before_ra_resource]}
 *
 * The @tt{before_ra} resource provides a generic method for
 * defining @emph{CPS transformation}.  The @conv[before_raC] conversion
 * can be used to apply this evaluator.
 *
 * The implementation of the @tt{before_ra_resource} and the @tt[before_raC]
 * conversion rely on tables to store the shape of redices, together with the
 * conversions for the reduction.
 *
 * @docoff
 * @end[doc]
 *)
let resource before_ra =
   table_resource_info identity extract_data

let before_raTopC_env e =
   get_resource_arg (env_arg e) get_before_ra_resource

let before_raTopC = funC before_raTopC_env

let before_raC =
   repeatC (higherC before_raTopC)

let resource after_ra =
   table_resource_info identity extract_data

let after_raTopC_env e =
   get_resource_arg (env_arg e) get_after_ra_resource

let after_raTopC = funC after_raTopC_env

let after_raC =
   repeatC (higherC after_raTopC)

(************************************************************************
 * Optimizations for before (and after) register allocation.
 *)

(*
 * Dead instruction elimination.
 *)
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

(*
 * Remove reserves of 0 bytes.
 *)
prim_rw delete_null_reserve :
   Cmp["cmp"]{'a1; 'a2;
   Jcc[opcode:s]{'cc; AsmReserve[0:n]{'params};
   'rest}}
   <-->
   'rest

(*! @docoff *)

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
