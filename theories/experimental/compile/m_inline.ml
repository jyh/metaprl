doc <:doc<
   @begin[spelling]
   inlined inlining
   @end[spelling]

   @begin[doc]
   @module[M_inline]

   This module implements a simple form of constant folding and
   constant inlining.  We do not inline functions due to our somewhat
   cumbersome choice of representation for function definitions.
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
extends M_ir
doc docoff

open Base_meta
open Tactic_type.Tacticals
open Top_conversionals

doc <:doc<
   @begin[doc]
   @modsection{Meta-arithmetic}

   We use the @MetaPRL built-in meta-arithmetic to fold constants.
   Arithmetic is performed using meta-terms, so we need a
   way to convert back to a number (i.e., atom).
   @end[doc]
>>
declare MetaInt{'e}

prim_rw meta_int_elim {| reduce |} : MetaInt{meta_num[i:n]} <--> AtomInt[i:n]

doc <:doc<
   @begin[doc]
   @rewrites

   Each of the rewrites below is added to the @tt{reduce_resource}.
   We group them into ones to perform constant folding and ones to
   inline constants.

   @modsubsection{Constant folding}

   Constant folding is straightforward given the meta-arithmetic
   provided by @MetaPRL.
   @end[doc]
>>
prim_rw reduce_add :
   AtomBinop{AddOp; AtomInt[i:n]; AtomInt[j:n]} <--> MetaInt{meta_sum[i:n, j:n]}

prim_rw reduce_sub :
   AtomBinop{SubOp; AtomInt[i:n]; AtomInt[j:n]} <--> MetaInt{meta_diff[i:n, j:n]}

prim_rw reduce_mul :
   AtomBinop{MulOp; AtomInt[i:n]; AtomInt[j:n]} <--> MetaInt{meta_prod[i:n, j:n]}

prim_rw reduce_div :
   AtomBinop{DivOp; AtomInt[i:n]; AtomInt[j:n]} <--> MetaInt{meta_quot[i:n, j:n]}

doc <:doc<
   @begin[doc]
   @modsubsection{Constant inlining}

   Constant inlining is also straightforward.  We can inline the branches
   of conditional expressions if we know the guards at compile time.
   @end[doc]
>>
prim_rw reduce_let_atom_true {| reduce |} :
   LetAtom{AtomTrue; v. 'e['v]} <--> 'e[AtomTrue]

prim_rw reduce_let_atom_false {| reduce |} :
   LetAtom{AtomFalse; v. 'e['v]} <--> 'e[AtomFalse]

prim_rw reduce_let_atom_int {| reduce |} :
   LetAtom{AtomInt[i:n]; v. 'e['v]} <--> 'e[AtomInt[i:n]]

prim_rw reduce_let_atom_var {| reduce |} :
   LetAtom{AtomVar{'v1}; v2. 'e['v2]} <--> 'e['v1]

prim_rw reduce_if_true {| reduce |} :
   If{AtomTrue; 'e1; 'e2} <--> 'e1

prim_rw reduce_if_false {| reduce |} :
   If{AtomFalse; 'e1; 'e2} <--> 'e2

doc <:doc<
   @begin[doc]
   We need these last three rewrites to ensure that the final program
   produced is well-formed.  Variables whose values have been inlined
   are rewritten to their value.
   @end[doc]
>>
prim_rw unfold_atom_var_true {| reduce |} :
   AtomVar{AtomTrue} <--> AtomTrue

prim_rw unfold_atom_var_false {| reduce |} :
   AtomVar{AtomFalse} <--> AtomFalse

prim_rw unfold_atom_var_int {| reduce |} :
   AtomVar{AtomInt[i:n]} <--> AtomInt[i:n]

doc docoff

(*
 * Add all these rules to the reduce resource.
 *)
let resource reduce += [
     << AtomBinop{AddOp; AtomInt[i:n]; AtomInt[j:n]} >>, (reduce_add thenC addrC [0] reduce_meta_sum);
     << AtomBinop{SubOp; AtomInt[i:n]; AtomInt[j:n]} >>, (reduce_sub thenC addrC [0] reduce_meta_diff);
     << AtomBinop{MulOp; AtomInt[i:n]; AtomInt[j:n]} >>, (reduce_mul thenC addrC [0] reduce_meta_prod);
     << AtomBinop{DivOp; AtomInt[i:n]; AtomInt[j:n]} >>, (reduce_div thenC addrC [0] reduce_meta_quot);
]

(*
 * Inlining.
 *)
let inlineT =
   onAllHypsT (fun i -> tryT (rw reduceC i)) thenT rw reduceC 0

dform int_df : MetaInt{'t} = math_it["Meta"] `"[" 't `"]"

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
