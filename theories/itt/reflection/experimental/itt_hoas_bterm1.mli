doc <:doc<
   @module[Itt_hoas_bterm]
   The @tt[Itt_hoas_bterm] module defines the inductive type <<BTerm>>
   and establishes the appropriate induction rules for this type.

   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

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

   Author: Aleksey Kopylov @email{kopylov@cs.caltech.edu}

   @end[license]
>>
extends Itt_hoas_destterm

open Basic_tactics

declare compatible_shapes{'bdepth;'op;'subterms}
declare dom{'BT}
declare mk{'x}
declare dest{'bt}
declare Iter{'X}
declare BT{'n}
declare BTerm
declare BTerm{'i}
declare dummy

(* Conversions *)
topval unfold_compatible_shapes : conv
topval unfold_dom : conv
topval unfold_mk : conv
topval unfold_dest : conv
topval unfold_Iter : conv
topval unfold_BT : conv
topval unfold_BTerm : conv
topval unfold_BTerm2 : conv
topval unfold_ndepth : conv
topval unfold_dummy : conv

topval fold_compatible_shapes : conv
topval fold_dom : conv
topval fold_mk : conv
topval fold_Iter : conv
topval fold_dest : conv
topval fold_BT : conv
topval fold_BTerm : conv
topval fold_BTerm2 : conv
topval fold_ndepth : conv
topval fold_dummy : conv

(* Boolean equality *)
declare beq_bterm{'t1; 't2}
declare beq_bterm_list{'l1; 'l2}
topval fold_beq_bterm : conv
topval fold_beq_bterm_list : conv

(* 'e --> bind{x. 'e['x]} *)
topval etaExpandC : term -> conv

(* Tactics *)
val mk_bterm_wf : tactic
val mk_bterm_wf2 : tactic

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
