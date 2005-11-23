doc <:doc<
   @module["meta-struct"]
   Structural rules in the meta-logic

   @begin[license]

   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 2005 Mojave Group, Caltech

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

   Author: Jason Hickey @email{jyh@cs.caltech.edu}
   @end[license]

   @parents
>>
extends Meta_util

doc docoff

open Lm_printf

open Refiner.Refiner.Refine

open Basic_tactics
open Base_meta
open Meta_util

(************************************************************************
 * Cut.
 *
 *    S1 --> ... --> Si --> ... --> Sn --> T1
 *    S1 --> ... --> T1 --> Si --> ... --> Sn --> T2
 *    ----------------------------------------------
 *    S1 --> ... --> Si --> ... --> Sn --> T2
 *
 * Cut is already primitive in the refiner.
 * However, we would like a more general form that allows
 * the position of the cut-in goal to be specified.
 *)
let mcut_extract i addrs params goal subgoals args rest =
   match rest with
      [cut_lemma; cut_then] ->
         cut_then (Lm_list_util.insert_nth i (cut_lemma args) args)
    | _ ->
         raise (RefineError ("mcut_extract", StringError "illegal extract"))

let mcut_code addrs params goal assums =
   let i, t =
      match params with
         [i; t] ->
            dest_meta_num i, t
       | _ ->
            raise (RefineError ("mcut", StringError "two arguments required"))
   in
   let len = List.length assums in
   let i =
      if i < 0 then
         len + i + 1
      else if i = 0 then
         len
      else
         i - 1
   in
   let () =
      if i < 0 || i > len then
         raise (RefineError ("mcut", StringIntError ("argument out of range", i + 1)))
   in
   let seq1 = mk_msequent t assums in
   let seq2 = mk_msequent goal (Lm_list_util.insert_nth i t assums) in
      [seq1; seq2], mcut_extract i

ml_rule mcut 'i 't : 'T =
   mcut_code

let metaAssertAtT i t =
   mcut (mk_meta_num i) t

let metaAssertT t =
   metaAssertAtT (-1) t

(************************************************************************
 * Thinning.
 *
 *    S1 --> ... --> S_{i - 1} --> S_{i + 1} --> ... --> Sn
 *    ------------------------------------------------------------
 *    S1 --> ... --> S_{i - 1} --> Si --> S_{i + 1} --> ... --> Sn
 *)
let mthin_extract i addrs params goal subgoals args rest =
   match rest with
      [f] ->
         f (Lm_list_util.remove_nth i args)
    | _ ->
         raise (RefineError ("mthin_extract", StringError "illegal extract"))

let mthin_code addrs params goal assums =
   let i = get_pos_assum_from_params params assums - 1 in
   let seq = mk_msequent goal (Lm_list_util.remove_nth i assums) in
      [seq], mthin_extract i

ml_rule mthin 'i : 'T =
   mthin_code

let metaThinT i =
   mthin (mk_meta_num i)

(************************************************************************
 * Tactics.
 *)

(*
 * Move an assumption to a new location.
 *)
let moveToAssumT i j = funT (fun p ->
   let i = Sequent.get_pos_assum_num p i in
   let j = Sequent.get_pos_assum_num p j in
   let k, j =
      if j > i then
         i, j + 1
      else
         i + 1, j
   in
   let t = Sequent.nth_assum p i in
      metaAssertAtT j t
      thenLT [nthAssumT i; metaThinT k])

(************************************************************************
 * Tests.x
 *)
interactive test1 'S1 'S2 'S3 'S4 'S5 :
   sequent { <H> >- 'S1 } -->
   sequent { <H> >- 'S2 } -->
   sequent { <H> >- 'S3 } -->
   sequent { <H> >- 'S4 } -->
   sequent { <H> >- 'S5 } -->
   sequent { <H> >- 'T }

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
