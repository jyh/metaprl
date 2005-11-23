doc <:doc<
   @module[Dtactic]

   The @tactic[meta_dT] tactic is the analog of @tactic[dT], but
   for the meta-logic.

   @begin[license]

   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 1998-2005 Mojave Group, Caltech

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
   Modified by: Aleksey Nogin @email{nogin@cs.cornell.edu}
   @end[license]

   @parents
>>
extends Meta_util
extends Meta_dtactic
extends Meta_implies

doc docoff

open Refiner.Refiner.Refine

open Basic_tactics
open Base_meta
open Meta_util

(*
 * Cut.
 *
 *    S1 --> ... --> Sn --> T1
 *    S1 --> ... --> Sn --> T1 --> T2
 *    -------------------------------
 *    S1 --> ... --> Sn --> T2
 *)
let mcut_extract addrs params goal subgoals =
   raise (Invalid_argument "mcut_extract: not implemented")

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
      [seq1; seq2], mcut_extract

ml_rule mcut 'i 't : 'T =
   mcut_code

let metaAssertAtT i t =
   mcut (mk_meta_num i) t

let metaAssertT t =
   mcut (mk_meta_num (-1)) t

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
