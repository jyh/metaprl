(*!
 * @begin[doc]
 * @module[Mp_mc_fir_phobos]
 *
 * Convert preFIR terms to FIR terms.
 * @end[doc]
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
 *
 * Copyright (C) 2002 Adam Granicz, Caltech
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
 * Author: Adam Granicz
 * @email{granicz@cs.caltech.edu}
 * @end[license]
 *)

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)
extends Base_meta
extends Mp_mc_theory
(*! @docoff *)

open Top_conversionals
open Mp_mc_base

(*
 * This function takes a list of ((redex, _), (contractum, _)),
 * representing a list of iforms.  The conversional returned
 * applies all these rewrites until a fix point is reached.
 *)
let applyIFormsAndBaseC iform_rewrites =
   let patterns = List.map
      (fun ((redex, _), (contractum, _)) ->

         (* Debugging output. *)
         debug_string "##### creating iform:";
         debug_term redex;
         debug_string "<-->";
         debug_term contractum;

         (* Create the iform now. *)
         create_iform "post_proc" false redex contractum

      ) iform_rewrites
   in
      (repeatC (higherC (firstC (reduceTopC :: patterns))))

let applyIFormsC iform_rewrites =
   let patterns = List.map
      (fun ((redex, _), (contractum, _)) ->

         (* Debugging output. *)
         debug_string "##### creating iform:";
         debug_term redex;
         debug_string "<-->";
         debug_term contractum;

         (* Create the iform now. *)
         create_iform "post_proc" false redex contractum

      ) iform_rewrites
   in
   match patterns with
      [] ->
         idC
    | _ ->
         (repeatC (higherC (applyAllC (patterns))))

let applyMetaBaseC =
   (repeatC (higherC (applyAllC [
      Base_meta.reduce_meta_sum;
      Base_meta.reduce_meta_diff;
      Base_meta.reduce_meta_prod;
      Base_meta.reduce_meta_quot;
      Base_meta.reduce_meta_rem])))
