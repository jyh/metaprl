(*!
 * @begin[doc]
 * @module[Mfir_bool]
 *
 * The @tt[Mfir_bool] module implements meta-booleans for the FIR theory.
 * @end[doc]
 *
 * ------------------------------------------------------------------------
 *
 * @begin[license]
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.  Additional
 * information about the system is available at
 * http://www.metaprl.org/
 *
 * Copyright (C) 2002 Brian Emre Aydemir, Caltech
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
 * Author: Brian Emre Aydemir
 * @email{emre@cs.caltech.edu}
 * @end[license]
 *)

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)

extends Base_theory

(*!
 * @docoff
 *)

open Base_meta
open Top_conversionals


(**************************************************************************
 * Declarations.
 **************************************************************************)

(*!
 * @begin[doc]
 * @terms
 *
 * The terms @tt[true] and @tt[false] are boolean constants.
 * @end[doc]
 *)

declare "true"
declare "false"

(*!
 * @begin[doc]
 *
 * The terms @tt[or], @tt[and], and @tt[not] are boolean connectives.
 * @end[doc]
 *)

declare "or"{ 'bool1; 'bool2 }
declare "and"{ 'bool1; 'bool2 }
declare "not"{ 'boolean }

(*!
 * @begin[doc]
 *
 * The term @tt[ifthenelse] performs a case analysis on @tt[test].
 * @end[doc]
 *)

declare ifthenelse{ 'test; 'true_case; 'false_case }


(**************************************************************************
 * Rewrites.
 **************************************************************************)

(*!
 * @begin[doc]
 * @rewrites
 *
 * Case analysis on booleans is straightforward.
 * @end[doc]
 *)

prim_rw reduce_ifthenelse_true :
   ifthenelse{ "true"; 't; 'f } <-->
   't

prim_rw reduce_ifthenelse_false :
   ifthenelse{ "false"; 't; 'f } <-->
   'f

(*!
 * @begin[doc]
 *
 * The logical connectives are treated classically.
 * @end[doc]
 *)

prim_rw reduce_and :
   "and"{ 'bool1; 'bool2 } <-->
   ifthenelse{ 'bool1; 'bool2; "false" }

prim_rw reduce_or :
   "or"{ 'bool1; 'bool2 } <-->
   ifthenelse{ 'bool1; "true"; 'bool2 }

prim_rw reduce_not :
   "not"{ 'b } <-->
   ifthenelse{ 'b; "false"; "true" }

(*!
 * @docoff
 *)

let resource reduce += [
   << "and"{ 'bool1; 'bool2 } >>, reduce_and;
   << "or"{ 'bool1; 'bool2 } >>, reduce_or;
   << "not"{ 'b } >>, reduce_not;
   << ifthenelse{ "true"; 'true_case; 'false_case } >>,
      reduce_ifthenelse_true;
   << ifthenelse{ "false"; 'true_case; 'false_case } >>,
      reduce_ifthenelse_false
]


(**************************************************************************
 * Display forms.
 **************************************************************************)

(*
 * Constants.
 *)

dform true_df : except_mode[src] ::
   "true" =
   bf["true"]

dform false_df : except_mode[src] ::
   "false" =
   bf["false"]

(*
 * Connectives.
 *)

dform or_df : except_mode[src] ::
   "or"{ 'bool1; 'bool2 } =
   `"(" slot{'bool1} vee space slot{'bool2} `")"

dform and_df : except_mode[src] ::
   "and"{ 'bool1; 'bool2 } =
   `"(" slot{'bool1} wedge space slot{'bool2} `")"

dform not_df : except_mode[src] ::
   "not"{ 'boolean } =
   tneg slot{'boolean}

(*
 * Case analysis.
 *)

dform ifthenelse_df : except_mode[src] ::
   ifthenelse{ 'test; 'true_case; 'false_case } =
   pushm[0] szone push_indent bf["if"] hspace
      szone slot{'test} ezone popm hspace
      push_indent bf["then"] hspace
      szone slot{'true_case} ezone popm hspace
      push_indent bf["else"] hspace
      szone slot{'false_case} ezone popm
      ezone popm
