(*!
 * @begin[doc]
 * @module[Mfir_sequent]
 *
 * The @tt[Mfir_sequent] module declares terms used in FIR theory sequents.
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

(**************************************************************************
 * Declarations.
 **************************************************************************)

(*!
 * @begin[doc]
 * @terms
 * @modsubsection{Sequent tags}
 *
 * The term @tt[mfir] is used to tag FIR theory sequents.  The term @tt[it] is
 * used in FIR theory rules to express (the lack of) computational content of
 * a proof.
 * @end[doc]
 *)

declare mfir
declare it

(*!
 * @begin[doc]
 * @modsubsection{Judgments}
 *
 * A proof of @tt[wf_context] demonstrates that a sequent's context is
 * well-formed.
 * @end[doc]
 *)

declare wf_context

(*!
 * @begin[doc]
 *
 * A proof of @tt[has_type] consists of showing that a term @tt[t] has type
 * @tt[ty].  The parameter @tt[str] is a hint as to the nature of the term
 * being typed.
 * @end[doc]
 *)

declare has_type[str:s]{ 't; 'ty }

(*!
 * @docoff
 *)

(**************************************************************************
 * Display forms.
 **************************************************************************)

(*
 * Sequent tags.
 *)

dform mfir_df : except_mode[src] ::
   mfir =
   it["mfir"]

dform it_df1 : except_mode[src] :: except_mode[tex] ::
   it =
   cdot

dform it_df2 : mode[tex] ::
   it =
   izone `"\\bullet" ezone

(*
 * Judgments.
 *)

dform wf_context_df1 : except_mode[src] :: except_mode[tex] ::
   wf_context =
   cdot

dform wf_context_df2 : mode[tex] ::
   wf_context =
   izone `"\\diamond" ezone

dform has_type_df : except_mode[src] ::
   has_type[str:s]{ 't; 'ty } =
   slot{'t} `":" slot{'ty} `" [" it[str:s] `"]"
