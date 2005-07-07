doc <:doc<
   @theory{ILC: A Foundation for Automated Reasoning About Pointer Programs}
   @module[Ilc_core]

   The @tt[Ilc_core] module implements the basic language of the ILC.

   @docoff
   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html for more information.

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

   Authors: Aleksey Nogin @email{nogin@cs.caltech.edu}
            Limin Jia @email{ljia@cs.princeton.edu}
   @end[license]
>>

doc <:doc< @parents >>
extends Base_theory
extends Itt_theory

doc <:doc<
   @terms
   @modsubsection{Meta-Types}
   << Linear >> is the meta-type of all the linear logic formulas. <<AffLinear>> is the subtype of
   << Linear >> that contains only those expressions that may appear in the non-linear context (namely,
   linear formulas with a bang or a circle on top).  << DataType >> is the
   meta-type for the ``base'' types of the PL. We will also use the << Term >> meta-type
   of the type theory expressions. <<TyScope>> is the meta-meta-type of meta-types that may
   appear in the ilc non-linear contexts.

   Note that the meta-types are only here to help detect typos in the axiom and theorem statements,
   and they are not part of the formal specification of the ILC calculus (and all the types and type
   annotations other than <<Judgment>> may be safely deleted).

   Further documentation of the syntax declarations and the meta-type system may be found in
   @tt["doc/ps/theories/misc.{ps,pdf}"] (to obtain these files, run @tt["omake doc/ps/theories/misc.ps"] or
   @tt["omake doc/ps/theories/misc.pdf"] respectively).
>>

declare typeclass TyScope -> Ty

declare typeclass Linear              -> Dform
declare typeclass AffLinear : TyScope -> Linear (* XXX: Aleksey: Is there a better name for it? *)
declare typeclass DataType  : TyScope -> Dform

doc <:doc<
   The <<DataType>> terms in hypothesis list may introduce bindings of meta-type <<Term>>, while
   the <<AffLinear>> terms may not introduce bindings.
>>

declare type TyElem{'ty : TyScope} : Ty
declare rewrite TyElem{AffLinear} <--> Ignore
declare rewrite TyElem{DataType} <--> Term

doc <:doc<
   <<LinearSeq>> meta-type will only be used to specify the internal structure of the ILC
   sequents.
>>

declare typeclass LinearSeq -> Dform

doc <:doc<
   @modsubsection{Judgments}
   The @tt[ilc] sequents may have terms of any of the TyScope types in its hypotheses and its conclusion
   must be a <<LinearSeq>> sequent. The resulting sequent will have the meta-type <<Judgment>> of ``top-level''
   @MetaPRL judgments.

   The @tt[linear] sequents should have <<Linear>> formulas in both hypotheses and conclusion, those linear
   hypotheses may not introduce bindings.
>>
declare sequent[ilc]    { exst a : TyScope. TyElem{'a} : 'a >- LinearSeq } : Judgment
declare sequent[linear] { Ignore : Linear >- Linear } : LinearSeq

doc <:doc<
   @modsubsection{Theory Transitions}
>>

declare circ{'t : Term} : AffLinear
declare data{'t : Term} : DataType

doc <:doc<
   @modsubsection{Linear Connectives}
>>

(*
 * For connectives such as implications and conjuntions we need to use names
 * that would not coflict with the type theory ones (in order not to be forced
 * to use fully qualified names for the type theory connectives)
 *
 * This is not a complete list (yet).
 *)
declare bang{'t : Linear} : AffLinear
declare tensor{'t1 : Linear; 't2 : Linear} : Linear
declare plus{'t1 : Linear; 't2 : Linear} : Linear
declare impl{'t1 : Linear; 't2 : Linear} : Linear
declare conj{'t1 : Linear; 't2 : Linear} : Linear
declare one : Linear

(* This theory does not use proof terms *)
declare default_extract
