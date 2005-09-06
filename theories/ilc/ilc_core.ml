doc <:doc<
   @theory{ILC: A Foundation for Automated Reasoning About Pointer Programs}
   @module[Ilc_core]

   The @tt[Ilc_core] module implements the basic language of the ILC.

   This is currently work in progress (only a tiny part of ILC is actually implemented).

   @docoff
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

   Authors: Aleksey Nogin @email{nogin@cs.caltech.edu}
            Limin Jia @email{ljia@cs.princeton.edu}
   @end[license]
>>

doc <:doc< @parents >>
extends Base_theory
extends Itt_theory

doc docoff

open Basic_tactics
open Itt_logic

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
declare Parameter
declare bang{'t : Linear} : AffLinear
declare tensor{'t1 : Linear; 't2 : Linear} : Linear
declare plus{'t1 : Linear; 't2 : Linear} : Linear
declare impl{'t1 : Linear; 't2 : Linear} : Linear
declare conj{'t1 : Linear; 't2 : Linear} : Linear
declare one : Linear
declare top : Linear
declare zero : Linear
declare exists{x.'B['x] : Linear} : Linear
declare forall{x.'B['x] : Linear} : Linear

doc <:doc<
   @rules
   @modsubsection{Rules of the Linear Logic}
>>

(*
 * Aleksey:
 * - for now, I only wrote down a few rules to provide an example
 * - syntax: <#X> is the same thing as <X>, except it stands for a context that
 *   may _not_ introduce bindings. Strictly speaking, all the linear contexts
 *   should be annotated this way, but in most cases it does not really matter.
 * - tensor_elim allows emininating tensor from any linear formula (not just the
 *   last one as in the paper) for efficiency - this way one does not have to use
 *   the commutativity rule first.
 *)

prim top_intro {| intro [] |} :
   ilc{| <H> >- linear{| <L> >- top |} |}

prim one_intro {| intro [] |} :
   ilc{| <H> >- linear{| >- one |} |}

prim one_elim 'L :
   ilc{| <H> >- linear{| <L>; <M> >- 'C |} |} -->
     ilc{| <H> >- linear{| <L>; one ; <M> >- 'C |} |}

prim zero_elim 'L :
   ilc{| <H> >- linear{| <L>; zero ; <M> >- 'C |} |}


prim tensor_elim 'L :
   ilc{| <H> >- linear{| <L>; 'A1; 'A2; <M> >- 'C |} |} -->
   ilc{| <H> >- linear{| <L>; tensor{'A1; 'A2}; <M> >- 'C |} |}

prim tensor_intro 'L1 :
   ilc{| <H> >- linear{| <#L1> >- 'C1 |} |} -->
   ilc{| <H> >- linear{| <#L2> >- 'C2 |} |} -->
   ilc{| <H> >- linear{| <#L1>; <#L2> >- tensor{'C1; 'C2} |} |}

prim conj_intro {| intro [] |} :
   ilc{| <H> >- linear{| <#L> >- 'C1 |} |} -->
   ilc{| <H> >- linear{| <#L> >- 'C2 |} |} -->
   ilc{| <H> >- linear{| <#L> >- conj{'C1; 'C2} |} |}

prim conj_elim_left 'L:
   ilc{| <H> >- linear{| <#L>; 'C1 ;<M> >- 'C |} |} -->
   ilc{| <H> >- linear{| <#L>; conj{'C1; 'C2}; <M> >- 'C |} |}

prim conj_elim_right 'L:
   ilc{| <H> >- linear{| <#L>; 'C2 ;<M> >- 'C |} |} -->
   ilc{| <H> >- linear{| <#L>; conj{'C1; 'C2}; <M> >- 'C |} |}

prim plus_intro_left{| intro[SelectOption 1]|} :
   ilc{| <H> >- linear{| <#L> >- 'C1 |} |} -->
   ilc{| <H> >- linear{| <#L> >- plus{'C1; 'C2} |} |}

prim plus_intro_right{| intro[SelectOption 2]|} :
   ilc{| <H> >- linear{| <#L> >- 'C2 |} |} -->
   ilc{| <H> >- linear{| <#L> >- plus{'C1; 'C2} |} |}

prim plus_elim 'L:
   ilc{| <H> >- linear{| <#L>; 'C1 ;<M> >- 'C |} |} -->
   ilc{| <H> >- linear{| <#L>; 'C2 ;<M> >- 'C |} |} -->
   ilc{| <H> >- linear{| <#L>; plus{'C1; 'C2}; <M> >- 'C |} |}

prim impl_intro {| intro [] |} :
   ilc{| <H> >- linear{| <#L>; 'C1 >- 'C2 |} |} -->
   ilc{| <H> >- linear{| <#L> >- impl{'C1; 'C2} |} |}

prim impl_elim 'L1 :
   ilc{| <H> >- linear{| <#L1>; 'C1 >- 'C1 |} |} -->
   ilc{| <H> >- linear{| <#L2>; 'C2 >- 'C |} |} -->
   ilc{| <H> >- linear{| <#L1>;<#L2>; impl{'C1; 'C2} >- 'C |} |}

prim forall_intro{| intro[] |}  :
   ilc{| <H>; x: data{Parameter} >- linear{| <L> >- 'B['x] |} |} -->
   ilc{| <H> >- linear{| <L> >- forall{y.'B['y]} |} |}

prim forall_elim 'L 'a :
   ilc{| <H> >- linear {| <L>; 'B['a]; <M> >- 'C |} |} -->
   ilc{| <H> >- linear {| <L>; forall{x.'B['x]} ; <M> >- 'C |} |}

prim exists_intro{| intro[] |} 'a :
   ilc{| <H> >- linear{| <L> >- 'B['a] |} |} -->
   ilc{| <H> >- linear{| <L> >- exists{x.'B['x]} |} |}

prim exists_elim 'L  :
   ilc{| <H>; x: data{Parameter} >- linear {| <L>; 'B['x]; <M> >- 'C |} |} -->
   ilc{| <H> >- linear {| <L>; exists{x.'B['x]} ; <M> >- 'C |} |}

prim bang_intro {| intro[] |}:
   ilc{| <H> >- linear{| >- 'A |} |} -->
   ilc{| <H> >- linear{| >- bang{'A} |} |}

prim bang_elim 'L :
   ilc{| <H>; bang{'A} >- linear{| <#L>; <M> >- 'C |} |} -->
   ilc{| <H> >- linear{| <#L>; bang{'A}; <M> >- 'C |} |}

prim lin_hyp :
   ilc{| <H> >- linear{| 'A >- 'A |} |}

prim un_hyp 'H:
   ilc{| <H> ; bang{'A} ; <M> >- linear{| >- 'A |} |}



doc <:doc<
   @modsubsection{Structural Rules}
   Thinning (AKA weakening) rule.
>>
prim axiom 'L :
   ilc{| <H> >- linear{| <L>; 'A; <M> >- 'A |} |}

prim thin 'H 'J:
   ilc{| <H>; <K> >- linear{| <L> >- 'C |} |} -->
   ilc{| <H>; <J>; < K<|H|> > >- linear{| < L<|H; K|> > >- 'C<|H; K; L|> |} |}

doc <:doc< Commutativity rule for the non-linear context >>

prim commut_nl 'H 'J1 'J2:
   ilc{| <H>; <J2>; <J1>; <K> >- linear{| <L> >- 'C |} |} -->
   ilc{| <H>; <J1>; < J2<|H|> >; <K> >- linear{| <L> >- 'C |} |}

doc <:doc< Commutativity rule for the linear context >>

prim commut_l 'J 'K1 'K2:
   ilc{| <H> >- linear{| <J>; <K2>; <K1>; <L> >- 'C |} |} -->
   ilc{| <H> >- linear{| <J>; <K1>; <K2 <|H; J|> >; <L> >- 'C |} |}

doc <:doc<
   @modsubsection{Connection between the Type Theory and Linear Logic}
   We use the ``helper'' sequent @tt[erase] (denoted <<seq_sep{erase}>>) here.
>>

(* Note: we keep "erase" somewhat "internal" by not declaring it in the .mli interface file *)
declare sequent[erase] { exst a : TyScope. TyElem{'a} : 'a >- Term } : Term

prim circ_elim 'L :
   ilc{| <H>; circ{'A} >- linear{| <#L>; <M> >- 'C |} |} -->
   ilc{| <H> >- linear{| <#L>; circ{'A}; <M> >- 'C |} |}

prim circ_intro {| intro [] |} :
   sequent{ >- erase{| <H> >- 'C |} } -->
   ilc {| <H> >- linear{| >- circ{'C} |} |}

(* XXX: Aleksey: the 3 "erase" rules below may need some extra ``well-formedness'' assumptions *)

prim erase_type {| intro [] |} :
   sequent{ <H>; x: 'T >- erase{| <J['x]> >- 'C['x] |} } -->
   sequent{ <H> >- erase{| x: data{'T}; <J['x]> >- 'C['x] |} }

prim erase_circ {| intro [] |} :
   sequent{ <H>; 'A >- erase{| <J> >- 'C |} } -->
   sequent{ <H> >- erase{| circ{'A}; <J> >- 'C |} }

(* XXX: Aleksey: erase_bang is probably redundant in presence of the "thin" rule *)
prim erase_bang {| intro [] |} :
   sequent{ <H> >- erase{| <J> >- 'C |} } -->
   sequent{ <H> >- erase{| bang{'A}; <J> >- 'C |} }

prim absurdity :
   ilc{| <H> >- linear{| >- circ{"false"} |} |} -->
   ilc{| <H> >- linear{| <J> >- 'C |} |}

prim hole:
       ilc{| <H> >- linear{| <L> >- 'C |} |}

doc docoff

(*******************************************************
 * DISPLAY FORMS (AKA pretty-printing specifications)
 *)

prec prec_bang
prec prec_bang > prec_not

dform bang_df : parens :: "prec"[prec_bang] :: bang{'t} =
   `"!" slot["lt"]{'t}

dform circ_df : parens :: "prec"[prec_bang] :: circ{'t} =
   Mpsymbols!bigcirc slot["lt"]{'t}

(*
 * XXX: Aleksey: Is there a canonical paranthization of "T1 tensor T2 tensor T3"?
 * If so, we might want to replace one of the "le" below with an "lt"
 *)
dform tensor_df : parens :: "prec"[prec_and] :: tensor{'t1; 't2} =
   slot["le"]{'t1} Mpsymbols!tensor slot["le"]{'t2}

dform plus_df : parens :: "prec"[prec_or] :: plus{'t1; 't2} =
   slot["le"]{'t1} Mpsymbols!oplus slot["le"]{'t2}

dform implies_df : parens :: "prec"[prec_implies] :: impl{'t1; 't2} =
   slot["le"]{'t1} Mpsymbols!multimap slot["lt"]{'t2}

dform conj_df : parens :: "prec"[prec_or] :: conj{'t1; 't2} =
   slot["le"]{'t1} `"&" slot["le"]{'t2}

dform one_df : one = bf["1"]

dform top_df : top = bf["T"]

dform zero_df : zero = bf["0"]

dform forall_df : parens :: "prec"[prec_quant] :: forall{x. 'B} =
   szone pushm[3] forall slot{'x} `"." hspace slot{'B} popm ezone

dform exists_df : parens :: "prec"[prec_quant] :: exists{x. 'B} =
   szone pushm[3] exists slot{'x} `"." hspace slot{'B} popm ezone

(*
 * Sequents
 *)
dform tt_sequent_df : sequent_arg = sub["TT"]

dform ilc_seq_df : seq_sep{ilc} = bf["|| "]

dform linear_seq_df : linear = subl

dform erase_seq_df : erase = sube

dform default_extract_df : sequent('arg){ <H> >- default_extract } = `""
dform default_extract_df2 : default_extract = `""
