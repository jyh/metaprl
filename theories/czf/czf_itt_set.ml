doc <:doc< 
   @begin[doc]
   @module[Czf_itt_set]
  
   The @tt{Czf_itt_set} module provides the basic definition
   of sets and their elements.  The @tt{set} term denotes
   the type of all sets, defined using the $W$-type in
   the module @hrefmodule[Itt_w], as follows:
  
   $$@set @equiv @w{T; @univ{1}; T}.$$
  
   That is, the @emph{sets} are pairs of a type $T @in @univ{1}$,
   and a function $T @rightarrow @set$ that specifies the
   elements of the set.  Note that the type $T$ can be @emph{any}
   type in $@univ{1}$; equality of sets is is general undecidable, and
   their members can't necessarily be enumerated.  This is a
   @emph{constructive} theory, not a decidable theory.  Of course,
   there will be special cases where equality of sets is decidable.
  
   The sets are defined with the terms $@collect{x; T; f[x]}$, where
   $T$ is a type in $@univ{1}$, and $f[x]$ is a set for any index $x @in T$.
   The sets $f[x]$ are the @emph{elements} of the set, and $T$ is
   the a type used as their index.  For example, the following set
   is empty.
  
   $$@{@} = @collect{x; @void; x}$$
  
   @noindent
   The following set is the singleton set containing the empty
   set.
  
   $$@{@{@}@} = @collect{x; @unit; @{@}}$$
  
   @noindent
   The following set is equivalent.
  
   $$@{@{@}@}' = @collect{x; @int; @{@}}$$
  
   This raises an important point about equality.
   The membership equality defined ion $W$-types
   requires equality on the index type $T$ as well as the element
   function $f$.  The two sets $@{@{@}@}$ and $@{@{@}@}'$ are
   @emph{not} equal in this type because they have the provably
   different index types $@unit$ and $@int$, even though they have
   the same elements.
  
   One solution to this problem would be to use a quotient
   construction using the quotient type defined in the
   @hrefmodule[Itt_quotient] module.  The @hrefmodule[Czf_itt_eq]
   module defines extensional set equality $@equiv_{@i{ext}}$, and
   we could potentially define the ``real'' sets with the following
   type definition.
  
   $$@i{real@_sets} @equiv (@quot{set; s_1; s_2; s_1 @equiv_{@i{ext}} s_2})$$
  
   This type definition would require explicit functionality
   reasoning on all functions over @i{real_set}.  This construction,
   however, makes these functionality proofs impossible because it
   omits the computational content of the equivalence judgment,
   which is a necessary part of the proof.
  
   Alternative quotient formulations may be possible, but we have not
   pursued this direction extensively.  Instead, we introduce set
   equality in the @hrefmodule[Czf_itt_eq] module, together with
   explicit functionality predicates for set operators.  In addition,
   we prove the functionality properties for all the primitive
   set operations.
  
   One avenue for improvement in this theory would be to stratify
   the set types to arbitrary type universes $@univ{i}$, which would
   allow for higher-order reasoning on sets, classes, etc.
   @end[doc]
  
   ----------------------------------------------------------------
  
   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.
  
   See the file doc/index.html for information on Nuprl,
   OCaml, and more information about this system.
  
   Copyright (C) 1998 Jason Hickey, Cornell University
  
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
   @email{jyh@cs.cornell.edu}
   @end[license]
>>

doc <:doc< 
   @doc{@parents}
>>
extends Itt_theory
extends Itt_eta
doc docoff
extends Czf_itt_comment

open Printf
open Mp_debug

open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermSubst
open Refiner.Refiner.TermMan
open Refiner.Refiner.Refine
open Refiner.Refiner.RefineError
open Mp_resource
open Term_stable

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Sequent
open Perv
open Mptop

open Base_dtactic
open Base_auto_tactic
open Top_conversionals

open Itt_squash
open Itt_equal
open Itt_rfun
open Itt_dprod
open Itt_union
open Itt_struct
open Itt_logic
open Itt_w

let _ =
   show_loading "Loading Czf_itt_set%t"

let debug_czf_set =
   create_debug (**)
      { debug_name = "czf_set";
        debug_description = "display czf_set operations";
        debug_value = false
      }

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @terms
  
   The @tt{set} term defines the type of sets; the @tt{collect}
   terms are the individual sets.  The @tt[isset] term is the
   well-formedness judgment for the $@set$ type.  The @tt[set_ind] term
   is the induction combinator for computation over sets.  The
   @i{s} argument represents the set; @i{T} is it's index type,
   @i{f} is it's function value, and @i{g} is used to perform
   recursive computations on the children.
   @end[doc]
>>
declare set
declare isset{'s}
declare collect{'T; x. 'a['x]}
declare set_ind{'s; T, f, g. 'b['T; 'f; 'g]}
doc <:doc< @docoff >>

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @rewrites
   The following four rewrites give the primitive definitions
   of the set constructions from the terms in the @Nuprl type theory.
   @end[doc]
>>
prim_rw unfold_set : set <--> w{univ[1:l]; x. 'x}
prim_rw unfold_isset : isset{'s} <--> ('s = 's in set)
prim_rw unfold_collect : collect{'T; x. 'a['x]} <--> tree{'T; lambda{x. 'a['x]}}
prim_rw unfold_set_ind : set_ind{'s; x, f, g. 'b['x; 'f; 'g]} <-->
   tree_ind{'s; x, f, g. 'b['x; 'f; 'g]}

doc <:doc< 
   @begin[doc]
   The @hrefterm[set_ind] term performs a pattern match;
   the normal reduction sequence can be derived from the
   computational behavior of the @hrefterm[tree_ind] term.
   @end[doc]
>>

interactive_rw reduce_set_ind {| reduce |} :
   set_ind{collect{'T; x. 'A['x]}; a, f, g. 'b['a; 'f; 'g]}
   <--> 'b['T; lambda{x. 'A['x]}; lambda{a2. set_ind{.'A['a2]; a, f, g. 'b['a; 'f; 'g]}}]
   
doc docoff

let fold_set        = makeFoldC << set >> unfold_set
let fold_isset      = makeFoldC << isset{'t} >> unfold_isset
let fold_collect    = makeFoldC << collect{'T; x. 'a['x]} >> unfold_collect
let fold_set_ind    = makeFoldC << set_ind{'s; a, f, g. 'b['a; 'f; 'g]} >> unfold_set_ind

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform set_df : except_mode[src] :: set =
   `"set"

dform isset_df : parens :: except_mode[src] :: "prec"[prec_apply] :: isset{'s} =
   slot{'s} `" set"

dform collect_df : parens :: except_mode[src] :: "prec"[prec_apply] :: collect{'T; x. 'a} =
   szone pushm[3] `"collect" " " slot{'x} `":" " " slot{'T} `"." hspace slot{'a} popm ezone

dform set_ind_df : parens :: "prec"[prec_tree_ind] :: set_ind{'z; a, f, g. 'body} =
   szone pushm[3]
   pushm[3] `"let set(" slot{'a} `", " slot{'f} `")." slot{'g} `" = " slot{'z} `" in" popm hspace
   slot{'body} popm ezone

(************************************************************************
 * RELATION TO ITT                                                      *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @rules
   @modsubsection{Typehood and equality}
  
   The @hrefterm[set] term is a type in the @Nuprl type theory.
   The @tt{equal_set} and @tt[isset_assum] rules define the
   @tt[isset] well-formedness judgment.  The @tt[isset_assum]
   is added to the @hreftactic[trivialT] tactic for use as
   default reasoning.
   @end[doc]
>>
interactive set_type {| intro [] |} :
   sequent ['ext] { <H> >- "type"{set} }

(*
 * Equality from sethood.
 *)
interactive equal_set :
   sequent ['ext] { <H> >- isset{'s} } -->
   sequent ['ext] { <H> >- 's = 's in set }

(*
 * By assumption.
 *)
interactive isset_assum 'H :
   sequent ['ext] { <H>; x: set; <J['x]> >- isset{'x} }

doc <:doc< 
   @begin[doc]
   The @hrefterm[collect] terms are well-formed, if their
   index type $T$ is a type in $@univ{1}$, and their element function
   $a$ produces a set for any argument $x @in T$.
   @end[doc]
>>
interactive isset_collect {| intro [] |} :
   sequent [squash] { <H> >- 'T = 'T in univ[1:l] } -->
   sequent [squash] { <H>; y: 'T >- isset{'a['y]} } -->
   sequent ['ext] { <H> >- isset{collect{'T; x. 'a['x]}} }

interactive isset_collect2 {| intro [] |} :
   sequent [squash] { <H> >- 'T = 'T in univ[1:l] } -->
   sequent [squash] { <H>; y: 'T >- isset{'a['y]} } -->
   sequent ['ext] { <H> >- collect{'T; x. 'a['x]} IN set }

doc <:doc< 
   @docoff
   This is how a set is constructed.
>>
interactive isset_apply {| intro [] |} :
   sequent [squash] { <H> >- ('f 'a) IN set } -->
   sequent ['ext] { <H> >- isset{.'f 'a} }

doc <:doc< 
   @begin[doc]
   @modsubsection{Elimination}
  
   The elimination form performs induction on the
   assumption $a@colon @set$.  The inductive argument is this:
   goal $C$ is true for any set $a$ if it is true for some
   set $@collect{x; T; f(x)}$ where the induction hypothesis
   is true on every child $f(x)$ for $x @in T$.  By definition,
   induction requires that tree representing the set be well-founded
   (which is true for all $W$-types).
   @end[doc]
>>
interactive set_elim {| elim [ThinOption thinT] |} 'H :
   sequent ['ext] { <H>;
                    a: set;
                    <J['a]>;
                    T: univ[1:l];
                    f: 'T -> set;
                    w: (all x : 'T. 'C['f 'x]);
                    z: isset{collect{'T; x. 'f 'x}}
                  >- 'C[collect{'T; x. 'f 'x}]
                  } -->
                     sequent ['ext] { <H>; a: set; <J['a]> >- 'C['a] }

doc <:doc< 
   @docoff
   The next two rules allow any set argument to be replaced with
   an @tt{collect} argument.  These rules are never used.
>>
interactive set_split_hyp 'H 's (bind{v. 'A['v]}) :
   sequent [squash] { <H>; x: 'A['s]; <J['x]> >- isset{'s} } -->
   sequent [squash] { <H>; x: 'A['s]; <J['x]>; z: set >- "type"{'A['z]} } -->
   sequent ['ext] { <H>;
                    x: 'A['s];
                    <J['x]>;
                    T: univ[1:l];
                    f: 'T -> set;
                    z: 'A[collect{'T; y. 'f 'y}]
                    >- 'C['z] } -->
   sequent ['ext] { <H>; x: 'A['s]; <J['x]> >- 'C['x] }

interactive set_split_concl 's (bind{v. 'C['v]}) :
   sequent [squash] { <H> >- isset{'s} } -->
   sequent [squash] { <H>; z: set >- "type"{'C['z]} } -->
   sequent ['ext] { <H>; T: univ[1:l]; f: 'T -> set >- 'C[collect{'T; y. 'f 'y}] } -->
   sequent ['ext] { <H> >- 'C['s] }

doc <:doc< 
   @begin[doc]
   @modsubsection{Combinator equality}
   The induction combinator computes a value of type $T$ if its
   argument $z$ is a set, and the body $b[z, f, g]$ computes a value
   of type $T$, for any type $z @in @univ{1}$, any function
   $f @in z @rightarrow @set$, and a recursive invocation
   $g @in x@colon @univ{1} @rightarrow x @rightarrow T$.
   @end[doc]
>>
interactive set_ind_equality2 {| intro [] |} :
   ["wf"]   sequent [squash] { <H> >- 'z1 = 'z2 in set } -->
   ["main"] sequent [squash] { <H>; a1: univ[1:l]; f1: 'a1 -> set; g1: x: 'a1 -> 'T >-
      'body1['a1; 'f1; 'g1] = 'body2['a1; 'f1; 'g1] in 'T } -->
   sequent ['ext] { <H> >- set_ind{'z1; a1, f1, g1. 'body1['a1; 'f1; 'g1]}
                          = set_ind{'z2; a2, f2, g2. 'body2['a2; 'f2; 'g2]}
                          in 'T }
doc <:doc< @docoff >>

(************************************************************************
 * PRIMITIVES                                                           *
 ************************************************************************)

(*
 * Isset.
 *)
let isset_term = << isset{'s} >>
let isset_opname = opname_of_term isset_term
let is_isset_term = is_dep0_term isset_opname
let mk_isset_term = mk_dep0_term isset_opname
let dest_isset = dest_dep0_term isset_opname

let set_ind_term = << set_ind{'s; T, f, g. 'B['T; 'f; 'g]} >>
let set_ind_opname = opname_of_term set_ind_term
let is_set_ind_term = is_dep0_dep3_term set_ind_opname
let mk_set_ind_term = mk_dep0_dep3_term set_ind_opname
let dest_set_ind = dest_dep0_dep3_term set_ind_opname

(************************************************************************
 * OTHER TACTICS                                                        *
 ************************************************************************)

(*
 * Typehood of isset{'s1}
 *)
let d_isset_typeT =
   rw (addrC [0] unfold_isset) 0 thenT dT 0

let isset_type_term = << "type"{isset{'s1}} >>

let resource intro += (isset_type_term, wrap_intro d_isset_typeT)

(*
 * Equal sets.
 *)
let eqSetT = equal_set

(*
 * Assumption.
 *)
let setAssumT = isset_assum

(*
 * Split a set in a hyp or concl.
 *)
let splitT t i = funT (fun p ->
   if i = 0 then
      let bind = var_subst_to_bind (Sequent.concl p) t in
         set_split_concl t bind
         thenLT [addHiddenLabelT "wf";
                 addHiddenLabelT "wf";
                 addHiddenLabelT "main"]
   else
      let hyp = nth_hyp p i in
      let bind = var_subst_to_bind hyp t in
         set_split_hyp (get_pos_hyp_num p i) t bind
         thenLT [addHiddenLabelT "wf";
                 addHiddenLabelT "wf";
                 addHiddenLabelT "main"])

(************************************************************************
 * AUTOMATION                                                           *
 ************************************************************************)

(*
 * Add set assumptions to trivial tactic.
 *)
let resource auto += {
   auto_name = "setAssumT";
   auto_prec = trivial_prec;
   auto_tac = onSomeHypT setAssumT;
   auto_type = AutoTrivial;
}

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
