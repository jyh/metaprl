doc <:doc< 
   @spelling{groupoid semigroup}
   @begin[doc]
   @module[Itt_grouplikeobj]
  
   This theory defines group-like objects: groupoid, semigroup,
   and monoid.
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
  
   Author: Xin Yu @email{xiny@cs.caltech.edu}
   @end[license]
>>

doc <:doc< @doc{@parents} >>
extends Itt_record
extends Itt_set
extends Itt_subset
extends Itt_fun
extends Itt_disect
doc docoff

open Printf
open Mp_debug
open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermAddr
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.Refine
open Refiner.Refiner.RefineError
open Mp_resource
open Simple_print

open Tactic_type
open Tactic_type.Tacticals
open Tactic_type.Sequent
open Tactic_type.Conversionals
open Mptop
open Var

open Dtactic
open Auto_tactic

open Itt_struct
open Itt_record
open Itt_fun
open Itt_logic
open Itt_int_ext
open Itt_subtype
open Itt_subset
open Itt_squash

let _ =
   show_loading "Loading Itt_grouplikeobj%t"

(************************************************************************
 * GROUPOID                                                             *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @modsection{Groupoid}
   @modsubsection{Rewrites}
  
   @end[doc]
>>
define unfold_groupoid : groupoid[i:l] <-->
   {car: univ[i:l]; "*": ^car -> ^car -> ^car}
doc docoff

let fold_groupoid = makeFoldC << groupoid[i:l] >> unfold_groupoid

let groupoidDT n = rw unfold_groupoid n thenT dT n

let resource elim +=
   [<<groupoid[i:l]>>, groupoidDT]

doc <:doc< 
   @begin[doc]
   @modsubsection{Well-formedness}
  
   @end[doc]
>>
interactive groupoid_wf {| intro [] |} :
   sequent { <H> >- "type"{groupoid[i:l]} }

doc <:doc< 
   @begin[doc]
   @modsubsection{Introduction and Elimination}
  
   @end[doc]
>>
interactive groupoid_intro {| intro [AutoMustComplete] |} :
   sequent { <H> >- 'g in {car: univ[i:l]; "*": ^car -> ^car -> ^car} } -->
   sequent { <H> >- 'g in groupoid[i:l] }

(*interactive groupoid_elim {| elim [] |} 'H :
   sequent { <H>; g: {car: univ[i:l]; "*": ^car -> ^car -> ^car}; <J['g]> >- 'C['g] } -->
   sequent { <H>; g: groupoid[i:l]; <J['g]> >- 'C['g] }
*)

(************************************************************************
 * SEMIGROUP                                                            *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @modsection{Semigroup}
   @modsubsection{Rewrites}
  
   @end[doc]
>>
define unfold_isSemigroup : isSemigroup{'g} <-->
   all x: 'g^car. all y: 'g^car. all z: 'g^car. (('x *['g] 'y) *['g] 'z = 'x *['g] ('y *['g] 'z) in 'g^car)

define unfold_semigroup1 : semigroup[i:l] <-->
   {g: groupoid[i:l] | isSemigroup{'g}}
doc docoff

let unfold_semigroup = unfold_semigroup1 thenC addrC [0] unfold_groupoid thenC addrC [1] unfold_isSemigroup

let fold_isSemigroup = makeFoldC << isSemigroup{'g} >> unfold_isSemigroup
let fold_semigroup1 = makeFoldC << semigroup[i:l] >> unfold_semigroup1
let fold_semigroup = makeFoldC << semigroup[i:l] >> unfold_semigroup

let semigroupDT n = rw unfold_semigroup n thenT dT n

let resource elim +=
   [<<semigroup[i:l]>>, semigroupDT]

doc <:doc< 
   @begin[doc]
   @modsubsection{Well-formedness}
  
   @end[doc]
>>

interactive isSemigroup_wf {| intro [] |} :
   sequent { <H> >- "type"{'A^car} } -->
   sequent { <H>; x: 'A^car; y: 'A^car >- 'x *['A] 'y in 'A^car} -->
   sequent { <H> >- "type"{isSemigroup{'A}} }

interactive semigroup_wf {| intro [] |} :
   sequent { <H> >- "type"{semigroup[i:l]} }

doc <:doc< 
   @begin[doc]
   @modsubsection{Introduction and Elimination}
  
   @end[doc]
>>
interactive isSemigroup_intro {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- "type"{.'g^car} } -->
   [main] sequent { <H>; x: 'g^car; y: 'g^car; z: 'g^car >- ('x *['g] 'y) *['g] 'z = 'x *['g] ('y *['g] 'z) in 'g^car } -->
   sequent { <H> >- isSemigroup{'g} }

interactive isSemigroup_elim {| elim [] |} 'H :
   sequent { <H>; u: all x: 'g^car. all y: 'g^car. all z: 'g^car. (('x *['g] 'y) *['g] 'z = 'x *['g] ('y *['g] 'z) in 'g^car); <J['u]> >- 'C['u] } -->
   sequent { <H>; u: isSemigroup{'g}; <J['u]> >- 'C['u] }

interactive semigroup_intro {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- 'g in groupoid[i:l] } -->
   [main] sequent { <H> >- isSemigroup{'g} } -->
   sequent { <H> >- 'g in semigroup[i:l] }

interactive semigroup_elim {| elim [] |} 'H :
   sequent { <H>; g: {car: univ[i:l]; "*": ^car -> ^car -> ^car}; u: all x: 'g^car. all y: 'g^car. all z: 'g^car. (('x *['g] 'y) *['g] 'z = 'x *['g] ('y *['g] 'z) in 'g^car); <J['g]> >- 'C['g] } -->
   sequent { <H>; g: semigroup[i:l]; <J['g]> >- 'C['g] }

doc <:doc< 
   @begin[doc]
   @modsubsection{Hierarchy}
  
   @end[doc]
>>
interactive semigrp_subtype_grpoid :
   sequent { <H> >- semigroup[i:l] subtype groupoid[i:l] }

(************************************************************************
 * MONOID                                                               *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @modsection{Monoid}
   @modsubsection{Rewrites}
  
   @end[doc]
>>
define unfold_premonoid1 : premonoid[i:l] <-->
   record["1":t]{r. 'r^car; groupoid[i:l]}

define unfold_isMonoid1 : isMonoid{'g} <-->
   isSemigroup{'g} & all x: 'g^car. ('g^"1" *['g] 'x = 'x  in 'g^car & 'x *['g] 'g^"1" = 'x in 'g^car )

define unfold_monoid1 : monoid[i:l] <-->
   {g: premonoid[i:l] | isMonoid{'g}}
doc docoff

let unfold_premonoid = unfold_premonoid1 thenC addrC [1] unfold_groupoid
let unfold_isMonoid = unfold_isMonoid1 thenC addrC [0] unfold_isSemigroup
let unfold_monoid = unfold_monoid1 thenC addrC [0] unfold_premonoid thenC addrC [1] unfold_isMonoid

let fold_premonoid1 = makeFoldC << premonoid[i:l] >> unfold_premonoid1
let fold_premonoid = makeFoldC << premonoid[i:l] >> unfold_premonoid
let fold_isMonoid1 = makeFoldC << isMonoid{'g} >> unfold_isMonoid1
let fold_isMonoid = makeFoldC << isMonoid{'g} >> unfold_isMonoid
let fold_monoid1 = makeFoldC << monoid[i:l] >> unfold_monoid1
let fold_monoid = makeFoldC << monoid[i:l] >> unfold_monoid

let monoidDT n = rw unfold_monoid n thenT dT n

let resource elim +=
   [<<monoid[i:l]>>, monoidDT]

doc <:doc< 
   @begin[doc]
   @modsubsection{Well-formedness}
  
   @end[doc]
>>
interactive premonoid_wf {| intro [] |} :
   sequent { <H> >- "type"{premonoid[i:l]} }

interactive isMonoid_wf {| intro [] |} :
   sequent { <H> >- "type"{'A^car} } -->
   sequent { <H>; x: 'A^car; y: 'A^car >- 'x *['A] 'y in 'A^car} -->
   sequent { <H> >- 'A^"1" in 'A^car} -->
   sequent { <H> >- "type"{isMonoid{'A}} }

interactive monoid_wf {| intro [] |} :
   sequent { <H> >- "type"{monoid[i:l]} }

doc <:doc< 
   @begin[doc]
   @modsubsection{Introduction and Elimination}
  
   @end[doc]
>>
interactive premonoid_intro {| intro [AutoMustComplete] |} :
   sequent { <H> >- 'g in {car: univ[i:l]; "*": ^car -> ^car -> ^car; "1": ^car} } -->
   sequent { <H> >- 'g in premonoid[i:l] }

interactive premonoid_elim {| elim [] |} 'H :
   sequent { <H>; g: {car: univ[i:l]; "*": ^car -> ^car -> ^car; "1": ^car}; <J['g]> >- 'C['g] } -->
   sequent { <H>; g: premonoid[i:l]; <J['g]> >- 'C['g] }

interactive isMonoid_intro {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- "type"{.'g^car} } -->
   [main] sequent { <H> >- isSemigroup{'g} } -->
   [main] sequent { <H>; x: 'g^car >- 'g^"1" *['g] 'x = 'x in 'g^car } -->
   [main] sequent { <H>; x: 'g^car >- 'x *['g] 'g^"1" = 'x in 'g^car } -->
   sequent { <H> >- isMonoid{'g} }

interactive isMonoid_elim {| elim [] |} 'H :
   sequent { <H>; u: isMonoid{'g}; v: all x: 'g^car. all y: 'g^car. all z: 'g^car. (('x *['g] 'y) *['g] 'z = 'x *['g] ('y *['g] 'z) in 'g^car); w: all x: 'g^car. (('g^"1" *['g] 'x = 'x in 'g^car) & ('x *['g] 'g^"1" = 'x in 'g^car)); <J['u]> >- 'C['u] } -->
   sequent { <H>; u: isMonoid{'g}; <J['u]> >- 'C['u] }

interactive monoid_intro {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- 'g in premonoid[i:l] } -->
   [main] sequent { <H> >- isMonoid{'g} } -->
   sequent { <H> >- 'g in monoid[i:l] }

interactive monoid_elim {| elim [] |} 'H :
   sequent { <H>; g: {car: univ[i:l]; "*": ^car -> ^car -> ^car; "1": ^car}; u: all x: 'g^car. all y: 'g^car. all z: 'g^car. (('x *['g] 'y) *['g] 'z = 'x *['g] ('y *['g] 'z) in 'g^car); v: all x: 'g^car. ('g^"1" *['g] 'x = 'x in 'g^car & 'x *['g] 'g^"1" = 'x in 'g^car); <J['g]> >- 'C['g] } -->
   sequent { <H>; g: monoid[i:l]; <J['g]> >- 'C['g] }

doc <:doc< 
   @begin[doc]
   @modsubsection{Hierarchy}
  
   @end[doc]
>>
interactive monoid_subtype_semigrp :
   sequent { <H> >- monoid[i:l] subtype semigroup[i:l] }

(************************************************************************
 * BINARY OPERATION IS COMMUTATIVE                                      *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @modsection{Commutative Operation}
   @modsubsection{Rewrites}
  
   @end[doc]
>>
define unfold_isCommutative : isCommutative{'g} <-->
   all x: 'g^car. all y: 'g^car. ('x *['g] 'y = 'y *['g] 'x in 'g^car)

define unfold_csemigroup : csemigroup[i:l] <-->
   {g: semigroup[i:l] | isCommutative{'g}}

define unfold_cmonoid : cmonoid[i:l] <-->
   {g: monoid[i:l] | isCommutative{'g}}
doc docoff

let fold_isCommutative = makeFoldC << isCommutative{'g} >> unfold_isCommutative
let fold_csemigroup = makeFoldC << csemigroup[i:l] >> unfold_csemigroup
let fold_cmonoid = makeFoldC << cmonoid[i:l] >> unfold_cmonoid

let csemigroupDT n = rw unfold_csemigroup n thenT dT n
let cmonoidDT n = rw unfold_cmonoid n thenT dT n

let resource elim +=
   [<<csemigroup[i:l]>>, csemigroupDT;
    <<cmonoid[i:l]>>, cmonoidDT
   ]

doc <:doc< 
   @begin[doc]
   @modsubsection{Well-formedness}
  
   @end[doc]
>>
interactive isComutative_wf {| intro [] |} :
   sequent { <H> >- "type"{'A^car} } -->
   sequent { <H>; x: 'A^car; y: 'A^car >- 'x *['A] 'y in 'A^car} -->
   sequent { <H> >- "type"{isCommutative{'A}} }

interactive csemigroup_wf {| intro [] |} :
   sequent { <H> >- "type"{csemigroup[i:l]} }

interactive cmonoid_wf {| intro [] |} :
   sequent { <H> >- "type"{cmonoid[i:l]} }

doc <:doc< 
   @begin[doc]
   @modsubsection{Introduction and Elimination}
  
   @end[doc]
>>
interactive isCommutative_intro {| intro [] |} :
   [wf] sequent { <H> >- "type"{.'g^car} } -->
   [main] sequent { <H>; x: 'g^car; y: 'g^car >- ('x *['g] 'y = 'y *['g] 'x in 'g^car) } -->
   sequent { <H> >- isCommutative{'g} }

interactive isCommutative_elim {| elim [] |} 'H :
   sequent { <H>; u: isCommutative{'g}; v: all x: 'g^car. all y: 'g^car. ('x *['g] 'y = 'y *['g] 'x in 'g^car); <J['u]> >- 'C['u] } -->
   sequent { <H>; u: isCommutative{'g}; <J['u]> >- 'C['u] }

interactive csemigroup_intro {| intro [] |} :
   [wf] sequent { <H> >- 'g in semigroup[i:l] } -->
   [main] sequent { <H> >- isCommutative{'g} } -->
   sequent { <H> >- 'g in csemigroup[i:l] }

interactive csemigroup_elim {| elim [] |} 'H :
   sequent { <H>; g: semigroup[i:l]; x: isCommutative{'g}; <J['g]> >- 'C['g] } -->
   sequent { <H>; g: csemigroup[i:l]; <J['g]> >- 'C['g] }

interactive cmonoid_intro {| intro [] |} :
   [wf] sequent { <H> >- 'g in monoid[i:l] } -->
   [main] sequent { <H> >- isCommutative{'g} } -->
   sequent { <H> >- 'g in cmonoid[i:l] }

interactive cmonoid_elim {| elim [] |} 'H :
   sequent { <H>; g: monoid[i:l]; x: isCommutative{'g}; <J['g]> >- 'C['g] } -->
   sequent { <H>; g: cmonoid[i:l]; <J['g]> >- 'C['g] }

doc <:doc< 
   @begin[doc]
   @modsubsection{Hierarchy}
  
   @end[doc]
>>
interactive csemigrp_subtype_semigrp :
   sequent { <H> >- csemigroup[i:l] subtype semigroup[i:l] }

interactive cmonoid_subtype_monoid :
   sequent { <H> >- cmonoid[i:l] subtype monoid[i:l] }

(************************************************************************
 * SUBSTRUCTURE                                                         *
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @modsection{Substructure}
   @modsubsection{Rewrites}
  
   @end[doc]
>>
define unfold_subStructure : subStructure{'s; 'g} <-->
   ('s^car subset 'g^car) & ('g^"*" = 's^"*" in 's^car -> 's^car -> 's^car)
doc docoff

let fold_subStructure = makeFoldC << subStructure{'s; 'g} >> unfold_subStructure

doc <:doc< 
   @begin[doc]
   @modsubsection{Well-formedness}
  
   @end[doc]
>>
interactive subStructure_wf {| intro [] |} :
   sequent { <H> >- "type"{'A^car} } -->
   sequent { <H> >- "type"{'B^car} } -->
   sequent { <H> >- 'B^"*" = 'A^"*" in 'A^car -> 'A^car -> 'A^car } -->
   sequent { <H> >- "type"{subStructure{'A; 'B}} }

doc <:doc< 
   @begin[doc]
   @modsubsection{Introduction and Elimination}
  
   @end[doc]
>>
interactive subStructure_intro {| intro [] |} :
   [wf] sequent { <H> >- 'g^"*" = 's^"*" in 's^car -> 's^car -> 's^car } -->
   [main] sequent { <H> >- 's^car subset 'g^car } -->
   sequent { <H> >- subStructure{'s; 'g} }

interactive subStructure_elim {| elim [] |} 'H :
   sequent { <H>; u: subStructure{'s; 'g}; x: 's^car subset 'g^car; v: 'g^"*" = 's^"*" in 's^car -> 's^car -> 's^car; <J['u]> >- 'C['u] } -->
   sequent { <H>; u: subStructure{'s; 'g}; <J['u]> >- 'C['u] }

doc <:doc< 
   @begin[doc]
   @modsubsection{Rules}
  
   Substructure is squash-stable.
   @end[doc]
>>
interactive subStructure_sqStable {| squash |} :
   [wf] sequent { <H> >- squash{subStructure{'s; 'g}} } -->
   sequent { <H> >- subStructure{'s; 'g} }
doc docoff

interactive subStructure_type_right 'B :
   sequent { <H> >- subStructure{'A; 'B} } -->
   sequent { <H> >- "type"{'A^car} }

interactive subStructure_type_left 'A :
   sequent { <H> >- subStructure{'A; 'B} } -->
   sequent { <H> >- "type"{'B^car} }

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

prec prec_mul

dform groupoid_df1 : except_mode[src] :: except_mode[prl] :: groupoid[i:l] =
   mathbbG `"roupoid" sub{slot[i:l]}

dform groupoid_df2 : mode[prl] :: groupoid[i:l] =
   `"Groupoid[" slot[i:l] `"]"

dform semigroup_df1 : except_mode[src] :: except_mode[prl] :: semigroup[i:l] =
   mathbbS `"emigroup" sub{slot[i:l]}

dform semigroup_df2 : mode[prl] :: semigroup[i:l] =
   `"Semigroup[" slot[i:l] `"]"

dform monoid_df1 : except_mode[src] :: except_mode[prl] :: monoid[i:l] =
   mathbbM `"onoid" sub{slot[i:l]}

dform monoid_df2 : mode[prl] :: monoid[i:l] =
   `"Monoid[" slot[i:l] `"]"

dform premonoid_df1 : except_mode[src] :: except_mode[prl] :: premonoid[i:l] =
   `"premonoid" sub{slot[i:l]}

dform premonoid_df2 : mode[prl] :: premonoid[i:l] =
   `"premonoid[" slot[i:l] `"]"

dform isSemigroup_df : except_mode[src] :: isSemigroup{'g} =
   `"isSemigroup(" slot{'g} `")"

dform isMonoid_df : except_mode[src] :: isMonoid{'g} =
   `"isMonoid(" slot{'g} `")"

dform car_df1 : except_mode[src] :: except_mode[prl] :: ('g^car) =
   `"car" sub{'g}

dform car_df2 : mode[prl] :: ('g^car) =
   slot{'g} `".car"

dform mul_df1 : except_mode[src] :: except_mode[prl] :: parens :: "prec"[prec_mul] :: ('g^"*" 'a 'b) =
   slot{'a} `"*" sub{'g} slot{'b}

dform mul_df2 : mode[prl] :: parens :: "prec"[prec_mul] :: ('g^"*" 'a 'b) =
   slot["lt"]{'a} `" " slot{'g} `".* " slot["le"]{'b}

dform id_df1 : except_mode[src] :: except_mode[prl] :: ('g^"1") =
   1 sub{'g}

dform id_df2 : mode[prl] :: ('g^"1") =
   slot{'g} `".1"

dform isCommutative_df : except_mode[src] :: isCommutative{'g} =
   `"isCommutative(" slot{'g} `")"

dform csemigroup_df1 : except_mode[src] :: except_mode[prl] :: csemigroup[i:l] =
   `"Commutative_semigroup" sub{slot[i:l]}

dform csemigroup_df2 : mode[prl] :: csemigroup[i:l] =
   `"Commutative_semigroup[" slot[i:l] `"]"

dform cmonoid_df1 : except_mode[src] :: except_mode[prl] :: cmonoid[i:l] =
   `"Commutative_monoid" sub{slot[i:l]}

dform monoid_df2 : mode[prl] :: cmonoid[i:l] =
   `"Commutative_monoid[" slot[i:l] `"]"

dform subStructure_df1 : except_mode[src] :: except_mode[prl] :: parens :: "prec"[prec_subtype] :: subStructure{'s; 'g} =
   slot{'s} `" " subseteq sub["str":s] `" " slot{'g}

dform subStructure_df2 : mode[prl] :: parens :: "prec"[prec_subtype] :: subStructure{'s; 'g} =
   slot{'s} `" " subseteq `"(str) " slot{'g}

(************************************************************************
 * TYPE INFERENCE                                                       *
 ************************************************************************)

let inf_id _ _ _ eqs opt_eqs defs t =
   let t, _ = dest_field t in
   let car = mk_field_term t "car" in
      eqs, opt_eqs, defs, car

let inf_inv _ _ _ eqs opt_eqs defs t =
   let t, _ = dest_field t in
   let car = mk_field_term t "car" in
      eqs, opt_eqs, defs, mk_fun_term car car

let inf_mul _ _ _ eqs opt_eqs defs t =
   let t, _ = dest_field t in
   let car = mk_field_term t "car" in
      eqs, opt_eqs, defs, mk_fun_term car (mk_fun_term car car)

let resource typeinf += [
   <<'g^"1">>, inf_id;
   <<'g^"inv">>, inf_inv;
   <<'g^"*">>, inf_mul
]

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
