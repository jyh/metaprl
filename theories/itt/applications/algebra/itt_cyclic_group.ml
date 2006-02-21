doc <:doc<
   @module[Itt_cyclic_group]

   This theory defines cyclic groups.

   @docoff
   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 2003-2006 MetaPRL Group, California Institute of Technology

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

doc <:doc< @parents >>
extends Itt_group
extends Itt_int_base
extends Itt_int_ext
extends Itt_int_arith
extends Itt_subset
extends Itt_labels
doc docoff

open Basic_tactics

open Itt_group

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

doc rewrites

define unfold_group_power : group_power{'g; 'a; 'n} <-->
   ind{'n; i, j. ('g^inv 'a) *['g] 'j; .'g^"1"; k, l. 'a *['g] 'l}

define unfold_isCyclic : isCyclic{'g} <-->
   (exst a: 'g^car. all x: 'g^car. exst n: int. ('x = group_power{'g; 'a; 'n} in 'g^car))

define unfold_cycSubg : cycSubg{'g; 'a} <-->
   {car={x: 'g^car| exst n: int. 'x = group_power{'g; 'a; 'n} in 'g^car}; "*"='g^"*"; "1"='g^"1"; inv='g^inv}

define unfold_natpower : natpower{'g; 'a; 'n} <-->
   ind{'n; .'g^"1"; k, l. 'a *['g] 'l}
doc docoff

let resource reduce += [ 
   << group_power{'g; 'a; number[n:n]} >>, wrap_reduce unfold_group_power;
   << natpower{'g; 'a; number[n:n]} >>, wrap_reduce unfold_natpower;
]

let fold_group_power = makeFoldC << group_power{'g; 'a; 'n} >> unfold_group_power
let fold_isCyclic = makeFoldC << isCyclic{'g} >> unfold_isCyclic
let fold_cycSubg = makeFoldC << cycSubg{'g; 'a} >> unfold_cycSubg
let fold_natpower = makeFoldC << natpower{'g; 'a; 'n} >> unfold_natpower

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform group_power_df1 : except_mode[src] :: except_mode[prl] :: parens :: "prec"[prec_inv] :: group_power{'G; 'a; 'n} =
   slot["le"]{'a} sup{'n} sub{'G}

dform group_power_df2 : mode[prl] :: parens :: "prec"[prec_inv] :: group_power{'G; 'a; 'n} =
(*   `"(" slot{'a} `"^" slot{'n} `")" sub{'G}*)
   slot["le"]{'a} sup{'n} sub{'G}

dform natpower_df1 : except_mode[src] :: except_mode[prl] :: parens :: "prec"[prec_inv] :: natpower{'G; 'a; 'n} =
   slot["le"]{'a} sup{'n} sub{'G}

dform natpower_df2 : mode[prl] :: parens :: "prec"[prec_inv] :: natpower{'G; 'a; 'n} =
   slot["le"]{'a} sup{'n} sub{'G}

dform isCyclic_df : except_mode[src] :: isCyclic{'G} =
   `"isCyclic(" slot{'G} `")"

dform cycSubg_df : except_mode[src] :: cycSubg{'G; 'a} =
   `"Cyclic_subgroup(" slot{'G} `"; " slot{'a} `")"

(************************************************************************
 * REDUCTIONS                                                           *
 ************************************************************************)

interactive_rw reduce_group_power_0 {| reduce |} :
   group_power{'g; 'a; 0} <--> ('g^"1")

interactive_rw reduce_natpower_0 {| reduce |} :
   natpower{'g; 'a; 0} <--> ('g^"1")

interactive_rw natpower_group_power :
   ('n in nat) -->
   natpower{'g; 'a; 'n} <--> group_power{'g; 'a; 'n}

let natpowerC = natpower_group_power

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc<
   @modsection{Rules}
   @modsubsection{Group power operation}

   Well-formedness.
>>
interactive natpower_wf {| intro [] |} :
   [wf] sequent { <H> >- 'a in 'g^car } -->
   [wf] sequent { <H> >- 'n in nat } -->
   [wf] sequent { <H>; x: 'g^car; y: 'g^car >- 'x *['g] 'y in 'g^car } -->
   [wf] sequent { <H> >- 'g^"1" in 'g^car } -->
   sequent { <H> >- natpower{'g; 'a; 'n} in 'g^car }

interactive group_power_wf {| intro [] |} :
   [wf] sequent { <H> >- 'a in 'g^car } -->
   [wf] sequent { <H> >- 'n in int } -->
   [wf] sequent { <H>; x: 'g^car; y: 'g^car >- 'x *['g] 'y in 'g^car } -->
   [wf] sequent { <H>; x: 'g^car >- 'g^inv 'x in 'g^car } -->
   [wf] sequent { <H> >- 'g^"1" in 'g^car } -->
   sequent { <H> >- group_power{'g; 'a; 'n} in 'g^car }
doc docoff

(* a ^ 0 = e *)
interactive group_power_0 {| intro [intro_typeinf <<'g>>] |} group[i:l] :
   [wf] sequent { <H> >- 'g in group[i:l] } -->
   [wf] sequent { <H> >- 'a in 'g^car } -->
   sequent { <H> >- group_power{'g; 'a; 0} = 'g^"1" in 'g^car }

(* a ^ 1 = a *)
interactive group_power_1 {| intro [intro_typeinf <<'g>>] |} group[i:l] :
   [wf] sequent { <H> >- 'g in group[i:l] } -->
   [wf] sequent { <H> >- 'a in 'g^car } -->
   sequent { <H> >- group_power{'g; 'a; 1} = 'a in 'g^car }

(* a ^ (n + 1) * a ^ (-1) = a ^ n *)
interactive group_power_less {| intro [intro_typeinf <<'g>>] |} group[i:l] :
   [wf] sequent { <H> >- 'g in group[i:l] } -->
   [wf] sequent { <H> >- 'a in 'g^car } -->
   [wf] sequent { <H> >- 'n in int } -->
   sequent { <H> >- group_power{'g; 'a; ('n +@ 1)} *['g] ('g^inv 'a) = group_power{'g; 'a; 'n} in 'g^car }

(* a ^ n * x = a ^ (n + 1) *)
interactive group_power_more {| intro [intro_typeinf <<'g>>] |} group[i:l] :
   [wf] sequent { <H> >- 'g in group[i:l] } -->
   [wf] sequent { <H> >- 'a in 'g^car } -->
   [wf] sequent { <H> >- 'n in int } -->
   sequent { <H> >- group_power{'g; 'a; 'n} *['g] 'a = group_power{'g; 'a; ('n +@ 1)} in 'g^car }

doc <:doc<

   Power reduction 1: $a^m * a^n = a^{m + n}$
>>
interactive group_power_reduce {| intro [intro_typeinf <<'g>>] |} group[i:l] :
   [wf] sequent { <H> >- 'g in group[i:l] } -->
   [wf] sequent { <H> >- 'a in 'g^car } -->
   [wf] sequent { <H> >- 'm in int } -->
   [wf] sequent { <H> >- 'n in int } -->
   sequent { <H> >- group_power{'g; 'a; 'm} *['g] group_power{'g; 'a; 'n} = group_power{'g; 'a; ('m +@ 'n)} in 'g^car }
doc docoff

interactive group_power_inv_reduce {| intro [intro_typeinf <<'g>>] |} group[i:l] :
   [wf] sequent { <H> >- 'g in group[i:l] } -->
   [wf] sequent { <H> >- 'a in 'g^car } -->
   [wf] sequent { <H> >- 'n in int } -->
   sequent { <H> >- 'g^inv group_power{'g; 'a; 'n} = group_power{'g; 'a; (-'n)} in 'g^car }

doc <:doc<

   Power reduction 2: $(a^m)^n = a^{m * n}$
>>
interactive group_power_power_reduce {| intro [intro_typeinf <<'g>>] |} group[i:l] :
   [wf] sequent { <H> >- 'g in group[i:l] } -->
   [wf] sequent { <H> >- 'a in 'g^car } -->
   [wf] sequent { <H> >- 'm in int } -->
   [wf] sequent { <H> >- 'n in int } -->
   sequent { <H> >- group_power{'g; group_power{'g; 'a; 'm}; 'n} = group_power{'g; 'a; ('m *@ 'n)} in 'g^car }

doc <:doc<

   If $s$ is a subgroup of $g$, the power operation on $s$ is the same as
   that on $g$.
>>
interactive subgroup_power {| intro [AutoMustComplete; intro_typeinf <<'g>>] |} group[i:l] :
   [main] sequent { <H> >- subgroup[i:l]{'s; 'g} } -->
   [wf] sequent { <H> >- 'a in 's^car } -->
   [wf] sequent { <H> >- 'n in int } -->
   sequent { <H> >- group_power{'g; 'a; 'n} = group_power{'s; 'a; 'n} in 's^car }

doc <:doc<
   @modsubsection{Cyclic group}

>>
interactive isCyclic_type {| intro [intro_typeinf <<'g>>]; nth_hyp |} group[i:l] :
   [wf] sequent { <H> >- 'g in group[i:l] } -->
   sequent { <H> >- "type"{isCyclic{'g}} }

interactive isCyclic_intro {| intro [intro_typeinf <<'g>>] |} group[i:l] 'a :
   [wf] sequent { <H> >- 'g in group[i:l] } -->
   [wf] sequent { <H> >- 'a in 'g^car } -->
   sequent { <H>; x: 'g^car >- exst n: int. 'x = group_power{'g; 'a; 'n} in 'g^car } -->
   sequent { <H> >- isCyclic{'g} }

interactive isCyclic_elim {| elim [elim_typeinf <<'g>>] |} 'H group[i:l] :
   [wf] sequent { <H>; x: isCyclic{'g}; <J['x]> >- 'g in group[i:l] } -->
   [main] sequent { <H>; x: isCyclic{'g}; <J['x]>; a: 'g^car; b: all x: 'g^car. exst n: int. ('x = group_power{'g; 'a; 'n} in 'g^car) >- 'C['x] } -->
   sequent { <H>; x: isCyclic{'g}; <J['x]> >- 'C['x] }

doc <:doc<

   Every cyclic group is abelian.
>>
interactive isCyclic_commutative group[i:l] :
   [wf] sequent { <H> >- 'g in group[i:l] } -->
   [main] sequent { <H> >- isCyclic{'g} } -->
   sequent { <H> >- isCommutative{'g} }

interactive isCyclic_abelian :
   [wf] sequent { <H> >- 'g in group[i:l] } -->
   [main] sequent { <H> >- isCyclic{'g} } -->
   sequent { <H> >- 'g in abelg[i:l] }
doc docoff

doc <:doc<

   Every non-trivial subgroup of a cyclic group is cyclic.
>>
interactive subg_isCyclic group[i:l] 'g :
   [main] sequent { <H> >- isCyclic{'g} } -->
   [main] sequent { <H> >- subgroup[i:l]{'s; 'g} } -->
   [main] sequent { <H> >- exst x: 's^car. not {('x = 's^"1" in 's^car)} } -->
   [decidable] sequent { <H>; a: int; x: 'g^car >- decidable{(group_power{'g; 'x; 'a} in 's^car subset 'g^car)} } -->
   sequent { <H> >- isCyclic{'s} }

doc <:doc<
   @modsubsection{Cyclic subgroup}

>>
interactive cycSubg_intro {| intro [] |} :
   [wf] sequent { <H> >- 'g in group[i:l] } -->
   [wf] sequent { <H> >- 'a in 'g^car } -->
   sequent { <H> >- cycSubg{'g; 'a} in group[i:l] }

doc <:doc<

   A cyclic subgroup is a subgroup.
>>
interactive cycSubg_subgroup {| intro [] |} :
   [wf] sequent { <H> >- 'g in group[i:l] } -->
   [wf] sequent { <H> >- 'a in 'g^car } -->
   sequent { <H> >- subgroup[i:l]{cycSubg{'g; 'a}; 'g} }

interactive cycSubg_car {| intro [AutoMustComplete] |} :
   [wf] sequent { <H> >- 'g in group[i:l] } -->
   [wf] sequent { <H> >- 'a in 'g^car } -->
   sequent { <H> >- cycSubg{'g; 'a}^car = {x: 'g^car| exst n: int. 'x = group_power{'g; 'a; 'n} in 'g^car} in univ[i:l] }

interactive cycSubg_op {| intro [AutoMustComplete; intro_typeinf <<'g>>] |} group[i:l] :
   [wf] sequent { <H> >- 'g in group[i:l] } -->
   [wf] sequent { <H> >- 'a in 'g^car } -->
   sequent { <H> >- cycSubg{'g; 'a}^"*" = 'g^"*" in cycSubg{'g; 'a}^car -> cycSubg{'g; 'a}^car -> cycSubg{'g; 'a}^car }

interactive cycSubg_id {| intro [AutoMustComplete; intro_typeinf <<'g>>] |} group[i:l] :
   [wf] sequent { <H> >- 'g in group[i:l] } -->
   [wf] sequent { <H> >- 'a in 'g^car } -->
   sequent { <H> >- cycSubg{'g; 'a}^"1" = 'g^"1" in cycSubg{'g; 'a}^car }

interactive cycSubg_inv {| intro [AutoMustComplete; intro_typeinf <<'g>>] |} group[i:l] :
   [wf] sequent { <H> >- 'g in group[i:l] } -->
   [wf] sequent { <H> >- 'a in 'g^car } -->
   sequent { <H> >- cycSubg{'g; 'a}^inv = 'g^inv in cycSubg{'g; 'a}^car -> cycSubg{'g; 'a}^car }

doc docoff

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
