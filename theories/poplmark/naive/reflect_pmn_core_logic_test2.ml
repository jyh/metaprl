doc <:doc<
   @module[Reflec_pmn_core_logic_test2]

      Some more lemmas about FSub.

   @begin[license]
   Copyright (C) 2005-2006 Mojave Group, Caltech

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

   Author: Alexei Kopylov @email{kopylov@cs.caltech.edu}
   @end[license]

   @parents
>>

extends itt_hoas_theory
open Basic_tactics
extends reflect_pmn_core_logic
open Basic_tactics
open Itt_equal
open Itt_dfun
open Itt_logic

open Itt_struct
open Itt_unit
open Itt_hoas_bterm_wf
open Itt_hoas_sequent_bterm


let elimReflT elim_rule n =
   assertAtT n <<unit>> taa
   thenT elim_rule n
   thenMT repeatMT (forwardChainT ttca)
   thenT tryT (proofRuleWFT ttca thenT cvar_is_cvar_relax0 ttca)
   thenT tryOnAllHypsT unitElimination



interactive top_is_top:  <:xrule<
  <H1> >- ProvableJudgment {pmn_core_logic{};  $`fsub{| <H> >- fsub_subtype{TyTop; S}  |}} -->
  "wf": <H1> >- IsJudgment {pmn_core_logic{};  $`fsub{| <H> >- fsub_subtype{'T;TyTop}  |}} -->
  "wf": <H1> >- hyp_context {| >- hyplist {| <H> |} |} in CVar{0} -->
  "wf": <H1> >- vbind{| <H> >- 'T |} in BTerm{length{vlist{| <H> |} } } -->
  "wf": <H1> >- vbind{| <H> >- 'S |} in BTerm{length{vlist{| <H> |} } } -->
  <H1> >- ProvableJudgment {pmn_core_logic{};  $`fsub{| <H> >- fsub_subtype{T; S}  |}}
>>
