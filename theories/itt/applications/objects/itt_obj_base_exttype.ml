doc <:doc<
   @module[Itt_object_base_exttype]

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

   Author: Alexei Kopylov
   @end[license]
>>

doc <:doc<
   @parents
>>
extends Itt_obj_base_closetype
extends Itt_bisect
extends Itt_union_of
extends Itt_closed_intsect
extends Itt_nat

open Itt_struct
open Itt_logic

open Basic_tactics

let funElimT term n =
   rw (tryC (unfold_all orelseC unfold_implies)) n
   thenT withT term (dT n)
   thenMT (revHypSubstT (-1) 0)
(* TODO:
    1. Should this tactic be in elimination resource?
    2. Should we move additional hyps in the function elim rules lefty?
*)

define unfold_isEObj: isEObj{'T;X.'N['X];'U} <-->
   all X: 'U. { Y: 'U |  ('X isect 'T subtype 'Y & 'Y subtype 'X & 'Y subtype 'N['Y])}

(*
interactive human_definition:
   isEObj{'T;X.'N['X];'U} <=>
   all X: 'U. exst Y: 'U.  ('X isect 'T subtype 'Y & 'Y subtype 'X & 'Y subtype 'N['Y])
*)

interactive isEObj_wf2 {| intro[] |} :
   sequent { <H> >- 'U in closed[l:l] } -->
   sequent { <H> >- 'T in univ[l':l] } -->
   sequent { <H>; X:'U >- 'N['X] in univ[l:l] } -->
   sequent { <H> >- isEObj{'T;X.'N['X];'U} in univ[l':l] }


interactive isEObj_wf {| intro[] |} univ[l:l]:
   sequent { <H> >- "type"{'U} } -->
   sequent { <H>; X:'U >- "type"{'X} } -->
   sequent { <H> >- "type"{'T} } -->
   sequent { <H>; X:'U >- "type"{'N['X]} } -->
   sequent { <H> >- "type"{isEObj{'T;X.'N['X];'U}} }




define unfold_EObj: EObj[l:l]{X.'N['X];'U} <-->
   union_of{{ T:univ[l':l] | isEObj{'T;X.'N['X];'U} }}


interactive wf_EObj2 {| intro[] |} :
   sequent { <H> >- 'U in closed[l:l] } -->
   sequent { <H>; X:'U >- 'N['X] in univ[l:l] } -->
   sequent { <H> >- EObj[l:l]{X.'N['X];'U} in univ[l'':l] }

interactive wf_EObj {| intro[] |} :
   sequent { <H> >- "type"{'U} } -->
   sequent { <H>; X:'U >- "type"{'X} } -->
   sequent { <H>; X:'U >- "type"{'N['X]} } -->
   sequent { <H> >- "type"{EObj[l:l]{X.'N['X];'U}} }


interactive isEObj_elim {| elim [ThinOption thinT] |} 'H 'X:
   sequent { <H>;  isEObj{'T;X.'N['X];'U}; <J> >- 'X in 'U } -->
   sequent { <H>;  isEObj{'T;X.'N['X];'U}; <J>;
             Y:'U; 'X isect 'T subtype 'Y; 'Y subtype 'X; 'Y subtype 'N['Y]  >- 'C } -->
   sequent { <H>;  isEObj{'T;X.'N['X];'U}; <J> >- 'C }



(*
interactive lemma1_human :
   sequent { <H> >- 'U in closed[l:l] } -->
   sequent { <H>; X:'U >- 'N['X] in 'U } -->
   sequent { <H> >- isEObj{'T;X.'N['X];'U} } -->
   sequent { <H> >- exst T':'U. 'T subtype '"T'" & '"T'" subtype 'N['"T'"] }
*)
interactive lemma1  'H univ[l:l]:
   [wf] sequent { <H>;  isEObj{'T;X.'N['X];'U}; <J> >- "type"{'T} } -->
   [wf] sequent { <H>;  isEObj{'T;X.'N['X];'U}; <J> >- 'U in closed[l:l] } -->
   sequent { <H>;  isEObj{'T;X.'N['X];'U}; <J>; T':'U; 'T subtype '"T'"; '"T'" subtype 'N['"T'"] >- 'C } -->
   sequent { <H>;  isEObj{'T;X.'N['X];'U}; <J> >- 'C }

interactive rule1 {| intro[] |} 'U:
   [wf] sequent { <H> >- 'U in closed[l:l] } -->
   [wf] sequent { <H>; X:univ[l:l] >- "type"{'M['X]} } -->
   sequent { <H> >-  'obj in EObj[l:l]{X.'X->'M['X];'U} } -->
   sequent { <H> >- 'obj in Obj[l:l]{X.'M['X]} }

interactive corollary1 {| intro[] |} :
   [wf] sequent { <H> >- 'U in closed[l:l] } -->
   sequent { <H>; X:univ[l:l] >- "type"{'M['X]} } -->
   sequent { <H> >- EObj[l:l]{X.'X->'M['X];'U} subtype Obj[l:l]{X.'M['X]} }


define to_prove_lemma2_we_need: Y{'NN;'X;'I} <--> lambda{n.
   ind{'n;
       lambda{i.'NN 'i 'X};
       "_",Y. lambda{i. 'NN 'i (Isect j:'I. 'Y 'j)}
      }}

interactive_rw y_base {| reduce |}:
   Y{'NN;'X;'I} 0 'i <--> 'NN 'i 'X

interactive_rw y_step {| reduce |}:
   ('n in nat) -->
   Y{'NN;'X;'I} ('n +@ 1) 'i <--> 'NN 'i (Isect j:'I. Y{'NN;'X;'I} 'n 'j)

interactive sublemma2_0 :
   sequent { <H>;
             U : closed[l:l];
             I : univ[l:l];
             all i:'I. semicont[l:l]{X.'N['i;'X];'U};
             T:univ[l':l];
             NN: all i:'I. isEObj{'T;X.'N['i;'X];'U};
             X : 'U;
             i : 'I;
             n : nat
             >- Y{'NN;'X;'I} 'n 'i in 'U
   }


interactive lemma2 {| intro[intro_typeinf <<'U>>] |} <<closed[l:l]>>:
   [wf] sequent { <H> >- 'U in closed[l:l] } -->
   [wf] sequent { <H> >- 'I in univ[l:l] } -->
   [wf] sequent { <H>; i:'I >- semicont[l:l]{X.'N['i;'X];'U} } -->
   sequent { <H> >-  'T in univ[l':l] } -->
   sequent { <H>; i:'I >-  isEObj{'T;X.'N['i;'X];'U} } -->
   sequent { <H> >- isEObj{'T;X.Isect i:'I. 'N['i;'X]; 'U} }


(* Corollary2 : EObj is semicontinius in M *)

interactive rule2 {| intro[] |}:
   [wf] sequent { <H> >- 'U in closed[l:l] } -->
   [wf] sequent { <H> >- 'I in univ[l:l] } -->
   [wf] sequent { <H>; i:'I >- semicont[l:l]{X.'N['i;'X];'U} } -->
   sequent { <H>; i:'I >-  'obj in EObj[l:l]{X.'N['i;'X];'U} } -->
   sequent { <H> >- 'obj in EObj[l:l]{X.Isect i:'I. 'N['i;'X]; 'U} }
