extends Itt_fun
extends Itt_nat

open Dtactic

define unfold_compose : compose{'f;'g} <--> lambda{x.'f ('g 'x)}

interactive_rw reduce_compose :  (compose{'f;'g} 'x) <--> ('f ('g 'x))

interactive compose_wf  {| intro [intro_typeinf <<'g>>] |} (x:'A -> 'B['x]) :
   sequent { <H> >- 'g in (x:'A -> 'B['x]) } -->
   sequent { <H>; x:'A >- 'f in 'B['x] -> 'C['x] } -->
   sequent { <H> >- compose{'f;'g} in x:'A -> 'C['x] }

interactive compose_wf2  {| intro [intro_typeinf <<'g>>] |} (x:'A -> 'B):
   sequent { <H> >- 'g in 'A -> 'B } -->
   sequent { <H>; x:'A >- 'f in 'B -> 'C } -->
   sequent { <H> >- compose{'f;'g} in 'A -> 'C }

interactive comp_assoc {|  intro [intro_typeinf <<'g>>] |} ('"B"->'"C")  :
   [wf] sequent { <H> >- "type"{'"A"} }  -->
   [wf] sequent { <H> >- "type"{'"B"} }  -->
   [wf] sequent { <H> >- "type"{'"C"} }  -->
   [wf] sequent { <H> >- "type"{'"D"} }  -->
   [wf] sequent { <H> >- '"f" in "fun"[]{'"A";'"B"} }  -->
   [wf] sequent { <H> >- '"g" in "fun"[]{'"B";'"C"} }  -->
   [wf] sequent { <H> >- '"h" in "fun"[]{'"C";'"D"} }  -->
   sequent { <H> >- "equal"[]{"fun"[]{'"A";"".'"D"};"compose"[]{'"h";"compose"[]{'"g";'"f"}};"compose"[]{"compose"[]{'"h";'"g"};'"f"}} }

define unfold_id: id <--> lambda{x.'x}

define unfold_funexp :  fun_exp{'f;'n} <--> ind{'n;id; "_" ,F.compose{'F;'f}}

