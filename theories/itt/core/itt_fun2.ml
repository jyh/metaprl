extends Itt_dfun
extends Itt_nat

open Basic_tactics

define unfold_compose : compose{'f;'g} <--> lambda{x.'f ('g 'x)}

interactive_rw reduce_compose {| reduce |}:  (compose{'f;'g} 'x) <--> ('f ('g 'x))

interactive compose_wf3  {| intro [] |}:
   sequent { <H> >- compose{'f;'g} in void -> 'C }

interactive compose_wf  {| intro [intro_typeinf <<'g>>] |} (x:'A -> 'B['x]) :
   [wf] sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- 'g in (x:'A -> 'B['x]) } -->
   sequent { <H>; x:'A >- 'f in 'B['x] -> 'C['x] } -->
   sequent { <H> >- compose{'f;'g} in x:'A -> 'C['x] }

interactive compose_wf2  {| intro [intro_typeinf <<'g>>] |} ('A -> 'B):
   [wf] sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- 'g in 'A -> 'B } -->
   sequent { <H>; x:'A >- 'f in 'B -> 'C } -->
   sequent { <H> >- compose{'f;'g} in 'A -> 'C }

interactive comp_assoc {|  intro [intro_typeinf <<'g>>] |} ('"B"->'"C")  :
   [wf] sequent { <H> >- "type"{'"A"} }  -->
   [wf] sequent { <H> >- "type"{'"B"} }  -->
   [wf] sequent { <H> >- "type"{'"C"} }  -->
   [wf] sequent { <H> >- "type"{'"D"} }  -->
   [wf] sequent { <H> >- '"f" in ('A -> 'B) }  -->
   [wf] sequent { <H> >- '"g" in ('B -> 'C) }  -->
   [wf] sequent { <H> >- '"h" in ('C -> 'D) }  -->
   sequent { <H> >- "equal"{('A -> 'D);"compose"{'"h";"compose"{'"g";'"f"}};"compose"{"compose"{'"h";'"g"};'"f"}} }

define unfold_id: id <--> lambda{x.'x}

interactive_rw id_reduce {| reduce |}: id 'x <--> 'x

interactive id_wf  {| intro [] |} :
   sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- id in 'A -> 'A }

define unfold_funexp :  fun_exp{'f;'n} <--> ind{'n;id; "_" ,F.compose{'F;'f}}

dform funexp_df :  fun_exp{'f;'n} = slot{'f} sup{'n}

interactive_rw funexp_reduce_base {| reduce |} :
   fun_exp{'f;0} <--> id

interactive_rw funexp_reduce_step {| reduce |} :
   ('n in nat) -->
   fun_exp{'f;'n +@ 1} <--> compose{fun_exp{'f;'n};'f}

interactive funexp_wf {| intro[] |}:
   sequent{ <H> >- 'T Type } -->
   sequent{ <H> >- 'f in 'T -> 'T } -->
   sequent{ <H> >- 'n in nat } -->
   sequent{ <H> >- fun_exp{'f;'n} in 'T -> 'T }
