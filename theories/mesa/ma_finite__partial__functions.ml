extends Nuprl_finite__partial__functions

open Dtactic
open Top_conversionals
open Mp_resource

interactive nuprl_fpf_single_wf  {| intro [] |}:
   [wf] sequent  { <Gamma> >- "type"{'"A"} }  -->
   [wf] sequent  { <Gamma>; x:'A >- "type"{'B['x]} }  -->
   [wf] sequent  { <Gamma> >- '"x" in '"A" }  -->
   [wf] sequent  { <Gamma> >- '"v" in '"B"['"x"] }  -->
   sequent  { <Gamma> >- ("fpf-single"[]{'"x";'"v"} in "fpf"[]{'"A";"x".'"B"['"x"]}) }


interactive nuprl_fpf_join_wf    {| intro [] |}  :
   [wf] sequent  { <Gamma> >- "type"{'"A"} }  -->
   [wf] sequent  { <Gamma>; x:'A >- "type"{'B['x]} }  -->
   [wf] sequent  { <Gamma> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent  { <Gamma> >- '"g" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent  { <Gamma> >- '"eq" in "deq"[]{'"A"} }  -->
   sequent  { <Gamma> >- ("fpf-join"[]{'"eq";'"f";'"g"} in "fpf"[]{'"A";"a".'"B"['"a"]}) }



interactive_rw nuprl_fpf_ap_single_rw {| reduce |}  :
  "fpf-ap"[]{"fpf-single"[]{'"x";'"v"};'"eq";'"x"} <--> '"v"

interactive_rw nuprl_fpf_cap_single1_rw  'A :
   ('"eq" in "deq"[]{'"A"}  ) -->
   ('"x" in '"A" )  -->
   "fpf-cap"[]{"fpf-single"[]{'"x";'"v"};'"eq";'"x";'"z"} <--> '"v"



interactive_rw nuprl_fpf_cap_single_rw  {| reduce |}  :
   "fpf-cap"[]{"fpf-single"[]{'"x";'"v"};'"eq";'"y";'"z"} <-->
      "ifthenelse"[]{"apply"[]{"apply"[]{"eqof"[]{'"eq"};'"x"};'"y"};'"v";'"z"}

interactive_rw nuprl_fpf_cap_join_rw  {| reduce |} : (* ??? *)
   ('f in fpf{top;x.top} ) -->
   ('g in fpf{top;x.top} ) -->
   "fpf-cap"[]{"fpf-join"[]{'eq;'f;'g};'eq;'y;'z} <-->
     "fpf-cap"[]{'f;'eq;'y;"fpf-cap"[]{'g;'eq;'y;'z}}



interactive nuprl_fpf_dom_single_intro {| intro[intro_typeinf <<'x>> ] |} 'A:
   [wf] sequent  { <Gamma> >- '"eq" in "deq"[]{'"A"} }  -->
   sequent  { <Gamma> >-  '"y"= '"x" in 'A } -->
   sequent  { <Gamma> >- "assert"{"fpf-dom"[]{'"eq";'"x";"fpf-single"[]{'"y";'"v"}}} }

interactive nuprl_fpf_dom_single_elim {| elim[elim_typeinf <<'x>> ] |}'Gamma  'A:
   [wf] sequent  { <Gamma> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent  { <Gamma> >- '"x" in '"A" }  -->
   [wf] sequent  { <Gamma> >- '"y" in '"A" }  -->
   sequent  { <Gamma>;  '"y"= '"x" in 'A; <Delta> >- 'C } -->
   sequent  { <Gamma>; "assert"{"fpf-dom"[]{'"eq";'"x";"fpf-single"[]{'"y";'"v"}}}; <Delta> >- 'C }




interactive nuprl_fpf_compatible_self {| intro[] |} :
   [wf] sequent  { <Gamma> >- "type"{'"A"} }  -->
   [wf] sequent  { <Gamma> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent  { <Gamma>; a : 'A  >- "type"{'B['a]}  }  -->
   [wf] sequent  { <Gamma> >- '"f" in "fpf"[]{'"A";"a".'B['a]} }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{'"A";"a".'B['a];'"eq";'"f";'"f"} }




interactive nuprl_fpf_compatible_join {| intro[] |} :
   [wf] sequent  { <Gamma> >- "type"{'"A"} }  -->
   [wf] sequent  { <Gamma> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent  { <Gamma>; x:'A >- "type"{'B['x]} }  -->
   [wf] sequent  { <Gamma> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent  { <Gamma> >- '"g" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent  { <Gamma> >- '"h" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{'"A";"a".'"B"['"a"];'"eq";'"h";'"f"} } -->
   sequent  { <Gamma> >- "fpf-compatible"[]{'"A";"a".'"B"['"a"];'"eq";'"h";'"g"} } -->
   sequent  { <Gamma> >- "fpf-compatible"[]{'"A";"a".'"B"['"a"];'"eq";'h;"fpf-join"[]{'"eq";'"f";'"g"}} }

interactive nuprl_fpf_compatible_join2 {| intro[] |} :
   [wf] sequent  { <Gamma> >- "type"{'"A"} }  -->
   [wf] sequent  { <Gamma> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent  { <Gamma>; x:'A >- "type"{'B['x]} }  -->
   [wf] sequent  { <Gamma> >- '"f" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent  { <Gamma> >- '"g" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   [wf] sequent  { <Gamma> >- '"h" in "fpf"[]{'"A";"a".'"B"['"a"]} }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{'"A";"a".'"B"['"a"];'"eq";'"f";'"h"} } -->
   sequent  { <Gamma> >- "fpf-compatible"[]{'"A";"a".'"B"['"a"];'"eq";'"g";'"h"} } -->
   sequent  { <Gamma> >- "fpf-compatible"[]{'"A";"a".'"B"['"a"];'"eq";"fpf-join"[]{'"eq";'"f";'"g"};'"h"} }

interactive nuprl_fpf_compatible_singles  {| intro[] |} :
   [wf] sequent  { <Gamma> >- "type"{'"A"} }  -->
   [wf] sequent  { <Gamma> >- '"eq" in "deq"[]{'"A"} }  -->
   [wf] sequent  { <Gamma>; x:'A >- "type"{'B['x]} }  -->
   [wf] sequent  { <Gamma> >- '"x" in '"A" }  -->
   [wf] sequent  { <Gamma> >- '"y" in '"A" }  -->
   [wf] sequent  { <Gamma> >- '"v" in '"B"['x] }  -->
   [wf] sequent  { <Gamma> >- '"u" in '"B"['y] }  -->
   sequent  { <Gamma>; 'x='y in 'A >- 'v='u in 'B['x] }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{'"A";"a".'B['a];'"eq";"fpf-single"[]{'"x";'"v"};"fpf-single"[]{'"y";'"u"}} }



