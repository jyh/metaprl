extends Nuprl_message__automata

open Dtactic

define pw_compat : "pw_ma-compat"[level:l]{'L} <--> all_list{'L; A_1.all_list{'L; A_2."ma-compat"[level:l]{'A_1;'A_2}}}

define pw_compat_list : pw_compat_list[level:l] <--> ({L:list{msga[level:l]} | "pw_ma-compat"[level:l]{'L}})

interactive empty_is_pw_compat  {| intro[] |} :
   sequent  { <H> >- nil in pw_compat_list[level:l] }


interactive all_list_if  {| intro[] |} :
   [wf] sequent  { <H> >- 'b in bool  } -->
   sequent  { <H>; "assert"{'b}  >-  all_list{'l; x. 'P['x]} } -->
   sequent  { <H>; "assert"{bnot{'b}} >-  all_list{'m; x. 'P['x]} } -->
   sequent  { <H> >- all_list{if 'b then 'l else 'm;  x. 'P['x]} }


prim msga_wf {| intro[] |} :
   sequent  { <H> >- "type"{msga[level:l]} } =
   it

prim join_wf {| intro[] |} :
   sequent  { <H> >- 'L in pw_compat_list[level:l]  } -->
   sequent  { <H> >- "ma-join-list"{'L} in msga[level:l] } =
   it

prim compat_wf {| intro[] |} :
   sequent  { <H> >-  'A in msga[level:l] } -->
   sequent  { <H> >-  'B in msga[level:l] } -->
   sequent  { <H> >- "type"{"ma-compat"[level:l]{'A;'B}} } =
   it

prim comp_left_join {| intro[] |} :
   [wf] sequent  { <H> >- 'L in pw_compat_list[level:l]  } -->
   [wf] sequent  { <H> >- 'B in msga[level:l]  } -->
   sequent  { <H> >- all_list{'L; A."ma-compat"[level:l]{'A;'B}}  } -->
   sequent  { <H> >- "ma-compat"[level:l]{"ma-join-list"{'L};'B} } =
   it

prim comp_right_join {| intro[] |} :
   [wf] sequent  { <H> >- 'A in msga[level:l]  } -->
   [wf] sequent  { <H> >- 'M in pw_compat_list[level:l]  } -->
   sequent  { <H> >- all_list{'M; B."ma-compat"[level:l]{'A;'B}}  } -->
   sequent  { <H> >- "ma-compat"[level:l]{'A; "ma-join-list"{'M}} } =
   it

interactive comp_join_join {| intro[] |} :
   [wf] sequent  { <H> >- 'L in pw_compat_list[level:l]  } -->
   [wf] sequent  { <H> >- 'M in pw_compat_list[level:l]  } -->
   sequent  { <H> >- all_list{'L; A.all_list{'M; B."ma-compat"[level:l]{'A;'B}}}  } -->
   sequent  { <H> >- "ma-compat"[level:l]{"ma-join-list"{'L}; "ma-join-list"{'M}} }

interactive comp_left_if {| intro[] |} :
   [wf] sequent  { <H> >- 'b in bool  } -->
   sequent  { <H>; "assert"{'b} >- "ma-compat"[level:l]{'A;'C}  } -->
   sequent  { <H>; "assert"{bnot{'b}} >- "ma-compat"[level:l]{'B;'C}  } -->
   sequent  { <H> >- "ma-compat"[level:l]{ if 'b then 'A else 'B; 'C} }

interactive comp_right_if {| intro[] |} :
   [wf] sequent  { <H> >- 'b in bool  } -->
   sequent  { <H>; "assert"{'b} >- "ma-compat"[level:l]{'C;'A}  } -->
   sequent  { <H>; "assert"{bnot{'b}} >- "ma-compat"[level:l]{'C;'B}  } -->
   sequent  { <H> >- "ma-compat"[level:l]{'C; if 'b then 'A else 'B} }


interactive nuprl_ma_empty_compat_left   {| intro[] |} :
   [wf] sequent  { <Gamma> >- '"A" in "msga"[level:l]{} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-empty"[]{};'"A"} }

interactive nuprl_ma_empty_compat_right   {| intro[] |} :
   [wf] sequent  { <Gamma> >- '"A" in "msga"[level:l]{} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{'"A";"ma-empty"[]{}} }

interactive nuprl_ma_empty_compatible_left  {| intro[] |} :
   [wf] sequent  { <Gamma> >- '"A" in "msga"[level:l]{} }  -->
   sequent  { <Gamma> >- "ma-compatible"[level:l]{"ma-empty"[]{};'"A"} }

interactive nuprl_ma_empty_compatible_right  {| intro[] |}  :
   [wf] sequent  { <Gamma> >- '"A" in "msga"[level:l]{} }  -->
   sequent  { <Gamma> >- "ma-compatible"[level:l]{'"A";"ma-empty"[]{}} }





