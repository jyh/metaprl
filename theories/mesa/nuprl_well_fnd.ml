extends Ma_core_2

open Dtactic


interactive nuprl_wellfounded_wf {| intro[] |}  '"A" "lambda"[]{"x1", "x".'"r"['"x1";'"x"]}  :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"A";"x1": '"A" >- '"r"['"x";'"x1"] in "univ"[level:l]{} }  -->
   sequent { <H> >- ("well_founded"[level:l]{'"A";"x", "y".'"r"['"x";'"y"]} in "univ"[level':l]{}) }

interactive nuprl_inv_image_ind_a  '"T" '"S" "lambda"[]{"x1", "x".'"r"['"x1";'"x"]} '"f"  :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- '"r"['"x";'"x1"] in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"S" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"S" >- '"f" '"x" in '"T" }  -->
   sequent { <H> >- "well_founded"[level:l]{'"T";"x", "y".'"r"['"x";'"y"]} }  -->
   sequent { <H> >- "well_founded"[level:l]{'"S";"x", "y".'"r"[('"f" '"x");('"f" '"y")]} }

interactive nuprl_inv_image_ind_tp  '"T" '"S" "lambda"[]{"x1", "x".'"r"['"x1";'"x"]} '"f"  :
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T";"x1": '"T" >- '"r"['"x";'"x1"] in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"S" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"S" >- '"f" '"x" in '"T" }  -->
   sequent { <H> >- "well_founded"[level:l]{'"T";"x", "y".'"r"['"x";'"y"]} }  -->
   sequent { <H> >- "well_founded"[level:l]{'"S";"x", "y".'"r"[('"f" '"x");('"f" '"y")]} }

interactive nuprl_inv_image_ind  '"A" '"B" "lambda"[]{"x1", "x".'"r"['"x1";'"x"]} '"f"  :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"A";"x1": '"A" >- '"r"['"x";'"x1"] in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"B" >- '"f" '"x" in '"A" }  -->
   sequent { <H> >- "well_founded"[level:l]{'"A";"x", "y".'"r"['"x";'"y"]} }  -->
   sequent { <H> >- "well_founded"[level:l]{'"B";"x", "y".'"r"[('"f" '"x");('"f" '"y")]} }

interactive nuprl_wellfounded_functionality_wrt_implies  '"T1" '"T2" "lambda"[]{"x1", "x".'"r2"['"x1";'"x"]} "lambda"[]{"x1", "x".'"r1"['"x1";'"x"]}  :
   [wf] sequent { <H> >- '"T1" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"T2" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T1";"x1": '"T1" >- '"r1"['"x";'"x1"] in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T2";"x1": '"T2" >- '"r2"['"x";'"x1"] in "univ"[level:l]{} }  -->
   sequent { <H> >- "equal"[]{"univ"[level:l]{};'"T1";'"T2"} }  -->
   sequent { <H>; "x": '"T1" ; "y": '"T1"  >- "guard"[]{"rev_implies"[]{'"r1"['"x";'"y"];'"r2"['"x";'"y"]}} }  -->
   sequent { <H> >- "guard"[]{"implies"[]{"well_founded"[level:l]{'"T1";"x", "y".'"r1"['"x";'"y"]};"well_founded"[level:l]{'"T2";"x", "y".'"r2"['"x";'"y"]}}} }

interactive nuprl_wellfounded_functionality_wrt_iff  '"T1" '"T2" "lambda"[]{"x1", "x".'"r2"['"x1";'"x"]} "lambda"[]{"x1", "x".'"r1"['"x1";'"x"]}  :
   [wf] sequent { <H> >- '"T1" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"T2" in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T1";"x1": '"T1" >- '"r1"['"x";'"x1"] in "univ"[level:l]{} }  -->
   [wf] sequent { <H>;"x": '"T2";"x1": '"T2" >- '"r2"['"x";'"x1"] in "univ"[level:l]{} }  -->
   sequent { <H> >- "equal"[]{"univ"[level:l]{};'"T1";'"T2"} }  -->
   sequent { <H>; "x": '"T1" ; "y": '"T1"  >- "iff"[]{'"r1"['"x";'"y"];'"r2"['"x";'"y"]} }  -->
   sequent { <H> >- "iff"[]{"well_founded"[level:l]{'"T1";"x", "y".'"r1"['"x";'"y"]};"well_founded"[level:l]{'"T2";"x", "y".'"r2"['"x";'"y"]}} }


(**** display forms ****)



