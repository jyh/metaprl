extends Ma_prog_1

open Dtactic


interactive nuprl_subtype_rel_wf {| intro[] |}   :
   [wf] sequent { <H> >- '"A" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"B" in "univ"[level:l]{} }  -->
   sequent { <H> >- ("subtype"[]{'"A";'"B"} in "univ"[level:l]{}) }

interactive nuprl_subtype_rel_wf_type {| intro[] |}   :
   [wf] sequent { <H> >- "type"{'"A" } }  -->
   [wf] sequent { <H> >- "type"{'"B" } }  -->
   sequent { <H> >- "type"{"subtype"[]{'"A";'"B"}} }


(**** display forms ****)


dform nuprl_subtype_rel : except_mode[src] :: "subtype"[]{'"A";'"B"} =
   `"" pushm[2:n] `"" slot{'"A"} `"" szone sbreak[""," "] ezone `"" sqsubseteq `"r "
    slot{'"B"} `"" popm  `""


