extends Ma_base__compat__lemmas_object_directory

open Dtactic


interactive nuprl_ma__single__pre__init__ma__single__pre__init__compatible   :
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"init" in "fpf"[]{"Id"[]{};"x"."fpf-cap"[]{'"ds";"id-deq"[]{};'"x";"void"[]{}}} }  -->
   [wf] sequent { <H> >- '"a1" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T1" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"d1" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"i1" in "fpf"[]{"Id"[]{};"x"."fpf-cap"[]{'"d1";"id-deq"[]{};'"x";"void"[]{}}} }  -->
   sequent { <H> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";'"d1"} }  -->
   sequent { <H> >- "fpf-compatible"[]{"Id"[]{};"x"."fpf-cap"[]{"fpf-join"[]{"id-deq"[]{};'"ds";'"d1"};"id-deq"[]{};'"x";"void"[]{}};"id-deq"[]{};'"init";'"i1"} }  -->
   sequent { <H> >- "not"[]{"equal"[]{"Id"[]{};'"a";'"a1"}} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-pre-init"[]{'"ds";'"init";'"a";'"T";'"P"};"ma-single-pre-init"[]{'"d1";'"i1";'"a1";'"T1";'"P1"}} }

interactive nuprl_ma__single__pre__ma__single__pre__compatible   :
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"a1" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T1" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"d1" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   sequent { <H> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";'"d1"} }  -->
   sequent { <H> >- "not"[]{"equal"[]{"Id"[]{};'"a";'"a1"}} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-pre"[]{'"ds";'"a";'"T";'"P"};"ma-single-pre"[]{'"d1";'"a1";'"T1";'"P1"}} }

interactive nuprl_ma__single__sends__ma__single__sends__compatible   :
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"f" in "list"[]{"prod"[]{"Id"[]{};"tg"."top"[]{}}} }  -->
   [wf] sequent { <H> >- '"k1" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"l1" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"d1" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"d2" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"f1" in "list"[]{"prod"[]{"Id"[]{};"tg"."top"[]{}}} }  -->
   sequent { <H> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";'"d1"} }  -->
   sequent { <H> >- "fpf-compatible"[]{"Knd"[]{};"x"."univ"[level:l]{};"Kind-deq"[]{};'"da";'"d2"} }  -->
   sequent { <H> >- "not"[]{"equal"[]{"prod"[]{"Knd"[]{};""."IdLnk"[]{}};"pair"[]{'"k";'"l"};"pair"[]{'"k1";'"l1"}}} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-sends"[]{'"ds";'"da";'"k";'"l";'"f"};"ma-single-sends"[]{'"d1";'"d2";'"k1";'"l1";'"f1"}} }

interactive nuprl_ma__single__effect__ma__single__effect__compatible   :
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"x1" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k1" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"d1" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"d2" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   sequent { <H> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";'"d1"} }  -->
   sequent { <H> >- "fpf-compatible"[]{"Knd"[]{};"x"."univ"[level:l]{};"Kind-deq"[]{};'"da";'"d2"} }  -->
   sequent { <H> >- "not"[]{"equal"[]{"prod"[]{"Knd"[]{};""."Id"[]{}};"pair"[]{'"k";'"x"};"pair"[]{'"k1";'"x1"}}} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-effect"[]{'"ds";'"da";'"k";'"x";'"f"};"ma-single-effect"[]{'"d1";'"d2";'"k1";'"x1";'"f1"}} }

interactive nuprl_ma__single__sframe__ma__single__sframe__compatible   :
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"l1" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"t1" in "Id"[]{} }  -->
   sequent { <H> >- "not"[]{"equal"[]{"prod"[]{"IdLnk"[]{};""."Id"[]{}};"pair"[]{'"l";'"tg"};"pair"[]{'"l1";'"t1"}}} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-sframe"[]{'"L";'"l";'"tg"};"ma-single-sframe"[]{'"L1";'"l1";'"t1"}} }

interactive nuprl_ma__single__frame__ma__single__frame__compatible   :
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"t" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"x1" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"t1" in "univ"[level:l]{} }  -->
   sequent { <H> >- "not"[]{"equal"[]{"Id"[]{};'"x";'"x1"}} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-frame"[]{'"L";'"t";'"x"};"ma-single-frame"[]{'"L1";'"t1";'"x1"}} }

interactive nuprl_ma__single__init__ma__single__init__compatible   :
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"x1" in "Id"[]{} }  -->
   sequent { <H> >- "not"[]{"equal"[]{"Id"[]{};'"x";'"x1"}} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-init"[]{'"x";'"t";'"v"};"ma-single-init"[]{'"x1";'"t1";'"v1"}} }


(**** display forms ****)


