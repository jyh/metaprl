extends Ma_lemmas

open Dtactic


interactive nuprl_ma__single__pre__init__ma__single__pre__compatible   :
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"init" in "fpf"[]{"Id"[]{};"x"."top"[]{}} }  -->
   [wf] sequent { <H> >- '"a1" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"d1" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   sequent { <H> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";'"d1"} }  -->
   sequent { <H> >- "not"[]{"equal"[]{"Id"[]{};'"a";'"a1"}} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-pre-init"[]{'"ds";'"init";'"a";'"T";'"P"};"ma-single-pre"[]{'"d1";'"a1";'"T1";'"P1"}} }

interactive nuprl_ma__single__pre__ma__single__pre__init__compatible   :
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"init" in "fpf"[]{"Id"[]{};"x"."top"[]{}} }  -->
   [wf] sequent { <H> >- '"a1" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"d1" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   sequent { <H> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";'"d1"} }  -->
   sequent { <H> >- "not"[]{"equal"[]{"Id"[]{};'"a";'"a1"}} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-pre"[]{'"d1";'"a1";'"T1";'"P1"};"ma-single-pre-init"[]{'"ds";'"init";'"a";'"T";'"P"}} }

interactive nuprl_ma__single__pre__init__ma__single__sends__compatible   :
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"init" in "fpf"[]{"Id"[]{};"x"."top"[]{}} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"d1" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"f" in "list"[]{"prod"[]{"Id"[]{};"tg"."top"[]{}}} }  -->
   sequent { <H> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";'"d1"} }  -->
   sequent { <H> >- "fpf-compatible"[]{"Knd"[]{};"x"."univ"[level:l]{};"Kind-deq"[]{};"fpf-single"[]{"locl"[]{'"a"};'"T"};'"da"} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-pre-init"[]{'"ds";'"init";'"a";'"T";'"P"};"ma-single-sends"[]{'"d1";'"da";'"k";'"l";'"f"}} }

interactive nuprl_ma__single__sends__ma__single__pre__init__compatible   :
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"init" in "fpf"[]{"Id"[]{};"x"."top"[]{}} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"d1" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"f" in "list"[]{"prod"[]{"Id"[]{};"tg"."top"[]{}}} }  -->
   sequent { <H> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";'"d1"} }  -->
   sequent { <H> >- "fpf-compatible"[]{"Knd"[]{};"x"."univ"[level:l]{};"Kind-deq"[]{};"fpf-single"[]{"locl"[]{'"a"};'"T"};'"da"} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-sends"[]{'"d1";'"da";'"k";'"l";'"f"};"ma-single-pre-init"[]{'"ds";'"init";'"a";'"T";'"P"}} }

interactive nuprl_ma__single__pre__init__ma__single__effect__compatible   :
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"init" in "fpf"[]{"Id"[]{};"x"."top"[]{}} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"d1" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   sequent { <H> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";'"d1"} }  -->
   sequent { <H> >- "fpf-compatible"[]{"Knd"[]{};"x"."univ"[level:l]{};"Kind-deq"[]{};"fpf-single"[]{"locl"[]{'"a"};'"T"};'"da"} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-pre-init"[]{'"ds";'"init";'"a";'"T";'"P"};"ma-single-effect"[]{'"d1";'"da";'"k";'"x";'"f"}} }

interactive nuprl_ma__single__effect__ma__single__pre__init__compatible   :
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"init" in "fpf"[]{"Id"[]{};"x"."top"[]{}} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"d1" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   sequent { <H> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";'"d1"} }  -->
   sequent { <H> >- "fpf-compatible"[]{"Knd"[]{};"x"."univ"[level:l]{};"Kind-deq"[]{};"fpf-single"[]{"locl"[]{'"a"};'"T"};'"da"} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-effect"[]{'"d1";'"da";'"k";'"x";'"f"};"ma-single-pre-init"[]{'"ds";'"init";'"a";'"T";'"P"}} }

interactive nuprl_ma__single__pre__init__ma__single__sframe__compatible   :
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."top"[]{}} }  -->
   [wf] sequent { <H> >- '"init" in "fpf"[]{"Id"[]{};"x"."top"[]{}} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{"Knd"[]{}} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-pre-init"[]{'"ds";'"init";'"a";'"T";'"P"};"ma-single-sframe"[]{'"L";'"l";'"tg"}} }

interactive nuprl_ma__single__sframe__ma__single__pre__init__compatible   :
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."top"[]{}} }  -->
   [wf] sequent { <H> >- '"init" in "fpf"[]{"Id"[]{};"x"."top"[]{}} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{"Knd"[]{}} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-sframe"[]{'"L";'"l";'"tg"};"ma-single-pre-init"[]{'"ds";'"init";'"a";'"T";'"P"}} }

interactive nuprl_ma__single__pre__init__ma__single__frame__compatible   :
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"init" in "fpf"[]{"Id"[]{};"x"."top"[]{}} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{"Knd"[]{}} }  -->
   [wf] sequent { <H> >- '"t" in "univ"[level:l]{} }  -->
   sequent { <H> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";"fpf-single"[]{'"x";'"t"}} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-pre-init"[]{'"ds";'"init";'"a";'"T";'"P"};"ma-single-frame"[]{'"L";'"t";'"x"}} }

interactive nuprl_ma__single__frame__ma__single__pre__init__compatible   :
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"init" in "fpf"[]{"Id"[]{};"x"."top"[]{}} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{"Knd"[]{}} }  -->
   [wf] sequent { <H> >- '"t" in "univ"[level:l]{} }  -->
   sequent { <H> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";"fpf-single"[]{'"x";'"t"}} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-frame"[]{'"L";'"t";'"x"};"ma-single-pre-init"[]{'"ds";'"init";'"a";'"T";'"P"}} }

interactive nuprl_ma__single__pre__init__ma__single__init__compatible   :
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"init" in "fpf"[]{"Id"[]{};"x"."fpf-cap"[]{'"ds";"id-deq"[]{};'"x";"void"[]{}}} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"t" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"v" in '"t" }  -->
   sequent { <H> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";"fpf-single"[]{'"x";'"t"}} }  -->
   sequent { <H>; "assert"[]{"fpf-dom"[]{"id-deq"[]{};'"x";'"init"}}  >- "equal"[]{'"t";"fpf-ap"[]{'"init";"id-deq"[]{};'"x"};'"v"} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-pre-init"[]{'"ds";'"init";'"a";'"T";'"P"};"ma-single-init"[]{'"x";'"t";'"v"}} }

interactive nuprl_ma__single__init__ma__single__pre__init__compatible   :
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"init" in "fpf"[]{"Id"[]{};"x"."fpf-cap"[]{'"ds";"id-deq"[]{};'"x";"void"[]{}}} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"t" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"v" in '"t" }  -->
   sequent { <H> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";"fpf-single"[]{'"x";'"t"}} }  -->
   sequent { <H>; "assert"[]{"fpf-dom"[]{"id-deq"[]{};'"x";'"init"}}  >- "equal"[]{'"t";"fpf-ap"[]{'"init";"id-deq"[]{};'"x"};'"v"} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-init"[]{'"x";'"t";'"v"};"ma-single-pre-init"[]{'"ds";'"init";'"a";'"T";'"P"}} }

interactive nuprl_ma__single__pre__ma__single__sends__compatible   :
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"d1" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"f" in "list"[]{"prod"[]{"Id"[]{};"tg"."top"[]{}}} }  -->
   sequent { <H> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";'"d1"} }  -->
   sequent { <H> >- "fpf-compatible"[]{"Knd"[]{};"x"."univ"[level:l]{};"Kind-deq"[]{};"fpf-single"[]{"locl"[]{'"a"};'"T"};'"da"} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-pre"[]{'"ds";'"a";'"T";'"P"};"ma-single-sends"[]{'"d1";'"da";'"k";'"l";'"f"}} }

interactive nuprl_ma__single__sends__ma__single__pre__compatible   :
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"d1" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"f" in "list"[]{"prod"[]{"Id"[]{};"tg"."top"[]{}}} }  -->
   sequent { <H> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";'"d1"} }  -->
   sequent { <H> >- "fpf-compatible"[]{"Knd"[]{};"x"."univ"[level:l]{};"Kind-deq"[]{};"fpf-single"[]{"locl"[]{'"a"};'"T"};'"da"} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-sends"[]{'"d1";'"da";'"k";'"l";'"f"};"ma-single-pre"[]{'"ds";'"a";'"T";'"P"}} }

interactive nuprl_ma__single__pre__ma__single__effect__compatible   :
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"d1" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   sequent { <H> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";'"d1"} }  -->
   sequent { <H> >- "fpf-compatible"[]{"Knd"[]{};"x"."univ"[level:l]{};"Kind-deq"[]{};"fpf-single"[]{"locl"[]{'"a"};'"T"};'"da"} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-pre"[]{'"ds";'"a";'"T";'"P"};"ma-single-effect"[]{'"d1";'"da";'"k";'"x";'"f"}} }

interactive nuprl_ma__single__effect__ma__single__pre__compatible   :
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"d1" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   sequent { <H> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";'"d1"} }  -->
   sequent { <H> >- "fpf-compatible"[]{"Knd"[]{};"x"."univ"[level:l]{};"Kind-deq"[]{};"fpf-single"[]{"locl"[]{'"a"};'"T"};'"da"} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-effect"[]{'"d1";'"da";'"k";'"x";'"f"};"ma-single-pre"[]{'"ds";'"a";'"T";'"P"}} }

interactive nuprl_ma__single__pre__ma__single__sframe__compatible   :
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."top"[]{}} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-pre"[]{'"ds";'"a";'"T";'"P"};"ma-single-sframe"[]{'"L";'"l";'"tg"}} }

interactive nuprl_ma__single__sframe__ma__single__pre__compatible   :
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."top"[]{}} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-sframe"[]{'"L";'"l";'"tg"};"ma-single-pre"[]{'"ds";'"a";'"T";'"P"}} }

interactive nuprl_ma__single__pre__ma__single__frame__compatible   :
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"t" in "univ"[level:l]{} }  -->
   sequent { <H> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";"fpf-single"[]{'"x";'"t"}} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-pre"[]{'"ds";'"a";'"T";'"P"};"ma-single-frame"[]{'"L";'"t";'"x"}} }

interactive nuprl_ma__single__frame__ma__single__pre__compatible   :
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"t" in "univ"[level:l]{} }  -->
   sequent { <H> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";"fpf-single"[]{'"x";'"t"}} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-frame"[]{'"L";'"t";'"x"};"ma-single-pre"[]{'"ds";'"a";'"T";'"P"}} }

interactive nuprl_ma__single__pre__ma__single__init__compatible   :
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"t" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"v" in '"t" }  -->
   sequent { <H> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";"fpf-single"[]{'"x";'"t"}} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-pre"[]{'"ds";'"a";'"T";'"P"};"ma-single-init"[]{'"x";'"t";'"v"}} }

interactive nuprl_ma__single__init__ma__single__pre__compatible   :
   [wf] sequent { <H> >- '"a" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"t" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"v" in '"t" }  -->
   sequent { <H> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";"fpf-single"[]{'"x";'"t"}} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-init"[]{'"x";'"t";'"v"};"ma-single-pre"[]{'"ds";'"a";'"T";'"P"}} }

interactive nuprl_ma__single__sends__ma__single__effect__compatible   :
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"f" in "list"[]{"prod"[]{"Id"[]{};"tg"."top"[]{}}} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k1" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"d1" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"d2" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   sequent { <H> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";'"d1"} }  -->
   sequent { <H> >- "fpf-compatible"[]{"Knd"[]{};"x"."univ"[level:l]{};"Kind-deq"[]{};'"da";'"d2"} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-sends"[]{'"ds";'"da";'"k";'"l";'"f"};"ma-single-effect"[]{'"d1";'"d2";'"k1";'"x";'"f1"}} }

interactive nuprl_ma__single__effect__ma__single__sends__compatible   :
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"f" in "list"[]{"prod"[]{"Id"[]{};"tg"."top"[]{}}} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k1" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"d1" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"d2" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   sequent { <H> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";'"d1"} }  -->
   sequent { <H> >- "fpf-compatible"[]{"Knd"[]{};"x"."univ"[level:l]{};"Kind-deq"[]{};'"da";'"d2"} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-effect"[]{'"d1";'"d2";'"k1";'"x";'"f1"};"ma-single-sends"[]{'"ds";'"da";'"k";'"l";'"f"}} }

interactive nuprl_ma__single__sends__ma__single__sframe__compatible   :
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"f" in "list"[]{"prod"[]{"Id"[]{};"tg"."top"[]{}}} }  -->
   [wf] sequent { <H> >- '"l1" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{"Knd"[]{}} }  -->
   sequent { <H>; "equal"[]{"IdLnk"[]{};'"l";'"l1"} ; "mem"[]{'"tg";"map"[]{"lambda"[]{"p"."fst"[]{'"p"}};'"f"};"Id"[]{}}  >- "mem"[]{'"k";'"L";"Knd"[]{}} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-sends"[]{'"ds";'"da";'"k";'"l";'"f"};"ma-single-sframe"[]{'"L";'"l1";'"tg"}} }

interactive nuprl_ma__single__sframe__ma__single__sends__compatible   :
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"f" in "list"[]{"prod"[]{"Id"[]{};"tg"."top"[]{}}} }  -->
   [wf] sequent { <H> >- '"l1" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{"Knd"[]{}} }  -->
   sequent { <H>; "equal"[]{"IdLnk"[]{};'"l";'"l1"} ; "mem"[]{'"tg";"map"[]{"lambda"[]{"p"."fst"[]{'"p"}};'"f"};"Id"[]{}}  >- "mem"[]{'"k";'"L";"Knd"[]{}} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-sframe"[]{'"L";'"l1";'"tg"};"ma-single-sends"[]{'"ds";'"da";'"k";'"l";'"f"}} }

interactive nuprl_ma__single__sends__ma__single__frame__compatible   :
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"a"."top"[]{}} }  -->
   [wf] sequent { <H> >- '"f" in "list"[]{"prod"[]{"Id"[]{};"tg"."top"[]{}}} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"t" in "univ"[level:l]{} }  -->
   sequent { <H> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";"fpf-single"[]{'"x";'"t"}} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-sends"[]{'"ds";'"da";'"k";'"l";'"f"};"ma-single-frame"[]{'"L";'"t";'"x"}} }

interactive nuprl_ma__single__frame__ma__single__sends__compatible   :
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"a"."top"[]{}} }  -->
   [wf] sequent { <H> >- '"f" in "list"[]{"prod"[]{"Id"[]{};"tg"."top"[]{}}} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"t" in "univ"[level:l]{} }  -->
   sequent { <H> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";"fpf-single"[]{'"x";'"t"}} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-frame"[]{'"L";'"t";'"x"};"ma-single-sends"[]{'"ds";'"da";'"k";'"l";'"f"}} }

interactive nuprl_ma__single__sends__ma__single__init__compatible   :
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"a"."top"[]{}} }  -->
   [wf] sequent { <H> >- '"f" in "list"[]{"prod"[]{"Id"[]{};"tg"."top"[]{}}} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"t" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"v" in '"t" }  -->
   sequent { <H> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";"fpf-single"[]{'"x";'"t"}} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-sends"[]{'"ds";'"da";'"k";'"l";'"f"};"ma-single-init"[]{'"x";'"t";'"v"}} }

interactive nuprl_ma__single__init__ma__single__sends__compatible   :
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"a"."top"[]{}} }  -->
   [wf] sequent { <H> >- '"f" in "list"[]{"prod"[]{"Id"[]{};"tg"."top"[]{}}} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"t" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"v" in '"t" }  -->
   sequent { <H> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";"fpf-single"[]{'"x";'"t"}} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-init"[]{'"x";'"t";'"v"};"ma-single-sends"[]{'"ds";'"da";'"k";'"l";'"f"}} }

interactive nuprl_ma__single__effect__ma__single__sframe__compatible   :
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."top"[]{}} }  -->
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"a"."top"[]{}} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-effect"[]{'"ds";'"da";'"k";'"x";'"f"};"ma-single-sframe"[]{'"L";'"l";'"tg"}} }

interactive nuprl_ma__single__sframe__ma__single__effect__compatible   :
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."top"[]{}} }  -->
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"a"."top"[]{}} }  -->
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-sframe"[]{'"L";'"l";'"tg"};"ma-single-effect"[]{'"ds";'"da";'"k";'"x";'"f"}} }

interactive nuprl_ma__single__effect__ma__single__frame__compatible   :
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"a"."top"[]{}} }  -->
   [wf] sequent { <H> >- '"x1" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{"Knd"[]{}} }  -->
   [wf] sequent { <H> >- '"t" in "univ"[level:l]{} }  -->
   sequent { <H> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";"fpf-single"[]{'"x1";'"t"}} }  -->
   sequent { <H>; "equal"[]{"Id"[]{};'"x";'"x1"}  >- "mem"[]{'"k";'"L";"Knd"[]{}} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-effect"[]{'"ds";'"da";'"k";'"x";'"f"};"ma-single-frame"[]{'"L";'"t";'"x1"}} }

interactive nuprl_ma__single__frame__ma__single__effect__compatible   :
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"a"."top"[]{}} }  -->
   [wf] sequent { <H> >- '"x1" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"L" in "list"[]{"Knd"[]{}} }  -->
   [wf] sequent { <H> >- '"t" in "univ"[level:l]{} }  -->
   sequent { <H> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";"fpf-single"[]{'"x1";'"t"}} }  -->
   sequent { <H>; "equal"[]{"Id"[]{};'"x";'"x1"}  >- "mem"[]{'"k";'"L";"Knd"[]{}} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-frame"[]{'"L";'"t";'"x1"};"ma-single-effect"[]{'"ds";'"da";'"k";'"x";'"f"}} }

interactive nuprl_ma__single__effect__ma__single__init__compatible   :
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"a"."top"[]{}} }  -->
   [wf] sequent { <H> >- '"x1" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"t" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"v" in '"t" }  -->
   sequent { <H> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";"fpf-single"[]{'"x1";'"t"}} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-effect"[]{'"ds";'"da";'"k";'"x";'"f"};"ma-single-init"[]{'"x1";'"t";'"v"}} }

interactive nuprl_ma__single__init__ma__single__effect__compatible   :
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent { <H> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent { <H> >- '"da" in "fpf"[]{"Knd"[]{};"a"."top"[]{}} }  -->
   [wf] sequent { <H> >- '"x1" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"t" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"v" in '"t" }  -->
   sequent { <H> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";"fpf-single"[]{'"x1";'"t"}} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-init"[]{'"x1";'"t";'"v"};"ma-single-effect"[]{'"ds";'"da";'"k";'"x";'"f"}} }

interactive nuprl_ma__single__sframe__ma__single__frame__compatible   :
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-sframe"[]{'"L";'"l";'"tg"};"ma-single-frame"[]{'"L1";'"t";'"x"}} }

interactive nuprl_ma__single__frame__ma__single__sframe__compatible   :
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-frame"[]{'"L1";'"t";'"x"};"ma-single-sframe"[]{'"L";'"l";'"tg"}} }

interactive nuprl_ma__single__sframe__ma__single__init__compatible   :
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-sframe"[]{'"L";'"l";'"tg"};"ma-single-init"[]{'"x";'"t";'"v"}} }

interactive nuprl_ma__single__init__ma__single__sframe__compatible   :
   [wf] sequent { <H> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent { <H> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-init"[]{'"x";'"t";'"v"};"ma-single-sframe"[]{'"L";'"l";'"tg"}} }

interactive nuprl_ma__single__frame__ma__single__init__compatible   :
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"t" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"x1" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"t1" in "univ"[level:l]{} }  -->
   sequent { <H> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};"fpf-single"[]{'"x";'"t"};"fpf-single"[]{'"x1";'"t1"}} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-frame"[]{'"L";'"t";'"x"};"ma-single-init"[]{'"x1";'"t1";'"v"}} }

interactive nuprl_ma__single__init__ma__single__frame__compatible   :
   [wf] sequent { <H> >- '"x" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"t" in "univ"[level:l]{} }  -->
   [wf] sequent { <H> >- '"x1" in "Id"[]{} }  -->
   [wf] sequent { <H> >- '"t1" in "univ"[level:l]{} }  -->
   sequent { <H> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};"fpf-single"[]{'"x";'"t"};"fpf-single"[]{'"x1";'"t1"}} }  -->
   sequent { <H> >- "ma-compat"[level:l]{"ma-single-init"[]{'"x1";'"t1";'"v"};"ma-single-frame"[]{'"L";'"t";'"x"}} }


(**** display forms ****)


