extends Nuprl_diagonal__compat__lemmas_object_directory

open Dtactic


interactive nuprl_ma_single_pre_init_ma_single_pre_init_compatible  {| intro[] |} :
   [wf] sequent  { <Gamma> >- '"a" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent  { <Gamma> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"P" in "top"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"init" in "fpf"[]{"Id"[]{};"x"."fpf-cap"[]{'"ds";"id-deq"[]{};'"x";"void"[]{}}} }  -->
   [wf] sequent  { <Gamma> >- '"a1" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"T1" in "univ"[level:l]{} }  -->
   [wf] sequent  { <Gamma> >- '"d1" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"P1" in "top"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"i1" in "fpf"[]{"Id"[]{};"x"."fpf-cap"[]{'"d1";"id-deq"[]{};'"x";"void"[]{}}} }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";'"d1"} }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Id"[]{};"x"."fpf-cap"[]{"fpf-join"[]{"id-deq"[]{};'"ds";'"d1"};"id-deq"[]{};'"x";"void"[]{}};"id-deq"[]{};'"init";'"i1"} }  -->
   sequent  { <Gamma> >- "not"[]{"equal"[]{"Id"[]{};'"a";'"a1"}} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-pre-init"[]{'"ds";'"init";'"a";'"T";'"P"};"ma-single-pre-init"[]{'"d1";'"i1";'"a1";'"T1";'"P1"}} }

interactive nuprl_ma_single_pre_ma_single_pre_compatible    {| intro[] |} :
   [wf] sequent  { <Gamma> >- '"a" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent  { <Gamma> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"P" in "top"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"a1" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"T1" in "univ"[level:l]{} }  -->
   [wf] sequent  { <Gamma> >- '"d1" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"P1" in "top"[]{} }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";'"d1"} }  -->
   sequent  { <Gamma> >- "not"[]{"equal"[]{"Id"[]{};'"a";'"a1"}} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-pre"[]{'"ds";'"a";'"T";'"P"};"ma-single-pre"[]{'"d1";'"a1";'"T1";'"P1"}} }

interactive nuprl_ma_single_sends_ma_single_sends_compatible    {| intro[] |} :
   [wf] sequent  { <Gamma> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"da" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"f" in "list"[]{"prod"[]{"Id"[]{};"tg"."top"[]{}}} }  -->
   [wf] sequent  { <Gamma> >- '"k1" in "Knd"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"l1" in "IdLnk"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"d1" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"d2" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"f1" in "list"[]{"prod"[]{"Id"[]{};"tg"."top"[]{}}} }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";'"d1"} }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Knd"[]{};"x"."univ"[level:l]{};"Kind-deq"[]{};'"da";'"d2"} }  -->
   sequent  { <Gamma> >- "not"[]{"equal"[]{"prod"[]{"Knd"[]{};""."IdLnk"[]{}};"pair"[]{'"k";'"l"};"pair"[]{'"k1";'"l1"}}} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-sends"[]{'"ds";'"da";'"k";'"l";'"f"};"ma-single-sends"[]{'"d1";'"d2";'"k1";'"l1";'"f1"}} }

interactive nuprl_ma_single_effect_ma_single_effect_compatible   {| intro[] |}  :
   [wf] sequent  { <Gamma> >- '"x" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"da" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"f" in "top"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"x1" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"k1" in "Knd"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"d1" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"d2" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"f1" in "top"[]{} }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";'"d1"} }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Knd"[]{};"x"."univ"[level:l]{};"Kind-deq"[]{};'"da";'"d2"} }  -->
   sequent  { <Gamma> >- "not"[]{"equal"[]{"prod"[]{"Knd"[]{};""."Id"[]{}};"pair"[]{'"k";'"x"};"pair"[]{'"k1";'"x1"}}} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-effect"[]{'"ds";'"da";'"k";'"x";'"f"};"ma-single-effect"[]{'"d1";'"d2";'"k1";'"x1";'"f1"}} }

interactive nuprl_ma_single_sframe_ma_single_sframe_compatible    {| intro[] |} :
   [wf] sequent  { <Gamma> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"L" in "top"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"l1" in "IdLnk"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"t1" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"L1" in "top"[]{} }  -->
   sequent  { <Gamma> >- "not"[]{"equal"[]{"prod"[]{"IdLnk"[]{};""."Id"[]{}};"pair"[]{'"l";'"tg"};"pair"[]{'"l1";'"t1"}}} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-sframe"[]{'"L";'"l";'"tg"};"ma-single-sframe"[]{'"L1";'"l1";'"t1"}} }

interactive nuprl_ma_single_frame_ma_single_frame_compatible    {| intro[] |} :
   [wf] sequent  { <Gamma> >- '"x" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"L" in "top"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"t" in "univ"[level:l]{} }  -->
   [wf] sequent  { <Gamma> >- '"x1" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"L1" in "top"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"t1" in "univ"[level:l]{} }  -->
   sequent  { <Gamma> >- "not"[]{"equal"[]{"Id"[]{};'"x";'"x1"}} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-frame"[]{'"L";'"t";'"x"};"ma-single-frame"[]{'"L1";'"t1";'"x1"}} }

interactive nuprl_ma_single_init_ma_single_init_compatible    {| intro[] |} :
   [wf] sequent  { <Gamma> >- '"x" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"t" in "top"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"v" in "top"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"x1" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"t1" in "top"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"v1" in "top"[]{} }  -->
   sequent  { <Gamma> >- "not"[]{"equal"[]{"Id"[]{};'"x";'"x1"}} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-init"[]{'"x";'"t";'"v"};"ma-single-init"[]{'"x1";'"t1";'"v1"}} }



