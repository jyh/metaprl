extends Nuprl_base__compat__lemmas_object_directory

open Dtactic


interactive nuprl_ma_single_pre_init_ma_single_pre_compatible  {| intro [] |} :
   [wf] sequent  { <Gamma> >- '"a" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"init" in "fpf"[]{"Id"[]{};"x"."top"[]{}} }  -->
   [wf] sequent  { <Gamma> >- '"a1" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"d1" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";'"d1"} }  -->
   sequent  { <Gamma> >- "not"[]{"equal"[]{"Id"[]{};'"a";'"a1"}} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-pre-init"[]{'"ds";'"init";'"a";'"T";'"P"};"ma-single-pre"[]{'"d1";'"a1";'"T1";'"P1"}} }

interactive nuprl_ma_single_pre_ma_single_pre_init_compatible  {| intro [] |} :
   [wf] sequent  { <Gamma> >- '"a" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"init" in "fpf"[]{"Id"[]{};"x"."top"[]{}} }  -->
   [wf] sequent  { <Gamma> >- '"a1" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"d1" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";'"d1"} }  -->
   sequent  { <Gamma> >- "not"[]{"equal"[]{"Id"[]{};'"a";'"a1"}} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-pre"[]{'"d1";'"a1";'"T1";'"P1"};"ma-single-pre-init"[]{'"ds";'"init";'"a";'"T";'"P"}} }

interactive nuprl_ma_single_pre_init_ma_single_sends_compatible  {| intro [] |} :
   [wf] sequent  { <Gamma> >- '"a" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent  { <Gamma> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"init" in "fpf"[]{"Id"[]{};"x"."top"[]{}} }  -->
   [wf] sequent  { <Gamma> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"d1" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"da" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"f" in "list"[]{"prod"[]{"Id"[]{};"tg"."top"[]{}}} }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";'"d1"} }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Knd"[]{};"x"."univ"[level:l]{};"Kind-deq"[]{};"fpf-single"[]{"locl"[]{'"a"};'"T"};'"da"} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-pre-init"[]{'"ds";'"init";'"a";'"T";'"P"};"ma-single-sends"[]{'"d1";'"da";'"k";'"l";'"f"}} }

interactive nuprl_ma_single_sends_ma_single_pre_init_compatible  {| intro [] |} :
   [wf] sequent  { <Gamma> >- '"a" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent  { <Gamma> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"init" in "fpf"[]{"Id"[]{};"x"."top"[]{}} }  -->
   [wf] sequent  { <Gamma> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"d1" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"da" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"f" in "list"[]{"prod"[]{"Id"[]{};"tg"."top"[]{}}} }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";'"d1"} }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Knd"[]{};"x"."univ"[level:l]{};"Kind-deq"[]{};"fpf-single"[]{"locl"[]{'"a"};'"T"};'"da"} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-sends"[]{'"d1";'"da";'"k";'"l";'"f"};"ma-single-pre-init"[]{'"ds";'"init";'"a";'"T";'"P"}} }

interactive nuprl_ma_single_pre_init_ma_single_effect_compatible  {| intro [] |} :
   [wf] sequent  { <Gamma> >- '"a" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent  { <Gamma> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"init" in "fpf"[]{"Id"[]{};"x"."top"[]{}} }  -->
   [wf] sequent  { <Gamma> >- '"x" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"d1" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"da" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";'"d1"} }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Knd"[]{};"x"."univ"[level:l]{};"Kind-deq"[]{};"fpf-single"[]{"locl"[]{'"a"};'"T"};'"da"} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-pre-init"[]{'"ds";'"init";'"a";'"T";'"P"};"ma-single-effect"[]{'"d1";'"da";'"k";'"x";'"f"}} }

interactive nuprl_ma_single_effect_ma_single_pre_init_compatible  {| intro [] |} :
   [wf] sequent  { <Gamma> >- '"a" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent  { <Gamma> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"init" in "fpf"[]{"Id"[]{};"x"."top"[]{}} }  -->
   [wf] sequent  { <Gamma> >- '"x" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"d1" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"da" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";'"d1"} }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Knd"[]{};"x"."univ"[level:l]{};"Kind-deq"[]{};"fpf-single"[]{"locl"[]{'"a"};'"T"};'"da"} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-effect"[]{'"d1";'"da";'"k";'"x";'"f"};"ma-single-pre-init"[]{'"ds";'"init";'"a";'"T";'"P"}} }

interactive nuprl_ma_single_pre_init_ma_single_sframe_compatible  {| intro [] |} :
   [wf] sequent  { <Gamma> >- '"a" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"ds" in "fpf"[]{"Id"[]{};"x"."top"[]{}} }  -->
   [wf] sequent  { <Gamma> >- '"init" in "fpf"[]{"Id"[]{};"x"."top"[]{}} }  -->
   [wf] sequent  { <Gamma> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"L" in "list"[]{"Knd"[]{}} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-pre-init"[]{'"ds";'"init";'"a";'"T";'"P"};"ma-single-sframe"[]{'"L";'"l";'"tg"}} }

interactive nuprl_ma_single_sframe_ma_single_pre_init_compatible  {| intro [] |} :
   [wf] sequent  { <Gamma> >- '"a" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"ds" in "fpf"[]{"Id"[]{};"x"."top"[]{}} }  -->
   [wf] sequent  { <Gamma> >- '"init" in "fpf"[]{"Id"[]{};"x"."top"[]{}} }  -->
   [wf] sequent  { <Gamma> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"L" in "list"[]{"Knd"[]{}} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-sframe"[]{'"L";'"l";'"tg"};"ma-single-pre-init"[]{'"ds";'"init";'"a";'"T";'"P"}} }

interactive nuprl_ma_single_pre_init_ma_single_frame_compatible  {| intro [] |} :
   [wf] sequent  { <Gamma> >- '"a" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"init" in "fpf"[]{"Id"[]{};"x"."top"[]{}} }  -->
   [wf] sequent  { <Gamma> >- '"x" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"L" in "list"[]{"Knd"[]{}} }  -->
   [wf] sequent  { <Gamma> >- '"t" in "univ"[level:l]{} }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";"fpf-single"[]{'"x";'"t"}} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-pre-init"[]{'"ds";'"init";'"a";'"T";'"P"};"ma-single-frame"[]{'"L";'"t";'"x"}} }

interactive nuprl_ma_single_frame_ma_single_pre_init_compatible  {| intro [] |} :
   [wf] sequent  { <Gamma> >- '"a" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"init" in "fpf"[]{"Id"[]{};"x"."top"[]{}} }  -->
   [wf] sequent  { <Gamma> >- '"x" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"L" in "list"[]{"Knd"[]{}} }  -->
   [wf] sequent  { <Gamma> >- '"t" in "univ"[level:l]{} }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";"fpf-single"[]{'"x";'"t"}} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-frame"[]{'"L";'"t";'"x"};"ma-single-pre-init"[]{'"ds";'"init";'"a";'"T";'"P"}} }

interactive nuprl_ma_single_pre_init_ma_single_init_compatible  {| intro [] |} :
   [wf] sequent  { <Gamma> >- '"a" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"init" in "fpf"[]{"Id"[]{};"x"."fpf-cap"[]{'"ds";"id-deq"[]{};'"x";"void"[]{}}} }  -->
   [wf] sequent  { <Gamma> >- '"x" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"t" in "univ"[level:l]{} }  -->
   [wf] sequent  { <Gamma> >- '"v" in '"t" }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";"fpf-single"[]{'"x";'"t"}} }  -->
   sequent  { <Gamma>; "assert"[]{"fpf-dom"[]{"id-deq"[]{};'"x";'"init"}}  >- "equal"[]{'"t";"fpf-ap"[]{'"init";"id-deq"[]{};'"x"};'"v"} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-pre-init"[]{'"ds";'"init";'"a";'"T";'"P"};"ma-single-init"[]{'"x";'"t";'"v"}} }

interactive nuprl_ma_single_init_ma_single_pre_init_compatible  {| intro [] |} :
   [wf] sequent  { <Gamma> >- '"a" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"init" in "fpf"[]{"Id"[]{};"x"."fpf-cap"[]{'"ds";"id-deq"[]{};'"x";"void"[]{}}} }  -->
   [wf] sequent  { <Gamma> >- '"x" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"t" in "univ"[level:l]{} }  -->
   [wf] sequent  { <Gamma> >- '"v" in '"t" }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";"fpf-single"[]{'"x";'"t"}} }  -->
   sequent  { <Gamma>; "assert"[]{"fpf-dom"[]{"id-deq"[]{};'"x";'"init"}}  >- "equal"[]{'"t";"fpf-ap"[]{'"init";"id-deq"[]{};'"x"};'"v"} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-init"[]{'"x";'"t";'"v"};"ma-single-pre-init"[]{'"ds";'"init";'"a";'"T";'"P"}} }

interactive nuprl_ma_single_pre_ma_single_sends_compatible  {| intro [] |} :
   [wf] sequent  { <Gamma> >- '"a" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent  { <Gamma> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"d1" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"da" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"f" in "list"[]{"prod"[]{"Id"[]{};"tg"."top"[]{}}} }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";'"d1"} }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Knd"[]{};"x"."univ"[level:l]{};"Kind-deq"[]{};"fpf-single"[]{"locl"[]{'"a"};'"T"};'"da"} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-pre"[]{'"ds";'"a";'"T";'"P"};"ma-single-sends"[]{'"d1";'"da";'"k";'"l";'"f"}} }

interactive nuprl_ma_single_sends_ma_single_pre_compatible  {| intro [] |} :
   [wf] sequent  { <Gamma> >- '"a" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent  { <Gamma> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"d1" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"da" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"f" in "list"[]{"prod"[]{"Id"[]{};"tg"."top"[]{}}} }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";'"d1"} }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Knd"[]{};"x"."univ"[level:l]{};"Kind-deq"[]{};"fpf-single"[]{"locl"[]{'"a"};'"T"};'"da"} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-sends"[]{'"d1";'"da";'"k";'"l";'"f"};"ma-single-pre"[]{'"ds";'"a";'"T";'"P"}} }

interactive nuprl_ma_single_pre_ma_single_effect_compatible  {| intro [] |} :
   [wf] sequent  { <Gamma> >- '"a" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent  { <Gamma> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"x" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"d1" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"da" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";'"d1"} }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Knd"[]{};"x"."univ"[level:l]{};"Kind-deq"[]{};"fpf-single"[]{"locl"[]{'"a"};'"T"};'"da"} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-pre"[]{'"ds";'"a";'"T";'"P"};"ma-single-effect"[]{'"d1";'"da";'"k";'"x";'"f"}} }

interactive nuprl_ma_single_effect_ma_single_pre_compatible  {| intro [] |} :
   [wf] sequent  { <Gamma> >- '"a" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent  { <Gamma> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"x" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"d1" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"da" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";'"d1"} }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Knd"[]{};"x"."univ"[level:l]{};"Kind-deq"[]{};"fpf-single"[]{"locl"[]{'"a"};'"T"};'"da"} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-effect"[]{'"d1";'"da";'"k";'"x";'"f"};"ma-single-pre"[]{'"ds";'"a";'"T";'"P"}} }

interactive nuprl_ma_single_pre_ma_single_sframe_compatible  {| intro [] |} :
   [wf] sequent  { <Gamma> >- '"a" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent  { <Gamma> >- '"ds" in "fpf"[]{"Id"[]{};"x"."top"[]{}} }  -->
   [wf] sequent  { <Gamma> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"tg" in "Id"[]{} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-pre"[]{'"ds";'"a";'"T";'"P"};"ma-single-sframe"[]{'"L";'"l";'"tg"}} }

interactive nuprl_ma_single_sframe_ma_single_pre_compatible  {| intro [] |} :
   [wf] sequent  { <Gamma> >- '"a" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent  { <Gamma> >- '"ds" in "fpf"[]{"Id"[]{};"x"."top"[]{}} }  -->
   [wf] sequent  { <Gamma> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"tg" in "Id"[]{} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-sframe"[]{'"L";'"l";'"tg"};"ma-single-pre"[]{'"ds";'"a";'"T";'"P"}} }

interactive nuprl_ma_single_pre_ma_single_frame_compatible  {| intro [] |} :
   [wf] sequent  { <Gamma> >- '"a" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent  { <Gamma> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"x" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"t" in "univ"[level:l]{} }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";"fpf-single"[]{'"x";'"t"}} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-pre"[]{'"ds";'"a";'"T";'"P"};"ma-single-frame"[]{'"L";'"t";'"x"}} }

interactive nuprl_ma_single_frame_ma_single_pre_compatible  {| intro [] |} :
   [wf] sequent  { <Gamma> >- '"a" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent  { <Gamma> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"x" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"t" in "univ"[level:l]{} }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";"fpf-single"[]{'"x";'"t"}} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-frame"[]{'"L";'"t";'"x"};"ma-single-pre"[]{'"ds";'"a";'"T";'"P"}} }

interactive nuprl_ma_single_pre_ma_single_init_compatible  {| intro [] |} :
   [wf] sequent  { <Gamma> >- '"a" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent  { <Gamma> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"x" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"t" in "univ"[level:l]{} }  -->
   [wf] sequent  { <Gamma> >- '"v" in '"t" }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";"fpf-single"[]{'"x";'"t"}} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-pre"[]{'"ds";'"a";'"T";'"P"};"ma-single-init"[]{'"x";'"t";'"v"}} }

interactive nuprl_ma_single_init_ma_single_pre_compatible  {| intro [] |} :
   [wf] sequent  { <Gamma> >- '"a" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"T" in "univ"[level:l]{} }  -->
   [wf] sequent  { <Gamma> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"x" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"t" in "univ"[level:l]{} }  -->
   [wf] sequent  { <Gamma> >- '"v" in '"t" }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";"fpf-single"[]{'"x";'"t"}} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-init"[]{'"x";'"t";'"v"};"ma-single-pre"[]{'"ds";'"a";'"T";'"P"}} }

interactive nuprl_ma_single_sends_ma_single_effect_compatible  {| intro [] |} :
   [wf] sequent  { <Gamma> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"da" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"f" in "list"[]{"prod"[]{"Id"[]{};"tg"."top"[]{}}} }  -->
   [wf] sequent  { <Gamma> >- '"x" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"k1" in "Knd"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"d1" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"d2" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";'"d1"} }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Knd"[]{};"x"."univ"[level:l]{};"Kind-deq"[]{};'"da";'"d2"} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-sends"[]{'"ds";'"da";'"k";'"l";'"f"};"ma-single-effect"[]{'"d1";'"d2";'"k1";'"x";'"f1"}} }

interactive nuprl_ma_single_effect_ma_single_sends_compatible  {| intro [] |} :
   [wf] sequent  { <Gamma> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"da" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"f" in "list"[]{"prod"[]{"Id"[]{};"tg"."top"[]{}}} }  -->
   [wf] sequent  { <Gamma> >- '"x" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"k1" in "Knd"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"d1" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"d2" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";'"d1"} }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Knd"[]{};"x"."univ"[level:l]{};"Kind-deq"[]{};'"da";'"d2"} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-effect"[]{'"d1";'"d2";'"k1";'"x";'"f1"};"ma-single-sends"[]{'"ds";'"da";'"k";'"l";'"f"}} }

interactive nuprl_ma_single_sends_ma_single_sframe_compatible  {| intro [] |} :
   [wf] sequent  { <Gamma> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"da" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"f" in "list"[]{"prod"[]{"Id"[]{};"tg"."top"[]{}}} }  -->
   [wf] sequent  { <Gamma> >- '"l1" in "IdLnk"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"L" in "list"[]{"Knd"[]{}} }  -->
   sequent  { <Gamma>; "equal"[]{"IdLnk"[]{};'"l";'"l1"} ; "mem"[]{'"tg";"map"[]{"lambda"[]{"p"."fst"[]{'"p"}};'"f"};"Id"[]{}}  >- "mem"[]{'"k";'"L";"Knd"[]{}} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-sends"[]{'"ds";'"da";'"k";'"l";'"f"};"ma-single-sframe"[]{'"L";'"l1";'"tg"}} }

interactive nuprl_ma_single_sframe_ma_single_sends_compatible  {| intro [] |} :
   [wf] sequent  { <Gamma> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"da" in "fpf"[]{"Knd"[]{};"a"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"f" in "list"[]{"prod"[]{"Id"[]{};"tg"."top"[]{}}} }  -->
   [wf] sequent  { <Gamma> >- '"l1" in "IdLnk"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"L" in "list"[]{"Knd"[]{}} }  -->
   sequent  { <Gamma>; "equal"[]{"IdLnk"[]{};'"l";'"l1"} ; "mem"[]{'"tg";"map"[]{"lambda"[]{"p"."fst"[]{'"p"}};'"f"};"Id"[]{}}  >- "mem"[]{'"k";'"L";"Knd"[]{}} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-sframe"[]{'"L";'"l1";'"tg"};"ma-single-sends"[]{'"ds";'"da";'"k";'"l";'"f"}} }

interactive nuprl_ma_single_sends_ma_single_frame_compatible  {| intro [] |} :
   [wf] sequent  { <Gamma> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"da" in "fpf"[]{"Knd"[]{};"a"."top"[]{}} }  -->
   [wf] sequent  { <Gamma> >- '"f" in "list"[]{"prod"[]{"Id"[]{};"tg"."top"[]{}}} }  -->
   [wf] sequent  { <Gamma> >- '"x" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"t" in "univ"[level:l]{} }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";"fpf-single"[]{'"x";'"t"}} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-sends"[]{'"ds";'"da";'"k";'"l";'"f"};"ma-single-frame"[]{'"L";'"t";'"x"}} }

interactive nuprl_ma_single_frame_ma_single_sends_compatible  {| intro [] |} :
   [wf] sequent  { <Gamma> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"da" in "fpf"[]{"Knd"[]{};"a"."top"[]{}} }  -->
   [wf] sequent  { <Gamma> >- '"f" in "list"[]{"prod"[]{"Id"[]{};"tg"."top"[]{}}} }  -->
   [wf] sequent  { <Gamma> >- '"x" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"t" in "univ"[level:l]{} }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";"fpf-single"[]{'"x";'"t"}} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-frame"[]{'"L";'"t";'"x"};"ma-single-sends"[]{'"ds";'"da";'"k";'"l";'"f"}} }

interactive nuprl_ma_single_sends_ma_single_init_compatible  {| intro [] |} :
   [wf] sequent  { <Gamma> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"da" in "fpf"[]{"Knd"[]{};"a"."top"[]{}} }  -->
   [wf] sequent  { <Gamma> >- '"f" in "list"[]{"prod"[]{"Id"[]{};"tg"."top"[]{}}} }  -->
   [wf] sequent  { <Gamma> >- '"x" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"t" in "univ"[level:l]{} }  -->
   [wf] sequent  { <Gamma> >- '"v" in '"t" }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";"fpf-single"[]{'"x";'"t"}} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-sends"[]{'"ds";'"da";'"k";'"l";'"f"};"ma-single-init"[]{'"x";'"t";'"v"}} }

interactive nuprl_ma_single_init_ma_single_sends_compatible  {| intro [] |} :
   [wf] sequent  { <Gamma> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"da" in "fpf"[]{"Knd"[]{};"a"."top"[]{}} }  -->
   [wf] sequent  { <Gamma> >- '"f" in "list"[]{"prod"[]{"Id"[]{};"tg"."top"[]{}}} }  -->
   [wf] sequent  { <Gamma> >- '"x" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"t" in "univ"[level:l]{} }  -->
   [wf] sequent  { <Gamma> >- '"v" in '"t" }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";"fpf-single"[]{'"x";'"t"}} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-init"[]{'"x";'"t";'"v"};"ma-single-sends"[]{'"ds";'"da";'"k";'"l";'"f"}} }

interactive nuprl_ma_single_effect_ma_single_sframe_compatible  {| intro [] |} :
   [wf] sequent  { <Gamma> >- '"x" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"ds" in "fpf"[]{"Id"[]{};"x"."top"[]{}} }  -->
   [wf] sequent  { <Gamma> >- '"da" in "fpf"[]{"Knd"[]{};"a"."top"[]{}} }  -->
   [wf] sequent  { <Gamma> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"tg" in "Id"[]{} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-effect"[]{'"ds";'"da";'"k";'"x";'"f"};"ma-single-sframe"[]{'"L";'"l";'"tg"}} }

interactive nuprl_ma_single_sframe_ma_single_effect_compatible  {| intro [] |} :
   [wf] sequent  { <Gamma> >- '"x" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"ds" in "fpf"[]{"Id"[]{};"x"."top"[]{}} }  -->
   [wf] sequent  { <Gamma> >- '"da" in "fpf"[]{"Knd"[]{};"a"."top"[]{}} }  -->
   [wf] sequent  { <Gamma> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"tg" in "Id"[]{} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-sframe"[]{'"L";'"l";'"tg"};"ma-single-effect"[]{'"ds";'"da";'"k";'"x";'"f"}} }

interactive nuprl_ma_single_effect_ma_single_frame_compatible  {| intro [] |} :
   [wf] sequent  { <Gamma> >- '"x" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"da" in "fpf"[]{"Knd"[]{};"a"."top"[]{}} }  -->
   [wf] sequent  { <Gamma> >- '"x1" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"L" in "list"[]{"Knd"[]{}} }  -->
   [wf] sequent  { <Gamma> >- '"t" in "univ"[level:l]{} }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";"fpf-single"[]{'"x1";'"t"}} }  -->
   sequent  { <Gamma>; "equal"[]{"Id"[]{};'"x";'"x1"}  >- "mem"[]{'"k";'"L";"Knd"[]{}} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-effect"[]{'"ds";'"da";'"k";'"x";'"f"};"ma-single-frame"[]{'"L";'"t";'"x1"}} }

interactive nuprl_ma_single_frame_ma_single_effect_compatible  {| intro [] |} :
   [wf] sequent  { <Gamma> >- '"x" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"da" in "fpf"[]{"Knd"[]{};"a"."top"[]{}} }  -->
   [wf] sequent  { <Gamma> >- '"x1" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"L" in "list"[]{"Knd"[]{}} }  -->
   [wf] sequent  { <Gamma> >- '"t" in "univ"[level:l]{} }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";"fpf-single"[]{'"x1";'"t"}} }  -->
   sequent  { <Gamma>; "equal"[]{"Id"[]{};'"x";'"x1"}  >- "mem"[]{'"k";'"L";"Knd"[]{}} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-frame"[]{'"L";'"t";'"x1"};"ma-single-effect"[]{'"ds";'"da";'"k";'"x";'"f"}} }

interactive nuprl_ma_single_effect_ma_single_init_compatible  {| intro [] |} :
   [wf] sequent  { <Gamma> >- '"x" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"da" in "fpf"[]{"Knd"[]{};"a"."top"[]{}} }  -->
   [wf] sequent  { <Gamma> >- '"x1" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"t" in "univ"[level:l]{} }  -->
   [wf] sequent  { <Gamma> >- '"v" in '"t" }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";"fpf-single"[]{'"x1";'"t"}} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-effect"[]{'"ds";'"da";'"k";'"x";'"f"};"ma-single-init"[]{'"x1";'"t";'"v"}} }

interactive nuprl_ma_single_init_ma_single_effect_compatible  {| intro [] |} :
   [wf] sequent  { <Gamma> >- '"x" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"k" in "Knd"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"ds" in "fpf"[]{"Id"[]{};"x"."univ"[level:l]{}} }  -->
   [wf] sequent  { <Gamma> >- '"da" in "fpf"[]{"Knd"[]{};"a"."top"[]{}} }  -->
   [wf] sequent  { <Gamma> >- '"x1" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"t" in "univ"[level:l]{} }  -->
   [wf] sequent  { <Gamma> >- '"v" in '"t" }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};'"ds";"fpf-single"[]{'"x1";'"t"}} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-init"[]{'"x1";'"t";'"v"};"ma-single-effect"[]{'"ds";'"da";'"k";'"x";'"f"}} }

interactive nuprl_ma_single_sframe_ma_single_frame_compatible  {| intro [] |} :
   [wf] sequent  { <Gamma> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"x" in "Id"[]{} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-sframe"[]{'"L";'"l";'"tg"};"ma-single-frame"[]{'"L1";'"t";'"x"}} }

interactive nuprl_ma_single_frame_ma_single_sframe_compatible  {| intro [] |} :
   [wf] sequent  { <Gamma> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"x" in "Id"[]{} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-frame"[]{'"L1";'"t";'"x"};"ma-single-sframe"[]{'"L";'"l";'"tg"}} }

interactive nuprl_ma_single_sframe_ma_single_init_compatible  {| intro [] |} :
   [wf] sequent  { <Gamma> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"x" in "Id"[]{} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-sframe"[]{'"L";'"l";'"tg"};"ma-single-init"[]{'"x";'"t";'"v"}} }

interactive nuprl_ma_single_init_ma_single_sframe_compatible  {| intro [] |} :
   [wf] sequent  { <Gamma> >- '"l" in "IdLnk"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"tg" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"x" in "Id"[]{} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-init"[]{'"x";'"t";'"v"};"ma-single-sframe"[]{'"L";'"l";'"tg"}} }

interactive nuprl_ma_single_frame_ma_single_init_compatible  {| intro [] |} :
   [wf] sequent  { <Gamma> >- '"x" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"t" in "univ"[level:l]{} }  -->
   [wf] sequent  { <Gamma> >- '"x1" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"t1" in "univ"[level:l]{} }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};"fpf-single"[]{'"x";'"t"};"fpf-single"[]{'"x1";'"t1"}} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-frame"[]{'"L";'"t";'"x"};"ma-single-init"[]{'"x1";'"t1";'"v"}} }

interactive nuprl_ma_single_init_ma_single_frame_compatible  {| intro [] |} :
   [wf] sequent  { <Gamma> >- '"x" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"t" in "univ"[level:l]{} }  -->
   [wf] sequent  { <Gamma> >- '"x1" in "Id"[]{} }  -->
   [wf] sequent  { <Gamma> >- '"t1" in "univ"[level:l]{} }  -->
   sequent  { <Gamma> >- "fpf-compatible"[]{"Id"[]{};"x"."univ"[level:l]{};"id-deq"[]{};"fpf-single"[]{'"x";'"t"};"fpf-single"[]{'"x1";'"t1"}} }  -->
   sequent  { <Gamma> >- "ma-compat"[level:l]{"ma-single-init"[]{'"x1";'"t1";'"v"};"ma-single-frame"[]{'"L";'"t";'"x"}} }


