extends Nuprl_event__systems
open Dtactic
open Auto_tactic
open Refiner.Refiner.Term
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError

open Tactic_type
open Tactic_type.Tacticals
open Top_tacticals
open Top_conversionals
open Var
open Typeinf



interactive alle_at_pred {| intro[SelectOption 2] |} event_system[level:l] bind{e.'P['e]} :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H>; e: "set"[]{"es-E"[]{'"es"};"e"."equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"}}  >- "type"{'"P"['"e"]} }  -->
   sequent { <H> >- ("alle-at"[]{'es;'i;e. 'P['e]} ) } -->
   sequent { <H> >- ("alle-at"[]{'es;'i;e.not{"assert"{"es-first"{'es;'e}}} => 'P["es-pred"{'es;'e}]} ) }


let alle_at_predT = funT
 (fun p ->
     let concl = Sequent.concl p in
     match explode_term concl with <<"alle-at"[]{'es; 'i; e.'impl}>> ->(
     match explode_term impl with <<'left => 'prop>> ->
     let pred_e = <:con<"es-pred"{$es$;$mk_var_term e$}>> in
     let bind = var_subs_to_bing prop pred_e in
     let es_type =  infer_type p es in
        alle_at_pred es_type  bind
     | _ -> failT )| _ -> failT
 )

let resource intro += (<< ("alle-at"[]{'es;'i;e.not{"assert"{"es-first"{'es;'e}}} => 'P["es-pred"{'es;'e}]} )>>, wrap_intro alle_at_predT)


interactive_rw es__after__pred_rw :
    "es-when"[]{'"es";'"x";'"e"} <-->  "es-after"[]{'"es";'"x";"es-pred"[]{'"es";'"e"}}



interactive nuprl_alle__at__ind {| intro[SelectOption 1; intro_typeinf <<'es>>] |} event_system[level:l]   :
   [wf] sequent { <H> >- '"es" in "event_system"[level:l]{} }  -->
   [wf] sequent { <H> >- '"i" in "Id"[]{} }  -->
   [wf] sequent { <H>;"x": "set"[]{"es-E"[]{'"es"};"e"."equal"[]{"Id"[]{};"es-loc"[]{'"es";'"e"};'"i"}} >- '"P"['"x"] in "univ"[level:l]{} }  -->
   sequent { <H> >- "alle-at"[]{'"es";'"i";"e"."implies"[]{"assert"[]{"es-first"[]{'"es";'"e"}};'"P"['"e"]}} } -->
   sequent { <H> >- "alle-at"[]{'"es";'"i";"e"."implies"[]{"not"[]{"assert"[]{"es-first"[]{'"es";'"e"}}};"implies"[]{'"P"["es-pred"[]{'"es";'"e"}];'"P"['"e"]}}} } -->
   sequent { <H> >- "alle-at"[]{'"es";'"i";"e".'"P"['"e"]} }

let es_invariantT =  selT 1 (dT 0) thenLT [autoT;autoT;autoT;idT; rw (addrC[2;1;1] (higherC es__after__pred_rw)) 0 thenT  alle_at_predT]
