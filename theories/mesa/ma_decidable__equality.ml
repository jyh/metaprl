extends Nuprl_decidable__equality

open Itt_fun

open Lm_printf
open Unify_mm
open Basic_tactics

interactive nuprl_eq_id_self  {| intro [] |} :
   [wf] sequent  { <Gamma> >- '"a" in "Id"[]{} }  -->
   sequent  { <Gamma> >- "assert"{"eq_id"[]{'"a";'"a"}} }


interactive_rw nuprl_id_deq_self {| reduce |} :
   ( '"a" in "Id"[]{} ) -->
   (eqof{."id-deq"} '"a" '"a") <--> btrue


interactive nuprl_eqof_wf {|intro[] |}   :
   [wf] sequent  { <Gamma> >- "type"{'"T"} }  -->
   [wf] sequent  { <Gamma> >- '"d" in "deq"[]{'"T"} }  -->
   sequent  { <Gamma> >- ("eqof"[]{'"d"} in "fun"[]{'"T";"fun"[]{'"T";"bool"[]{}}}) }


let inf_eqof inf consts decls eqs opt_eqs defs t =
   let a = dest_dep0_term (opname_of_term t) t in (* HACK should be easier way *)
   let eqs', opt_eqs', defs', dec_x = inf consts decls eqs opt_eqs defs a in
   let x =  dest_dep0_term (opname_of_term dec_x) dec_x in  (* HACK should be easier way *)
      eqs', opt_eqs', defs', mk_fun_term x (mk_fun_term x <<bool>>)


let resource typeinf += [<<"id-deq">>, infer_const <<"deq"[]{"Id"}>>;
                         <<eqof{'a}>>, inf_eqof]
