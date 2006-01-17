extends Itt_record_label0
extends Itt_nequal

open Basic_tactics

open Base_meta
open Itt_squiggle
open Itt_struct
open Itt_equal

(******************)
(*  Defenitions   *)
(******************)

(**** label ****)

declare label[t:t]

prim labelMember {| intro [] |} :
   sequent { <H> >- label[t:t] in label } =
   it

let label_term = << label[x:t] >>
let label_opname = opname_of_term label_term
let is_label_term = TermOp.is_string_term label_opname
let dest_label = TermOp.dest_string_term label_opname
let mk_label_term = TermOp.mk_string_term label_opname

(**** equality ****)

define unfold_eq_label : eq_label[x:t,y:t]{'A;'B} <-->  meta_eq[x:t, y:t]{'A; 'B}

(******************)
(*   Rules        *)
(******************)

prim reduce_eq_label_true {| intro [] |} :
   sequent{ <H> >- label[x:t] = label[y:t]  in label} -->
   sequent{ <H> >- eq_label[x:t,y:t]{'A;'B} ~ 'A}
      = it

prim reduce_eq_label_false {| intro [] |} :
   sequent{ <H> >- label[x:t] <> label[y:t]  in label} -->
   sequent{ <H> >- eq_label[x:t,y:t]{'A;'B} ~ 'B}
      = it

interactive_rw reduce_eq_label_true_rw label[x:t] label[y:t] :
   (label[x:t] = label[y:t]  in label) -->
   eq_label[x:t,y:t]{'A;'B} <--> 'A

interactive_rw reduce_eq_label_false_rw label[x:t]  label[y:t] :
   (label[x:t] <> label[y:t]  in label) -->
   eq_label[x:t,y:t]{'A;'B} <--> 'B

let eq_label_elimT = argfunT (fun n p ->
   let t = Sequent.nth_hyp p n in
   match explode_term t with
         <<'x='y in 'label>> ->   tryT (progressT (rwAll (sweepDnC (reduce_eq_label_true_rw x y orelseC reduce_eq_label_true_rw y x))) thenAT autoT)
                                  thenT sqSubstT <:con<"rewrite"{$x$ ; $y$}>> 0 thenAT  (Itt_record_label0.label_sqequal thenT hypothesis n) |
          _ -> failT
)

let neq_label_elimT = argfunT (fun n p ->
   let t = Sequent.nth_hyp p n in
   match explode_term t with
         <<'x<>'y in 'label>> ->  progressT (rwAll  (sweepDnC (reduce_eq_label_false_rw x y orelseC reduce_eq_label_false_rw y x))) thenAT autoT |
          _ ->  (raise (RefineError ("neqelimT", StringTermError (" a term: ", t))))
)


let resource elim +=
  [ << label[x:t] = label[y:t] in label >>, eq_label_elimT;
    << label[x:t] <> label[y:t] in label >>, neq_label_elimT ]


interactive_rw reduce_eq_label_trivial_rw :
      eq_label[x:t,x:t]{'A;'B} <--> 'A

let reduce_eq_label =  reduce_eq_label_trivial_rw orelseC
                       (unfold_eq_label thenC reduce_meta_eq_tok)

let resource reduce += << eq_label[x:t,y:t]{'A;'B}  >>, wrap_reduce reduce_eq_label



interactive eq_label_false :
   sequent{ <H> >- label[x:t] <> label[y:t]  in label} -->
   sequent{ <H> >- 'B} -->
   sequent{ <H> >- eq_label[x:t,y:t]{'A;'B}}

interactive eq_label_true :
   sequent{ <H> >- 'A} -->
   sequent{ <H> >- eq_label[x:t,x:t]{'A;'B}}

let eq_labelIntroT =
   rw reduce_eq_label 0 orelseT eq_label_false

let resource intro += (<< eq_label[x:t,y:t]{'A;'B} >>, wrap_intro eq_labelIntroT )

interactive not_eq_label :
   sequent{ <H> >- eq_label[x:t,y:t]{"false"; "true"} } -->
   sequent{ <H> >- label[x:t] <> label[y:t]  in label}

let not_eq_labelT =
   (not_eq_label thenT rw reduce_eq_label 0 thenT tryT (dT 0))  orelseT  Itt_nequal.triv_nequalT orelseT trivialT

let resource intro +=
   (<< label[x:t] <> label[y:t]  in label>>, wrap_intro not_eq_labelT )

(******************)
(*   Tactic       *)
(******************)

let decideEqLabelT x y =
   Itt_record_label0.decide_eq_label x y
      thenLT [tryT (dT 0);
              tryT (dT 0);
              tryT (dT (-1));
              tryT (dT (-1));
             ]

(******************)
(*  Display Forms *)
(******************)

dform label_df_tex : except_mode[src] :: label[t:t] =  tt{ slot[t:t]}

declare eq_label[x:t,y:t]

dform eq_label2_df : eq_label[x:t,y:t] =  label[x:t] space `"=" space  label[y:t]

dform eq_label_df : except_mode[src] ::
   eq_label[x:t,y:t]{'A;'B} = ifthenelse{eq_label[x:t,y:t];'A;'B}

