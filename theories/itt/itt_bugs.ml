include Itt_theory
open Base_meta

open Tactic_type.Conversionals


define unfold_label : label[t:t] <--> 17

define unfold_eq_label : eq_label[x:t,y:t]{'A;'B} <-->  meta_eq{label[x:t]; label[y:t]; 'A; 'B}

let reduce_eq_labelC = unfold_eq_label thenC reduce_meta_eq

let resource reduce += [<< eq_label[x:t,y:t]{'A;'B}  >>, reduce_eq_labelC;
                        << meta_eq{label[x:t]; label[y:t]; 'A; 'B}  >>, reduce_meta_eq]

interactive bug1 'H:
   sequent['ext] {'H >- 1 ~ 0 }


