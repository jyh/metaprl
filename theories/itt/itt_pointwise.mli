extends Itt_equal

rule contextSubstPointwise 'H 'J_1 'J 't1  :
   [equality] sequent { <H>; t:'T; <J_1['t]>;  <J['t]>; <J_2['t]> >- 't = 't1 in 'T } -->
   [main]  sequent { <H>; t:'T; <J_1['t]>;  <J['t1]>; <J_2['t]> >- 'C['t] } -->
   sequent { <H>; t:'T; <J_1['t]>;  <J['t]>; <J_2['t]> >- 'C['t] }
