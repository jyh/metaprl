extends Itt_equal

rule contextSubstPointwise 'H 'J_1 'J 'J_2 't1  :
   [equality] sequent ['ext] { 'H; t:'T; 'J_1['t];  'J['t]; 'J_2['t] >- 't = 't1 in 'T } -->
   [main]  sequent ['ext] { 'H; t:'T; 'J_1['t];  'J['t1]; 'J_2['t] >- 'C['t] } -->
   sequent ['ext] { 'H; t:'T; 'J_1['t];  'J['t]; 'J_2['t] >- 'C['t] }
