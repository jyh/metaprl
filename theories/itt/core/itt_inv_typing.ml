extends Itt_disect
extends Itt_prod
extends Itt_dfun

open Itt_struct

open Dtactic

prim dintersectionTypeElimination {| elim [ThinOption thinT] |} 'H 'a :
   [wf] sequent { <H>; u:"type"{bisect{'A; x. 'B['x]}}; <J['u]>  >- 'a in 'A } -->
   ('t['u;'v] :
   sequent { <H>; u:"type"{bisect{'A; x. 'B['x]}}; v:"type"{'B['a]}; <J['u]> >- 'C['u] }) -->
   sequent { <H>; u:"type"{bisect{'A; x. 'B['x]}}; <J['u]> >- 'C['u] } =
   't['u;it]

prim independentProductTypeElimination {| elim [ThinOption thinT] |} 'H :
   ('t['u;'v;'w] :
   sequent { <H>; u:"type"{'A * 'B}; v:"type"{'A}; w:"type"{'B}; <J['u]> >- 'C['u] }) -->
   sequent { <H>; u:"type"{'A * 'B}; <J['u]> >- 'C['u] } =
   't['u;it;it]

prim functionTypeElimination {| elim [ThinOption thinT] |} 'H :
   ('t['u;'v; 'w] :
   sequent { <H>; u:"type"{'A -> 'B }; v:"type"{'A}; w:('A -> "type"{'B}); <J['u]> >- 'C['u] }) -->
   sequent { <H>; u:"type"{'A -> 'B }; <J['u]> >- 'C['u] } =
   't['u;it;it]

