extends Nuprl_core_2

open Dtactic
open Mp_resource


interactive_rw beta2 : (lambda{x,y.'f['x;'y]} 'a 'b) <--> 'f['a;'b]


let resource reduce += <<lambda{x,y.'f['x;'y]} 'a 'b>>, beta2


