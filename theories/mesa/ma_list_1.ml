extends Nuprl_list_1

open Dtactic
open Top_conversionals
open Mp_resource

interactive_rw map_cons_reduce {| reduce |} :
      map{'f;'h::'t} <--> ( ('f 'h) :: map{'f;'t} )

interactive_rw map_nil_reduce {| reduce |} :
      map{'f;nil} <--> nil

let resource reduce +=
   [ <<map{'f;'h::'t}>>,  map_cons_reduce;
     <<map{'f;nil}>>,  map_nil_reduce]




