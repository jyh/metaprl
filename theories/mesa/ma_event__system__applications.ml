extends Nuprl_event__system__applications

open Dtactic


interactive nuprl_rset_wf {|intro[] |}   :
   sequent  { <Gamma> >- 'a in Id }  -->
   sequent  { <Gamma> >- "assert"[]{"apply"[]{'"R";'"a"}} }  -->
   sequent  { <Gamma> >- 'a in  "rset"[]{'"R"}  }
