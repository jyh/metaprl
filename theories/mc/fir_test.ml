(*****************************************************
 * Start of FIR program output from compiler.
 * Output stage: after front end
 *****************************************************)

include Mc_theory

interactive program1 'H :

(*
 * Program imports.
 *)

(*


*)

(*
 * Program exports.
 *)

(*

naml_main_00541 = init : tyFun{
   cons{ tyFun{
         cons{ tyInt;
         nil}; tyEnum{(0)}};
   nil}; tyEnum{(0)}}

*)

(* Begin final sequent. *)

sequent ['ext] { 'H >-
fix{ g. lambda{f.
(* Program types. *)
   ifthenelse{ eq_atom{'f; token["fini_00535":t]};
      unknownTydef (* TyDefLambda *);
   ifthenelse{ eq_atom{'f; token["exn_00536":t]};
      unknownTydef (* TyDefUnion *);
(* Program globals. *)
(* Program functions. *)
   ifthenelse{ eq_atom{'f; token["f_00537":t]};
(*
tyAll{
   cons{ 'b_00545;
   nil}; tyFun{
      cons{ tyInt;
      cons{ tyExists{
            cons{ 'a_00546;
            nil}; tyTuple{
               cons{ tyVar{'a_00546};
               cons{ tyFun{
                     cons{ tyVar{'a_00546};
                     cons{ tyUnion{ apply{'g; token["exn_00536":t]};
                           nil; int_set{cons{interval{(-1073741824); (1073741823)}; nil}}};
                     nil}}; tyEnum{(0)}};
               nil}}}};
      cons{ tyExists{
            cons{ 'a_00547;
            nil}; tyTuple{
               cons{ tyVar{'a_00547};
               cons{ tyFun{
                     cons{ tyVar{'a_00547};
                     cons{ tyExists{
                           cons{ 'a_00548;
                           nil}; tyTuple{
                              cons{ tyVar{'a_00548};
                              cons{ tyFun{
                                    cons{ tyVar{'a_00548};
                                    cons{ tyInt;
                                    cons{ tyExists{
                                          cons{ 'a_00549;
                                          nil}; tyTuple{
                                             cons{ tyVar{'a_00549};
                                             cons{ tyFun{
                                                   cons{ tyVar{'a_00549};
                                                   cons{ tyUnion{ apply{'g; token["exn_00536":t]};
                                                         nil; int_set{cons{interval{(-1073741824); (1073741823)}; nil}}};
                                                   nil}}; tyEnum{(0)}};
                                             nil}}}};
                                    cons{ tyExists{
                                          cons{ 'a_00550;
                                          nil}; tyTuple{
                                             cons{ tyVar{'a_00550};
                                             cons{ tyFun{
                                                   cons{ tyVar{'a_00550};
                                                   cons{ tyVar{'b_00545};
                                                   nil}}; tyEnum{(0)}};
                                             nil}}}};
                                    nil}}}}; tyEnum{(0)}};
                              nil}}}};
                     nil}}; tyEnum{(0)}};
               nil}}}};
      nil}}}; tyEnum{(0)}}};
*)
      lambda{x_00551. lambda{exnh_00552. lambda{cont_00553.
         letAlloc{ allocTuple{tyDelayed;
            cons{ atomVar{'x_00551};
            cons{ atomVar{apply{'g; token["fun_00544":t]}};
            nil}}}; fun_00554.
         letSubscript{ blockPolySub; tyDelayed; 'cont_00553; atomInt{(0)}; cl_env_00555.
         letSubscript{ blockPolySub; tyDelayed; 'cont_00553; atomInt{(1)}; cl_fun_00556.
         apply{apply{'cl_fun_00556; atomVar{'cl_env_00555}}; atomVar{'fun_00554}}}}}}}};
   ifthenelse{ eq_atom{'f; token["fun_00538":t]};
(*
tyAll{
   cons{ 'b_00557;
   nil}; tyFun{
      cons{ tyInt;
      cons{ tyInt;
      cons{ tyExists{
            cons{ 'a_00558;
            nil}; tyTuple{
               cons{ tyVar{'a_00558};
               cons{ tyFun{
                     cons{ tyVar{'a_00558};
                     cons{ tyUnion{ apply{'g; token["exn_00536":t]};
                           nil; int_set{cons{interval{(-1073741824); (1073741823)}; nil}}};
                     nil}}; tyEnum{(0)}};
               nil}}}};
      cons{ tyExists{
            cons{ 'a_00559;
            nil}; tyTuple{
               cons{ tyVar{'a_00559};
               cons{ tyFun{
                     cons{ tyVar{'a_00559};
                     cons{ tyVar{'b_00557};
                     nil}}; tyEnum{(0)}};
               nil}}}};
      nil}}}}; tyEnum{(0)}}};
*)
      lambda{x_00560. lambda{x_00561. lambda{exnh_00562. lambda{cont_00563.
         letBinop{ plusIntOp; tyInt; atomVar{'x_00560}; atomVar{'x_00561}; r_00564.
         letBinop{ plusIntOp; tyInt; atomVar{'x_00560}; atomVar{'x_00561}; r_00565.
         letAlloc{ allocTuple{tyDelayed;
            cons{ atomVar{'r_00565};
            cons{ atomVar{'exnh_00562};
            cons{ atomVar{'cont_00563};
            nil}}}}; env_00566.
         letAlloc{ allocTuple{tyDelayed;
            cons{ atomVar{'env_00566};
            cons{ atomVar{apply{'g; token["f_00543":t]}};
            nil}}}; f_00567.
         apply{apply{apply{apply{'g; token["f_00537":t]}; atomVar{'r_00564}}; atomVar{'exnh_00562}}; atomVar{'f_00567}}}}}}}}}};
   ifthenelse{ eq_atom{'f; token["exnh_00539":t]};
(*
tyFun{
   cons{ tyFun{
         cons{ tyInt;
         nil}; tyEnum{(0)}};
   cons{ tyUnion{ apply{'g; token["exn_00536":t]};
         nil; int_set{cons{interval{(-1073741824); (1073741823)}; nil}}};
   nil}}; tyEnum{(0)}};
*)
      lambda{fini_00568. lambda{e_00569.
         apply{'fini_00568; atomInt{(1)}}}};
   ifthenelse{ eq_atom{'f; token["f_00540":t]};
(*
tyAll{
   cons{ 'b_00570;
   nil}; tyFun{
      cons{ tyInt;
      cons{ tyExists{
            cons{ 'a_00571;
            nil}; tyTuple{
               cons{ tyVar{'a_00571};
               cons{ tyFun{
                     cons{ tyVar{'a_00571};
                     cons{ tyUnion{ apply{'g; token["exn_00536":t]};
                           nil; int_set{cons{interval{(-1073741824); (1073741823)}; nil}}};
                     nil}}; tyEnum{(0)}};
               nil}}}};
      cons{ tyExists{
            cons{ 'a_00572;
            nil}; tyTuple{
               cons{ tyVar{'a_00572};
               cons{ tyFun{
                     cons{ tyVar{'a_00572};
                     cons{ tyVar{'b_00570};
                     nil}}; tyEnum{(0)}};
               nil}}}};
      cons{ tyExists{
            cons{ 'a_00573;
            nil}; tyTuple{
               cons{ tyVar{'a_00573};
               cons{ tyFun{
                     cons{ tyVar{'a_00573};
                     cons{ tyInt;
                     cons{ tyExists{
                           cons{ 'a_00574;
                           nil}; tyTuple{
                              cons{ tyVar{'a_00574};
                              cons{ tyFun{
                                    cons{ tyVar{'a_00574};
                                    cons{ tyUnion{ apply{'g; token["exn_00536":t]};
                                          nil; int_set{cons{interval{(-1073741824); (1073741823)}; nil}}};
                                    nil}}; tyEnum{(0)}};
                              nil}}}};
                     cons{ tyExists{
                           cons{ 'a_00575;
                           nil}; tyTuple{
                              cons{ tyVar{'a_00575};
                              cons{ tyFun{
                                    cons{ tyVar{'a_00575};
                                    cons{ tyVar{'b_00570};
                                    nil}}; tyEnum{(0)}};
                              nil}}}};
                     nil}}}}; tyEnum{(0)}};
               nil}}}};
      nil}}}}; tyEnum{(0)}}};
*)
      lambda{r_00576. lambda{exnh_00577. lambda{cont_00578. lambda{f_00579.
         letSubscript{ blockPolySub; tyDelayed; 'f_00579; atomInt{(0)}; cl_env_00580.
         letSubscript{ blockPolySub; tyDelayed; 'f_00579; atomInt{(1)}; cl_fun_00581.
         apply{apply{apply{apply{'cl_fun_00581; atomVar{'cl_env_00580}}; atomVar{'r_00576}}; atomVar{'exnh_00577}}; atomVar{'cont_00578}}}}}}}};
   ifthenelse{ eq_atom{'f; token["naml_main_00541":t]};
(*
tyFun{
   cons{ tyFun{
         cons{ tyInt;
         nil}; tyEnum{(0)}};
   nil}; tyEnum{(0)}};
*)
      lambda{fini_00582.
         letAlloc{ allocTuple{tyDelayed;
            cons{ atomVar{'fini_00582};
            cons{ atomVar{apply{'g; token["exnh_00542":t]}};
            nil}}}; exnh_00583.
         apply{'fini_00582; atomInt{(0)}}}};
   ifthenelse{ eq_atom{'f; token["exnh_00542":t]};
(*
tyFun{
   cons{ tyFun{
         cons{ tyInt;
         nil}; tyEnum{(0)}};
   cons{ tyUnion{ apply{'g; token["exn_00536":t]};
         nil; int_set{cons{interval{(-1073741824); (1073741823)}; nil}}};
   nil}}; tyEnum{(0)}};
*)
      lambda{env_00584. lambda{a_00585.
         apply{apply{apply{'g; token["exnh_00539":t]}; atomVar{'env_00584}}; atomVar{'a_00585}}}};
   ifthenelse{ eq_atom{'f; token["f_00543":t]};
(*
tyAll{
   cons{ 'b_00586;
   nil}; tyFun{
      cons{ tyTuple{
            cons{ tyInt;
            cons{ tyExists{
                  cons{ 'a_00587;
                  nil}; tyTuple{
                     cons{ tyVar{'a_00587};
                     cons{ tyFun{
                           cons{ tyVar{'a_00587};
                           cons{ tyUnion{ apply{'g; token["exn_00536":t]};
                                 nil; int_set{cons{interval{(-1073741824); (1073741823)}; nil}}};
                           nil}}; tyEnum{(0)}};
                     nil}}}};
            cons{ tyExists{
                  cons{ 'a_00588;
                  nil}; tyTuple{
                     cons{ tyVar{'a_00588};
                     cons{ tyFun{
                           cons{ tyVar{'a_00588};
                           cons{ tyVar{'b_00586};
                           nil}}; tyEnum{(0)}};
                     nil}}}};
            nil}}}};
      cons{ tyExists{
            cons{ 'a_00589;
            nil}; tyTuple{
               cons{ tyVar{'a_00589};
               cons{ tyFun{
                     cons{ tyVar{'a_00589};
                     cons{ tyInt;
                     cons{ tyExists{
                           cons{ 'a_00590;
                           nil}; tyTuple{
                              cons{ tyVar{'a_00590};
                              cons{ tyFun{
                                    cons{ tyVar{'a_00590};
                                    cons{ tyUnion{ apply{'g; token["exn_00536":t]};
                                          nil; int_set{cons{interval{(-1073741824); (1073741823)}; nil}}};
                                    nil}}; tyEnum{(0)}};
                              nil}}}};
                     cons{ tyExists{
                           cons{ 'a_00591;
                           nil}; tyTuple{
                              cons{ tyVar{'a_00591};
                              cons{ tyFun{
                                    cons{ tyVar{'a_00591};
                                    cons{ tyVar{'b_00586};
                                    nil}}; tyEnum{(0)}};
                              nil}}}};
                     nil}}}}; tyEnum{(0)}};
               nil}}}};
      nil}}; tyEnum{(0)}}};
*)
      lambda{env_00592. lambda{a_00593.
         letSubscript{ blockPolySub; tyDelayed; 'env_00592; atomInt{(0)}; a_00594.
         letSubscript{ blockPolySub; tyDelayed; 'env_00592; atomInt{(1)}; a_00595.
         letSubscript{ blockPolySub; tyDelayed; 'env_00592; atomInt{(2)}; a_00596.
         apply{apply{apply{apply{apply{'g; token["f_00540":t]}; atomVar{'a_00594}}; atomVar{'a_00595}}; atomVar{'a_00596}}; atomVar{'a_00593}}}}}}};
   ifthenelse{ eq_atom{'f; token["fun_00544":t]};
(*
tyAll{
   cons{ 'b_00597;
   nil}; tyFun{
      cons{ tyInt;
      cons{ tyInt;
      cons{ tyExists{
            cons{ 'a_00598;
            nil}; tyTuple{
               cons{ tyVar{'a_00598};
               cons{ tyFun{
                     cons{ tyVar{'a_00598};
                     cons{ tyUnion{ apply{'g; token["exn_00536":t]};
                           nil; int_set{cons{interval{(-1073741824); (1073741823)}; nil}}};
                     nil}}; tyEnum{(0)}};
               nil}}}};
      cons{ tyExists{
            cons{ 'a_00599;
            nil}; tyTuple{
               cons{ tyVar{'a_00599};
               cons{ tyFun{
                     cons{ tyVar{'a_00599};
                     cons{ tyVar{'b_00597};
                     nil}}; tyEnum{(0)}};
               nil}}}};
      nil}}}}; tyEnum{(0)}}};
*)
      lambda{env_00600. lambda{a_00601. lambda{exnh_00602. lambda{cont_00603.
         apply{apply{apply{apply{apply{'g; token["fun_00538":t]}; atomVar{'env_00600}}; atomVar{'a_00601}}; atomVar{'exnh_00602}}; atomVar{'cont_00603}}}}}};
   unknownFun }}}}}}}}}}}} (* fix term and contents ended *)

} (* end final sequent *)

(* end theorem: program1 *)

(*****************************************************
 * End of FIR program output from compiler.
 *****************************************************)
(*****************************************************
 * Start of FIR program output from compiler.
 * Output stage: optimized
 *****************************************************)

include Mc_theory

interactive program2 'H :

(*
 * Program imports.
 *)

(*


*)

(*
 * Program exports.
 *)

(*

naml_main_00610 = init : tyFun{
   cons{ tyFun{
         cons{ tyInt;
         nil}; tyEnum{(0)}};
   nil}; tyEnum{(0)}}

*)

(* Begin final sequent. *)

sequent ['ext] { 'H >-
fix{ g. lambda{f.
(* Program types. *)
(* Program globals. *)
(* Program functions. *)
   ifthenelse{ eq_atom{'f; token["naml_main_00610":t]};
(*
tyFun{
   cons{ tyFun{
         cons{ tyInt;
         nil}; tyEnum{(0)}};
   nil}; tyEnum{(0)}};
*)
      lambda{fini_00651.
         apply{'fini_00651; atomInt{(0)}}};
   unknownFun }}} (* fix term and contents ended *)

} (* end final sequent *)

(* end theorem: program2 *)

(*****************************************************
 * End of FIR program output from compiler.
 *****************************************************)
