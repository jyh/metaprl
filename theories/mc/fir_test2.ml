(*****************************************************
 * Start of FIR program output from compiler.
 * Output stage: after front end
 *****************************************************)

include Mc_theory

interactive program_1 'H :

(*
 * Program imports.
 *)

(*


*)

(*
 * Program exports.
 *)

(*

naml_main_00510 = init : tyFun{
   cons{ tyFun{
         cons{ tyInt;
         nil}; tyEnum{(0)}};
   nil}; tyEnum{(0)}}

*)

(*
 * Program types.
 *)

(*

fini_00505 = tyDefLambda{
   nil; tyFun{
   cons{ tyInt;
   nil}; tyEnum{(0)}}}
exn_00506 = it (* TyDefUnion *)
bleh_00507 = it (* TyDefUnion *)

*)

(*
 * Program globals.
 *)

(*


*)

(*
 * Begin final sequent.
 *)

sequent ['ext] { 'H >-
fix{ g.
   ifthenelse{ eq_atom{'g; token["exnh_00509":t]};
      lambda{fini_00512. lambda{e_00513.
         tailCall{ 'fini_00512;
            cons{ atomInt{(1)};
            nil}
         } (* end tailCall *)
      }};
   ifthenelse{ eq_atom{'g; token["naml_main_00510":t]};
      lambda{fini_00514.
         letAlloc{ allocTuple{tyDelayed;
            cons{ atomVar{'fini_00514};
            cons{ atomVar{'exnh_00511};
            nil}}}; exnh_00515.
         letAlloc{ it (* AllocUnion *); c_00516.
         letSubscript{ blockPolySub; tyInt; 'c_00516; atomInt{(0)}; x_00517.
         letExt{ tyEnum{(1)}; token["ml_print_int":t]; tyFun{
            cons{ tyInt;
            nil}; tyEnum{(1)}};
            cons{ atomVar{'x_00517};
            nil}; r_00518.
         letAlloc{ allocArray{tyArray{tyEnum{(256)}};
            cons{ atomEnum{(256); (10)};
            cons{ atomEnum{(256); (0)};
            nil}}}; array_00519.
         letExt{ tyEnum{(1)}; token["ml_print_string":t]; tyFun{
            cons{ tyArray{tyEnum{(256)}};
            nil}; tyEnum{(1)}};
            cons{ atomVar{'array_00519};
            nil}; r_00520.
         tailCall{ 'fini_00514;
            cons{ atomInt{(0)};
            nil}
         } (* end tailCall *)
         } (* end letExt *)
         } (* end letAlloc *)
         } (* end letExt *)
         } (* end letSubscript *)
         } (* end letAlloc *)
         } (* end letAlloc *)
      };
   ifthenelse{ eq_atom{'g; token["exnh_00511":t]};
      lambda{env_00521. lambda{a_00522.
         tailCall{ 'exnh_00509;
            cons{ atomVar{'env_00521};
            cons{ atomVar{'a_00522};
            nil}}
         } (* end tailCall *)
      }};
   it (* end functions *) }}}
} (* end fix term *)
} (* end final sequent *)

(* end theorem: program *)

(*****************************************************
 * End of FIR program output from compiler.
 *****************************************************)
(*****************************************************
 * Start of FIR program output from compiler.
 * Output stage: optimized
 *****************************************************)

include Mc_theory

interactive program_2 'H :

(*
 * Program imports.
 *)

(*


*)

(*
 * Program exports.
 *)

(*

naml_main_00528 = init : tyFun{
   cons{ tyFun{
         cons{ tyInt;
         nil}; tyEnum{(0)}};
   nil}; tyEnum{(0)}}

*)

(*
 * Program types.
 *)

(*


*)

(*
 * Program globals.
 *)

(*

array_00537 : tyDelayed =

*)

(*
 * Begin final sequent.
 *)

sequent ['ext] { 'H >-
fix{ g.
   ifthenelse{ eq_atom{'g; token["naml_main_00528":t]};
      lambda{fini_00532.
         letExt{ tyEnum{(1)}; token["ml_print_int":t]; tyFun{
            cons{ tyInt;
            nil}; tyEnum{(1)}};
            cons{ atomInt{(1)};
            nil}; r_00536.
         letExt{ tyEnum{(1)}; token["ml_print_string":t]; tyFun{
            cons{ tyArray{tyEnum{(256)}};
            nil}; tyEnum{(1)}};
            cons{ atomVar{'array_00537};
            nil}; r_00538.
         tailCall{ 'fini_00532;
            cons{ atomInt{(0)};
            nil}
         } (* end tailCall *)
         } (* end letExt *)
         } (* end letExt *)
      };
   it (* end functions *) }
} (* end fix term *)
} (* end final sequent *)

(* end theorem: program *)

(*****************************************************
 * End of FIR program output from compiler.
 *****************************************************)
