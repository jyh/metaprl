(*****************************************************
 * Start of FIR program output from compiler.
 * Output stage: after front end
 *****************************************************)

include Mc_theory

interactive ce_test1 'H :
   sequent ['ext] { 'H >-
      letBinop{ plusIntOp; tyInt; 1; 2; v.
      letBinop{ minusIntOp; tyInt; 'v; 3; w. 'w }}}

interactive ce_test2 'H :
   sequent ['ext] { 'H >-
      letBinop{ plusIntOp; tyInt; 2; 'a; v. 'v }}

interactive ce_test3 'H :
   sequent ['ext] { 'H >-
      letBinop{ plusIntOp; tyInt; 4; 6; a.
      letBinop{ minusIntOp; tyInt; 4; 'a; b.
      letBinop{ mulIntOp; tyInt; 'b; 'c; v. 'v }}}}

interactive mod_test1 'H :
   sequent ['ext] { 'H >-
      letBinop{ plusIntOp; tyInt; 1000000000; 1000000000; v. 'v } }

interactive mod_test2 'H :
   sequent ['ext] { 'H >- pow{ 2; 4 } }

interactive mod_test3 'H :
   sequent ['ext] { 'H >- mod_arith_unsigned{ int8; 400 } }

interactive mod_test4 'H :
   sequent ['ext] { 'H >- mod_arith_signed{ int8; 127 } }

interactive mod_test5 'H :
   sequent ['ext] { 'H >- mod_arith_signed{ int8; 128 } }

interactive mod_test6 'H :
   sequent ['ext] { 'H >- mod_arith_signed{ int8; 129 } }

interactive deadcode_test1 'H :
   sequent ['ext] { 'H >-
      letBinop{ plusIntOp; tyInt; 1; 2; v.
      letBinop{ minusIntOp; tyInt; 2; 3; w. 'w }}}

interactive deadcode_test2 'H :
   sequent ['ext] { 'H >-
      letBinop{ plusIntOp; tyInt; 1; 2; v.
      letBinop{ minusIntOp; tyInt; 2; 3; w. it }}}

(* Wouldn't evaluate anyway, but lets me test the deadcode elim tactic. *)
interactive deadcode_test3 'H :
   sequent ['ext] { 'H >-
      letBinop{ remIntOp; tyInt; 1; 2; a.
      letBinop{ divIntOp; 1; 2; 3; x.
      letUnop{ uminusIntOp; tyInt; 'a; b.
      letAlloc{ allocTuple{tyInt;cons{'b;nil}}; c.
      letAlloc{ allocArray{tyInt;'c}; d.
      letAlloc{ allocArray{1; 2}; y.
      letAlloc{ allocArray{tyInt;2}; e.
      letSubscript{ 1; 'x; 'y; 'e; f.
      letBinop{ 1; 2; 'f; 4; g.
      letSubscript{ 'x; 2; 'y; 4; h. 'h }}}}}}}}}}}

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

naml_main_00509 = init : tyFun{
   cons{ tyFun{
         cons{ tyInt;
         nil}; tyEnum{(0)}};
   nil}; tyEnum{(0)}}

*)

(* Begin final sequent. *)

sequent ['ext] { 'H >-
apply{ apply{ fix{ g. lambda{f.
(* Program types. *)
   ifthenelse{ eq_atom{'f; token["fini_00504":t]};
      tyDefLambda{
         nil; tyFun{
            cons{ tyInt;
            nil}; tyEnum{(0)}}};
   ifthenelse{ eq_atom{'f; token["exn_00505":t]};
      tyDefUnion{
         nil; normalUnion;
         nil};
   ifthenelse{ eq_atom{'f; token["bleh_00506":t]};
      tyDefUnion{
         cons{ 'a_00507;
         nil}; normalUnion;
         cons{             cons{ unionElt{ tyInt; val_true };
            nil};
         nil}};
(* Program globals. *)
(* Program functions. *)
   ifthenelse{ eq_atom{'f; token["exnh_00508":t]};
(*
tyFun{
   cons{ tyFun{
         cons{ tyInt;
         nil}; tyEnum{(0)}};
   cons{ tyUnion{ apply{'g; token["exn_00505":t]};
         nil; int_set{cons{interval{(-1073741824); (1073741823)}; nil}}};
   nil}}; tyEnum{(0)}};
*)
      lambda{fini_00511. lambda{e_00512.
         apply{'fini_00511; atomInt{(1)}}}};
   ifthenelse{ eq_atom{'f; token["naml_main_00509":t]};
(*
tyFun{
   cons{ tyFun{
         cons{ tyInt;
         nil}; tyEnum{(0)}};
   nil}; tyEnum{(0)}};
*)
      lambda{fini_00513.
         letAlloc{ allocTuple{tyDelayed;
            cons{ atomVar{'fini_00513};
            cons{ atomVar{apply{'g; token["exnh_00510":t]}};
            nil}}}; exnh_00514.
         letAlloc{ allocUnion{ tyUnion{ apply{'g; token["bleh_00506":t]};
            cons{ tyDelayed;
            nil}; int_set{cons{interval{(0); (0)}; nil}}}; apply{'g; token["bleh_00506":t]}; (0);
            cons{ atomInt{(1)};
            nil}}; c_00515.
         letSubscript{ blockPolySub; tyInt; 'c_00515; atomInt{(0)}; x_00516.
         letExt{ tyEnum{(1)}; token["ml_print_int":t]; tyFun{
            cons{ tyInt;
            nil}; tyEnum{(1)}};
            cons{ atomVar{'x_00516};
            nil}; r_00517.
         letAlloc{ allocArray{tyArray{tyEnum{(256)}};
            cons{ atomEnum{(256); (10)};
            cons{ atomEnum{(256); (0)};
            nil}}}; array_00518.
         letExt{ tyEnum{(1)}; token["ml_print_string":t]; tyFun{
            cons{ tyArray{tyEnum{(256)}};
            nil}; tyEnum{(1)}};
            cons{ atomVar{'array_00518};
            nil}; r_00519.
         apply{'fini_00513; atomInt{(0)}}}}}}}}};
   ifthenelse{ eq_atom{'f; token["exnh_00510":t]};
(*
tyFun{
   cons{ tyFun{
         cons{ tyInt;
         nil}; tyEnum{(0)}};
   cons{ tyUnion{ apply{'g; token["exn_00505":t]};
         nil; int_set{cons{interval{(-1073741824); (1073741823)}; nil}}};
   nil}}; tyEnum{(0)}};
*)
      lambda{env_00520. lambda{a_00521.
         apply{apply{apply{'g; token["exnh_00508":t]}; atomVar{'env_00520}}; atomVar{'a_00521}}}};
   unknownFun }}}}}}}}; (* fix term and contents ended *)

token["naml_main_00509":t] }; lambda{x.'x} }

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

naml_main_00527 = init : tyFun{
   cons{ tyFun{
         cons{ tyInt;
         nil}; tyEnum{(0)}};
   nil}; tyEnum{(0)}}

*)

(* Begin final sequent. *)

sequent ['ext] { 'H >-
apply{ apply{ fix{ g. lambda{f.
(* Program types. *)
(* Program globals. *)
(*
tyDelayed
*)
   ifthenelse{ eq_atom{'f; token["array_00536":t]};
      allocArray{tyDelayed;
         cons{ atomEnum{(256); (10)};
         cons{ atomEnum{(256); (0)};
         nil}}};
(* Program functions. *)
   ifthenelse{ eq_atom{'f; token["naml_main_00527":t]};
(*
tyFun{
   cons{ tyFun{
         cons{ tyInt;
         nil}; tyEnum{(0)}};
   nil}; tyEnum{(0)}};
*)
      lambda{fini_00531.
         letExt{ tyEnum{(1)}; token["ml_print_int":t]; tyFun{
            cons{ tyInt;
            nil}; tyEnum{(1)}};
            cons{ atomInt{(1)};
            nil}; r_00535.
         letExt{ tyEnum{(1)}; token["ml_print_string":t]; tyFun{
            cons{ tyArray{tyEnum{(256)}};
            nil}; tyEnum{(1)}};
            cons{ atomVar{apply{'g; token["array_00536":t]}};
            nil}; r_00537.
         apply{'fini_00531; atomInt{(0)}}}}};
   unknownFun }}}}; (* fix term and contents ended *)

token["naml_main_00527":t] }; lambda{x.'x} }

} (* end final sequent *)

(* end theorem: program2 *)

(*****************************************************
 * End of FIR program output from compiler.
 *****************************************************)
