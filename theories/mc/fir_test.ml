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

set_string_01217 = set_string : tyAll{
   cons{ 'env_01220;
   cons{ 'env_01221;
   nil}}; tyFun{
      cons{ tyFun{
            cons{ tyVar{'env_01220};
            cons{ tyEnum{(1)};
            nil}}; tyEnum{(0)}};
      cons{ tyVar{'env_01220};
      cons{ tyFun{
            cons{ tyVar{'env_01221};
            cons{ tyRawData;
            cons{ tyRawInt{int32; val_true};
            nil}}}; tyEnum{(0)}};
      cons{ tyVar{'env_01221};
      cons{ tyRawData;
      cons{ tyRawInt{int32; val_true};
      cons{ tyRawInt{int32; val_true};
      nil}}}}}}}; tyEnum{(0)}}}
main_01218 = main : tyAll{
   cons{ 'env_01222;
   cons{ 'env_01223;
   nil}}; tyFun{
      cons{ tyFun{
            cons{ tyVar{'env_01222};
            cons{ tyRawInt{int32; val_true};
            nil}}; tyEnum{(0)}};
      cons{ tyVar{'env_01222};
      cons{ tyFun{
            cons{ tyVar{'env_01223};
            cons{ tyRawData;
            cons{ tyRawInt{int32; val_true};
            nil}}}; tyEnum{(0)}};
      cons{ tyVar{'env_01223};
      cons{ tyRawInt{int32; val_true};
      cons{ tyRawData;
      cons{ tyRawInt{int32; val_true};
      nil}}}}}}}; tyEnum{(0)}}}
init_01219 = init : tyFun{
   cons{ tyFun{
         cons{ tyEnum{(1)};
         nil}; tyEnum{(0)}};
   nil}; tyEnum{(0)}}

*)

(* Begin final sequent. *)

sequent ['ext] { 'H >-
fix{ g. lambda{f.
(* Program types. *)
   ifthenelse{ eq_atom{'f; token["set_string_01212":t]};
      tyDefLambda{
         nil; tyRawData};
   ifthenelse{ eq_atom{'f; token["main_01213":t]};
      tyDefLambda{
         nil; tyRawData};
(* Program globals. *)
(*
tyRawData
*)
   ifthenelse{ eq_atom{'f; token["xnil_01214":t]};
      it (* InitRawData *);
(*
tyRawData
*)
   ifthenelse{ eq_atom{'f; token["string_01215":t]};
      it (* InitRawData *);
(* Program functions. *)
   ifthenelse{ eq_atom{'f; token["print_string_01216":t]};
(*
tyAll{
   cons{ 'env_01224;
   cons{ 'env_01225;
   nil}}; tyFun{
      cons{ tyFun{
            cons{ tyVar{'env_01224};
            cons{ tyEnum{(1)};
            nil}}; tyEnum{(0)}};
      cons{ tyVar{'env_01224};
      cons{ tyFun{
            cons{ tyVar{'env_01225};
            cons{ tyRawData;
            cons{ tyRawInt{int32; val_true};
            nil}}}; tyEnum{(0)}};
      cons{ tyVar{'env_01225};
      cons{ tyRawData;
      cons{ tyRawInt{int32; val_true};
      nil}}}}}}; tyEnum{(0)}}};
*)
      lambda{cps_01226. lambda{cps_01227. lambda{exnh_01228. lambda{exnh_01229. lambda{v_01230. lambda{v_01231.
         letExt{ tyEnum{(1)}; token["print_string":t]; tyFun{
            cons{ tyRawData;
            cons{ tyRawInt{int32; val_true};
            nil}}; tyEnum{(1)}};
            cons{ atomVar{'v_01230};
            cons{ atomVar{'v_01231};
            nil}}; print_string_01232.
         apply{apply{'cps_01226; atomVar{'cps_01227}}; atomEnum{(1); (0)}}}}}}}}};
   ifthenelse{ eq_atom{'f; token["set_string_01217":t]};
(*
tyAll{
   cons{ 'env_01233;
   cons{ 'env_01234;
   nil}}; tyFun{
      cons{ tyFun{
            cons{ tyVar{'env_01233};
            cons{ tyEnum{(1)};
            nil}}; tyEnum{(0)}};
      cons{ tyVar{'env_01233};
      cons{ tyFun{
            cons{ tyVar{'env_01234};
            cons{ tyRawData;
            cons{ tyRawInt{int32; val_true};
            nil}}}; tyEnum{(0)}};
      cons{ tyVar{'env_01234};
      cons{ tyRawData;
      cons{ tyRawInt{int32; val_true};
      cons{ tyRawInt{int32; val_true};
      nil}}}}}}}; tyEnum{(0)}}};
*)
      lambda{cps_01235. lambda{cps_01236. lambda{exnh_01237. lambda{exnh_01238. lambda{s_01239. lambda{s_01240. lambda{i_01241.
         letAlloc{ allocMalloc{atomInt{(10)}}; set_string_01242.
         letUnop{ idOp; tyApply{ apply{'g; token["set_string_01212":t]};
            nil}; atomVar{'set_string_01242}; set_string_01243.
         memcpy{ rawRawIntSub{int8; val_false}; 'set_string_01243; atomRawInt{(0)}; 's_01239; atomVar{'s_01240}; atomRawInt{(10)};
         letBinop{ it (* PlusRawIntOp *); tyRawInt{int32; val_true}; atomVar{'i_01241}; atomRawInt{(1)}; x_01244.
         letBinop{ it (* MulRawIntOp *); tyRawInt{int32; val_true}; atomVar{'x_01244}; atomRawInt{(1)}; xx_01245.
         letBinop{ it (* PlusRawIntOp *); tyRawInt{int32; val_true}; atomRawInt{(0)}; atomVar{'xx_01245}; s_01246.
         letSubscript{ rawRawIntSub{int8; val_false}; tyRawInt{int8; val_false}; 'set_string_01243; atomVar{'s_01246}; xx_01247.
         letBinop{ it (* PlusRawIntOp *); tyRawInt{int32; val_true}; atomVar{'i_01241}; atomRawInt{(1)}; x_01248.
         letBinop{ it (* MulRawIntOp *); tyRawInt{int32; val_true}; atomVar{'x_01248}; atomRawInt{(1)}; xx_01249.
         letBinop{ it (* PlusRawIntOp *); tyRawInt{int32; val_true}; atomRawInt{(0)}; atomVar{'xx_01249}; xx_01250.
         letBinop{ it (* MulRawIntOp *); tyRawInt{int32; val_true}; atomVar{'i_01241}; atomRawInt{(1)}; xx_01251.
         letBinop{ it (* PlusRawIntOp *); tyRawInt{int32; val_true}; atomRawInt{(0)}; atomVar{'xx_01251}; xx_01252.
         letSubscript{ rawRawIntSub{int8; val_false}; tyRawInt{int8; val_false}; 'set_string_01243; atomVar{'xx_01252}; xx_01253.
         setSubscript{ rawRawIntSub{int8; val_false}; tyRawInt{int8; val_false}; 'set_string_01243; atomVar{'xx_01250}; atomVar{'xx_01253}; set_string_01243.
         letBinop{ it (* MulRawIntOp *); tyRawInt{int32; val_true}; atomVar{'i_01241}; atomRawInt{(1)}; xx_01254.
         letBinop{ it (* PlusRawIntOp *); tyRawInt{int32; val_true}; atomRawInt{(0)}; atomVar{'xx_01254}; xx_01255.
         setSubscript{ rawRawIntSub{int8; val_false}; tyRawInt{int8; val_false}; 'set_string_01243; atomVar{'xx_01255}; atomVar{'xx_01247}; set_string_01243.
         apply{apply{'cps_01235; atomVar{'cps_01236}}; atomEnum{(1); (0)}}}}}}}}}}}}}}}}}}}}}}}}}};
   ifthenelse{ eq_atom{'f; token["main_01218":t]};
(*
tyAll{
   cons{ 'env_01256;
   cons{ 'env_01257;
   nil}}; tyFun{
      cons{ tyFun{
            cons{ tyVar{'env_01256};
            cons{ tyRawInt{int32; val_true};
            nil}}; tyEnum{(0)}};
      cons{ tyVar{'env_01256};
      cons{ tyFun{
            cons{ tyVar{'env_01257};
            cons{ tyRawData;
            cons{ tyRawInt{int32; val_true};
            nil}}}; tyEnum{(0)}};
      cons{ tyVar{'env_01257};
      cons{ tyRawInt{int32; val_true};
      cons{ tyRawData;
      cons{ tyRawInt{int32; val_true};
      nil}}}}}}}; tyEnum{(0)}}};
*)
      lambda{cps_01258. lambda{cps_01259. lambda{exnh_01260. lambda{exnh_01261. lambda{argc_01262. lambda{argv_01263. lambda{argv_01264.
         letAlloc{ allocMalloc{atomInt{(36)}}; main_01265.
         letUnop{ idOp; tyApply{ apply{'g; token["main_01213":t]};
            nil}; atomVar{'main_01265}; main_01266.
         setSubscript{ rawFunctionSub; tyFun{
            cons{ tyVar{apply{'g; token["exnh_00927":t]}};
            cons{ tyRawData;
            cons{ tyRawInt{int32; val_true};
            nil}}}; tyEnum{(0)}}; 'main_01266; atomRawInt{(4)}; atomVar{'exnh_01260}; main_01266.
         setSubscript{ rawDataSub; tyVar{apply{'g; token["exnh_00927":t]}}; 'main_01266; atomRawInt{(28)}; atomVar{'exnh_01261}; main_01266.
         setSubscript{ rawFunctionSub; tyFun{
            cons{ tyVar{apply{'g; token["cps_00926":t]}};
            cons{ tyRawInt{int32; val_true};
            nil}}; tyEnum{(0)}}; 'main_01266; atomRawInt{(0)}; atomVar{'cps_01258}; main_01266.
         setSubscript{ rawDataSub; tyVar{apply{'g; token["cps_00926":t]}}; 'main_01266; atomRawInt{(24)}; atomVar{'cps_01259}; main_01266.
         setSubscript{ rawDataSub; tyRawData; 'main_01266; atomRawInt{(20)}; atomVar{'main_01266}; main_01266.
         setSubscript{ rawRawIntSub{int32; val_true}; tyRawInt{int32; val_true}; 'main_01266; atomRawInt{(32)}; atomRawInt{(8)}; main_01266.
         setSubscript{ rawRawIntSub{int8; val_false}; tyRawInt{int8; val_false}; 'main_01266; atomRawInt{(8)}; atomRawInt{(72)}; main_01266.
         setSubscript{ rawRawIntSub{int8; val_false}; tyRawInt{int8; val_false}; 'main_01266; atomRawInt{(9)}; atomRawInt{(101)}; main_01266.
         setSubscript{ rawRawIntSub{int8; val_false}; tyRawInt{int8; val_false}; 'main_01266; atomRawInt{(10)}; atomRawInt{(108)}; main_01266.
         setSubscript{ rawRawIntSub{int8; val_false}; tyRawInt{int8; val_false}; 'main_01266; atomRawInt{(11)}; atomRawInt{(108)}; main_01266.
         setSubscript{ rawRawIntSub{int8; val_false}; tyRawInt{int8; val_false}; 'main_01266; atomRawInt{(12)}; atomRawInt{(111)}; main_01266.
         setSubscript{ rawRawIntSub{int8; val_false}; tyRawInt{int8; val_false}; 'main_01266; atomRawInt{(13)}; atomRawInt{(0)}; main_01266.
         letAlloc{ allocMalloc{atomInt{(10)}}; set_string_01267.
         letUnop{ idOp; tyApply{ apply{'g; token["set_string_01212":t]};
            nil}; atomVar{'set_string_01267}; set_string_01268.
         memcpy{ rawRawIntSub{int8; val_false}; 'set_string_01268; atomRawInt{(0)}; 'main_01266; atomRawInt{(8)}; atomRawInt{(10)};
         letSubscript{ rawRawIntSub{int8; val_false}; tyRawInt{int8; val_false}; 'set_string_01268; atomRawInt{(1)}; xx_01269.
         letSubscript{ rawRawIntSub{int8; val_false}; tyRawInt{int8; val_false}; 'set_string_01268; atomRawInt{(0)}; xx_01270.
         setSubscript{ rawRawIntSub{int8; val_false}; tyRawInt{int8; val_false}; 'set_string_01268; atomRawInt{(1)}; atomVar{'xx_01270}; set_string_01268.
         setSubscript{ rawRawIntSub{int8; val_false}; tyRawInt{int8; val_false}; 'set_string_01268; atomRawInt{(0)}; atomVar{'xx_01269}; set_string_01268.
         letSubscript{ rawDataSub; tyRawData; 'main_01266; atomRawInt{(20)}; s_01271.
         letSubscript{ rawRawIntSub{int32; val_true}; tyRawInt{int32; val_true}; 'main_01266; atomRawInt{(32)}; s_01272.
         letAlloc{ allocMalloc{atomInt{(10)}}; set_string_01273.
         letUnop{ idOp; tyApply{ apply{'g; token["set_string_01212":t]};
            nil}; atomVar{'set_string_01273}; set_string_01274.
         memcpy{ rawRawIntSub{int8; val_false}; 'set_string_01274; atomRawInt{(0)}; 's_01271; atomVar{'s_01272}; atomRawInt{(10)};
         letSubscript{ rawRawIntSub{int8; val_false}; tyRawInt{int8; val_false}; 'set_string_01274; atomRawInt{(4)}; xx_01275.
         letSubscript{ rawRawIntSub{int8; val_false}; tyRawInt{int8; val_false}; 'set_string_01274; atomRawInt{(3)}; xx_01276.
         setSubscript{ rawRawIntSub{int8; val_false}; tyRawInt{int8; val_false}; 'set_string_01274; atomRawInt{(4)}; atomVar{'xx_01276}; set_string_01274.
         setSubscript{ rawRawIntSub{int8; val_false}; tyRawInt{int8; val_false}; 'set_string_01274; atomRawInt{(3)}; atomVar{'xx_01275}; set_string_01274.
         letSubscript{ rawDataSub; tyRawData; 'main_01266; atomRawInt{(20)}; s_01277.
         letSubscript{ rawRawIntSub{int32; val_true}; tyRawInt{int32; val_true}; 'main_01266; atomRawInt{(32)}; s_01278.
         letExt{ tyEnum{(1)}; token["print_string":t]; tyFun{
            cons{ tyRawData;
            cons{ tyRawInt{int32; val_true};
            nil}}; tyEnum{(1)}};
            cons{ atomVar{'s_01277};
            cons{ atomVar{'s_01278};
            nil}}; print_string_01279.
         letExt{ tyEnum{(1)}; token["print_string":t]; tyFun{
            cons{ tyRawData;
            cons{ tyRawInt{int32; val_true};
            nil}}; tyEnum{(1)}};
            cons{ atomVar{apply{'g; token["string_01215":t]}};
            cons{ atomRawInt{(0)};
            nil}}; print_string_01280.
         letSubscript{ rawFunctionSub; tyFun{
            cons{ tyVar{apply{'g; token["cps_00973":t]}};
            cons{ tyRawInt{int32; val_true};
            nil}}; tyEnum{(0)}}; 'main_01266; atomRawInt{(0)}; cps_01281.
         letSubscript{ rawDataSub; tyVar{apply{'g; token["cps_00973":t]}}; 'main_01266; atomRawInt{(24)}; cps_01282.
         apply{apply{'cps_01281; atomVar{'cps_01282}}; atomRawInt{(0)}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}};
   ifthenelse{ eq_atom{'f; token["init_01219":t]};
(*
tyFun{
   cons{ tyFun{
         cons{ tyEnum{(1)};
         nil}; tyEnum{(0)}};
   nil}; tyEnum{(0)}};
*)
      lambda{exit_01283.
         apply{'exit_01283; atomEnum{(1); (0)}}};
   unknownFun }}}}}}}}}} (* fix term and contents ended *)

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

set_string_01289 = set_string : tyAll{
   cons{ 'env_01292;
   cons{ 'env_01293;
   nil}}; tyFun{
      cons{ tyFun{
            cons{ tyVar{'env_01292};
            cons{ tyEnum{(1)};
            nil}}; tyEnum{(0)}};
      cons{ tyVar{'env_01292};
      cons{ tyFun{
            cons{ tyVar{'env_01293};
            cons{ tyRawData;
            cons{ tyRawInt{int32; val_true};
            nil}}}; tyEnum{(0)}};
      cons{ tyVar{'env_01293};
      cons{ tyRawData;
      cons{ tyRawInt{int32; val_true};
      cons{ tyRawInt{int32; val_true};
      nil}}}}}}}; tyEnum{(0)}}}
main_01290 = main : tyAll{
   cons{ 'env_01294;
   cons{ 'env_01295;
   nil}}; tyFun{
      cons{ tyFun{
            cons{ tyVar{'env_01294};
            cons{ tyRawInt{int32; val_true};
            nil}}; tyEnum{(0)}};
      cons{ tyVar{'env_01294};
      cons{ tyFun{
            cons{ tyVar{'env_01295};
            cons{ tyRawData;
            cons{ tyRawInt{int32; val_true};
            nil}}}; tyEnum{(0)}};
      cons{ tyVar{'env_01295};
      cons{ tyRawInt{int32; val_true};
      cons{ tyRawData;
      cons{ tyRawInt{int32; val_true};
      nil}}}}}}}; tyEnum{(0)}}}
init_01291 = init : tyFun{
   cons{ tyFun{
         cons{ tyEnum{(1)};
         nil}; tyEnum{(0)}};
   nil}; tyEnum{(0)}}

*)

(* Begin final sequent. *)

sequent ['ext] { 'H >-
fix{ g. lambda{f.
(* Program types. *)
(* Program globals. *)
(*
tyRawData
*)
   ifthenelse{ eq_atom{'f; token["string_01287":t]};
      it (* InitRawData *);
(* Program functions. *)
   ifthenelse{ eq_atom{'f; token["set_string_01289":t]};
(*
tyAll{
   cons{ 'env_01305;
   cons{ 'env_01306;
   nil}}; tyFun{
      cons{ tyFun{
            cons{ tyVar{'env_01305};
            cons{ tyEnum{(1)};
            nil}}; tyEnum{(0)}};
      cons{ tyVar{'env_01305};
      cons{ tyFun{
            cons{ tyVar{'env_01306};
            cons{ tyRawData;
            cons{ tyRawInt{int32; val_true};
            nil}}}; tyEnum{(0)}};
      cons{ tyVar{'env_01306};
      cons{ tyRawData;
      cons{ tyRawInt{int32; val_true};
      cons{ tyRawInt{int32; val_true};
      nil}}}}}}}; tyEnum{(0)}}};
*)
      lambda{cps_01307. lambda{cps_01308. lambda{exnh_01309. lambda{exnh_01310. lambda{s_01311. lambda{s_01312. lambda{i_01313.
         letAlloc{ allocMalloc{atomInt{(10)}}; set_string_01314.
         memcpy{ rawRawIntSub{int8; val_false}; 'set_string_01314; atomRawInt{(0)}; 's_01311; atomVar{'s_01312}; atomRawInt{(10)};
         letBinop{ it (* PlusRawIntOp *); tyDelayed; atomRawInt{(1)}; atomVar{'i_01313}; x_01316.
         letSubscript{ rawRawIntSub{int8; val_false}; tyRawInt{int8; val_false}; 'set_string_01314; atomVar{'x_01316}; xx_01319.
         letSubscript{ rawRawIntSub{int8; val_false}; tyRawInt{int8; val_false}; 'set_string_01314; atomVar{'i_01313}; xx_01325.
         setSubscript{ rawRawIntSub{int8; val_false}; tyRawInt{int8; val_false}; 'set_string_01314; atomVar{'x_01316}; atomVar{'xx_01325}; set_string_01314.
         setSubscript{ rawRawIntSub{int8; val_false}; tyRawInt{int8; val_false}; 'set_string_01314; atomVar{'i_01313}; atomVar{'xx_01319}; set_string_01314.
         apply{apply{'cps_01307; atomVar{'cps_01308}}; atomEnum{(1); (0)}}}}}}}}}}}}}}}};
   ifthenelse{ eq_atom{'f; token["main_01290":t]};
(*
tyAll{
   cons{ 'env_01328;
   cons{ 'env_01329;
   nil}}; tyFun{
      cons{ tyFun{
            cons{ tyVar{'env_01328};
            cons{ tyRawInt{int32; val_true};
            nil}}; tyEnum{(0)}};
      cons{ tyVar{'env_01328};
      cons{ tyFun{
            cons{ tyVar{'env_01329};
            cons{ tyRawData;
            cons{ tyRawInt{int32; val_true};
            nil}}}; tyEnum{(0)}};
      cons{ tyVar{'env_01329};
      cons{ tyRawInt{int32; val_true};
      cons{ tyRawData;
      cons{ tyRawInt{int32; val_true};
      nil}}}}}}}; tyEnum{(0)}}};
*)
      lambda{cps_01330. lambda{cps_01331. lambda{exnh_01332. lambda{exnh_01333. lambda{argc_01334. lambda{argv_01335. lambda{argv_01336.
         letAlloc{ allocMalloc{atomInt{(36)}}; main_01337.
         setSubscript{ rawFunctionSub; tyFun{
            cons{ tyVar{apply{'g; token["exnh_00927":t]}};
            cons{ tyRawData;
            cons{ tyRawInt{int32; val_true};
            nil}}}; tyEnum{(0)}}; 'main_01337; atomRawInt{(4)}; atomVar{'exnh_01332}; main_01337.
         setSubscript{ rawDataSub; tyVar{apply{'g; token["exnh_00927":t]}}; 'main_01337; atomRawInt{(28)}; atomVar{'exnh_01333}; main_01337.
         setSubscript{ rawFunctionSub; tyFun{
            cons{ tyVar{apply{'g; token["cps_00926":t]}};
            cons{ tyRawInt{int32; val_true};
            nil}}; tyEnum{(0)}}; 'main_01337; atomRawInt{(0)}; atomVar{'cps_01330}; main_01337.
         setSubscript{ rawDataSub; tyVar{apply{'g; token["cps_00926":t]}}; 'main_01337; atomRawInt{(24)}; atomVar{'cps_01331}; main_01337.
         setSubscript{ rawDataSub; tyRawData; 'main_01337; atomRawInt{(20)}; atomVar{'main_01337}; main_01337.
         setSubscript{ rawRawIntSub{int32; val_true}; tyRawInt{int32; val_true}; 'main_01337; atomRawInt{(32)}; atomRawInt{(8)}; main_01337.
         setSubscript{ rawRawIntSub{int8; val_false}; tyRawInt{int8; val_false}; 'main_01337; atomRawInt{(8)}; atomRawInt{(72)}; main_01337.
         setSubscript{ rawRawIntSub{int8; val_false}; tyRawInt{int8; val_false}; 'main_01337; atomRawInt{(9)}; atomRawInt{(101)}; main_01337.
         setSubscript{ rawRawIntSub{int8; val_false}; tyRawInt{int8; val_false}; 'main_01337; atomRawInt{(10)}; atomRawInt{(108)}; main_01337.
         setSubscript{ rawRawIntSub{int8; val_false}; tyRawInt{int8; val_false}; 'main_01337; atomRawInt{(11)}; atomRawInt{(108)}; main_01337.
         setSubscript{ rawRawIntSub{int8; val_false}; tyRawInt{int8; val_false}; 'main_01337; atomRawInt{(12)}; atomRawInt{(111)}; main_01337.
         setSubscript{ rawRawIntSub{int8; val_false}; tyRawInt{int8; val_false}; 'main_01337; atomRawInt{(13)}; atomRawInt{(0)}; main_01337.
         letAlloc{ allocMalloc{atomInt{(10)}}; set_string_01339.
         memcpy{ rawRawIntSub{int8; val_false}; 'set_string_01339; atomRawInt{(0)}; 'main_01337; atomRawInt{(8)}; atomRawInt{(10)};
         letSubscript{ rawRawIntSub{int8; val_false}; tyRawInt{int8; val_false}; 'set_string_01339; atomRawInt{(1)}; xx_01341.
         letSubscript{ rawRawIntSub{int8; val_false}; tyRawInt{int8; val_false}; 'set_string_01339; atomRawInt{(0)}; xx_01342.
         setSubscript{ rawRawIntSub{int8; val_false}; tyRawInt{int8; val_false}; 'set_string_01339; atomRawInt{(1)}; atomVar{'xx_01342}; set_string_01339.
         setSubscript{ rawRawIntSub{int8; val_false}; tyRawInt{int8; val_false}; 'set_string_01339; atomRawInt{(0)}; atomVar{'xx_01341}; set_string_01339.
         letSubscript{ rawDataSub; tyRawData; 'main_01337; atomRawInt{(20)}; s_01343.
         letSubscript{ rawRawIntSub{int32; val_true}; tyRawInt{int32; val_true}; 'main_01337; atomRawInt{(32)}; s_01344.
         letAlloc{ allocMalloc{atomInt{(10)}}; set_string_01345.
         memcpy{ rawRawIntSub{int8; val_false}; 'set_string_01345; atomRawInt{(0)}; 's_01343; atomVar{'s_01344}; atomRawInt{(10)};
         letSubscript{ rawRawIntSub{int8; val_false}; tyRawInt{int8; val_false}; 'set_string_01345; atomRawInt{(4)}; xx_01347.
         letSubscript{ rawRawIntSub{int8; val_false}; tyRawInt{int8; val_false}; 'set_string_01345; atomRawInt{(3)}; xx_01348.
         setSubscript{ rawRawIntSub{int8; val_false}; tyRawInt{int8; val_false}; 'set_string_01345; atomRawInt{(4)}; atomVar{'xx_01348}; set_string_01345.
         setSubscript{ rawRawIntSub{int8; val_false}; tyRawInt{int8; val_false}; 'set_string_01345; atomRawInt{(3)}; atomVar{'xx_01347}; set_string_01345.
         letSubscript{ rawDataSub; tyRawData; 'main_01337; atomRawInt{(20)}; s_01349.
         letSubscript{ rawRawIntSub{int32; val_true}; tyRawInt{int32; val_true}; 'main_01337; atomRawInt{(32)}; s_01350.
         letExt{ tyEnum{(1)}; token["print_string":t]; tyFun{
            cons{ tyRawData;
            cons{ tyRawInt{int32; val_true};
            nil}}; tyEnum{(1)}};
            cons{ atomVar{'s_01349};
            cons{ atomVar{'s_01350};
            nil}}; print_string_01351.
         letExt{ tyEnum{(1)}; token["print_string":t]; tyFun{
            cons{ tyRawData;
            cons{ tyRawInt{int32; val_true};
            nil}}; tyEnum{(1)}};
            cons{ atomVar{apply{'g; token["string_01287":t]}};
            cons{ atomRawInt{(0)};
            nil}}; print_string_01352.
         letSubscript{ rawFunctionSub; tyFun{
            cons{ tyVar{apply{'g; token["cps_00973":t]}};
            cons{ tyRawInt{int32; val_true};
            nil}}; tyEnum{(0)}}; 'main_01337; atomRawInt{(0)}; cps_01353.
         letSubscript{ rawDataSub; tyVar{apply{'g; token["cps_00973":t]}}; 'main_01337; atomRawInt{(24)}; cps_01354.
         apply{apply{'cps_01353; atomVar{'cps_01354}}; atomRawInt{(0)}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}};
   ifthenelse{ eq_atom{'f; token["init_01291":t]};
(*
tyFun{
   cons{ tyFun{
         cons{ tyEnum{(1)};
         nil}; tyEnum{(0)}};
   nil}; tyEnum{(0)}};
*)
      lambda{exit_01355.
         apply{'exit_01355; atomEnum{(1); (0)}}};
   unknownFun }}}}}} (* fix term and contents ended *)

} (* end final sequent *)

(* end theorem: program2 *)

(*****************************************************
 * End of FIR program output from compiler.
 *****************************************************)
