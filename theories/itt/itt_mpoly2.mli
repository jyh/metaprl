extends Itt_list2
extends Itt_ring_uce

open Refiner.Refiner.Refine
open Mp_resource
open Tactic_type.Conversionals

type var_set

val empty : unit -> var_set
val add : var_set -> term -> var_set
val find_index : var_set -> term -> int option
val vars_of_term : var_set -> term -> term -> var_set
val var_list : var_set -> term list

(*
 * RESOURCES USED BY standardizeT
 *)

resource (term * conv, conv) mpoly_eval
val process_mpoly_eval_resource_rw_annotation : (prim_rewrite, term*conv) rw_annotation_processor

topval mpoly_evalTopC : conv
topval mpoly_evalC : conv

topval reduce_add_mpolyC : conv

declare mpoly{'R; 'n}
declare eval_mpoly{'p; 'vals; 'R}
declare standardize{'p; 'R; 'n}
declare eval_mpolyTerm{'pt; 'vals; 'R}
declare mpoly_ofTerm{'pt; 'R; 'n}

rewrite mpolyTerm2mpoly :
	eval_mpolyTerm{'pt; 'vals; 'R} <-->
	eval_mpoly{mpoly_ofTerm{'pt;'R; length{'vals}}; 'vals; 'R}

rule eval_standardizeElim 'H unitringCE[i:l] :
	[wf] sequent{ <H> >- 'p in mpoly{'R; length{'vals}} } -->
	[wf] sequent{ <H> >- 'vals in list{'R^car} } -->
	[wf] sequent{ <H> >- 'R in unitringCE[i:l] } -->
	sequent{ <H>; ('t
		=eval_mpoly{standardize{'p; 'R; length{'vals}}; 'vals; 'R} in 'R^car); <J> >- 'C } -->
	sequent{ <H>; 't = eval_mpoly{'p; 'vals; 'R} in 'R^car; <J> >- 'C }

topval proveVarTypesT : term -> term list -> tactic
topval assertEqT : term -> term -> term list -> term -> term -> tactic
topval standardizeT : term -> term -> term -> term list -> term -> term -> tactic
topval stdT : term -> term -> term list -> int -> tactic

topval reduce_list_ind2Nil : conv
topval reduce_list_ind2Cons : conv
topval unfold_map2 : conv
topval unfold_mpoly : conv
topval unfold_const_mpoly : conv
topval reduce_eval_monom : conv
topval unfold_eval_mpoly : conv
topval reduce_add_mpolyNil : conv
topval reduce_add_mpolyCons : conv
topval reduce_mul_monom : conv
topval unfold_mul_monom_mpoly : conv
topval unfold_mul_mpoly : conv
topval unfold_id_mpoly : conv
topval unfold_zero_mpoly : conv
topval reduce_add_monom : conv
topval reduce_cmp_lexi : conv
topval reduce_eq_monom : conv
topval unfold_inject : conv
topval unfold_standardize : conv
topval reduce_eval_mpolyTermAdd : conv
topval reduce_eval_mpolyTermMul : conv
topval reduce_eval_mpolyTermConst : conv
topval reduce_eval_mpolyTermVar : conv
topval reduce_mpoly_ofTermAdd : conv
topval reduce_mpoly_ofTermMul : conv
topval reduce_mpoly_ofTermConst : conv
topval reduce_mpoly_ofTermVar : conv
