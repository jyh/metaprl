
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

val mpolyTerm_term : term
val is_mpolyTerm_term : term -> bool
val mk_mpolyTerm_term : term -> term -> term
val dest_mpolyTerm : term -> term * term

val varTerm_term : term
val is_varTerm_term : term -> bool
val mk_varTerm_term : term -> term
val dest_varTerm : term -> term

val mk_intnum_term : int -> term

topval mpoly_evalTopC : conv
topval mpoly_evalC : conv

declare mpoly{'R; 'n}
declare eval_mpoly{'p; 'vals; 'R}
declare eval_mpolyTerm{'pt; 'vals; 'R}
declare mpoly_ofTerm{'pt; 'R}
declare mpolyTerm{'R; 'n}

rule eval_standardizeElim 'H unitringCE[i:l] :
	[wf] sequent{ <H> >- 'pt in mpolyTerm{'R; length{'vals}} } -->
	[wf] sequent{ <H> >- 'vals in list{'R^car} } -->
	[wf] sequent{ <H> >- 'R in unitringCE[i:l] } -->
	sequent{ <H>; ('t
		=eval_mpoly{mpoly_ofTerm{'pt; 'R}; 'vals; 'R} in 'R^car); <J> >- 'C } -->
	sequent{ <H>; 't = eval_mpolyTerm{'pt; 'vals; 'R} in 'R^car; <J> >- 'C }

topval proveVarTypesT : term -> term list -> tactic
topval assertEqT : term -> term -> term list -> term -> term -> tactic
topval standardizeT : term -> term -> term -> term list -> term -> term -> tactic
topval stdT : term -> term -> term list -> int -> tactic
