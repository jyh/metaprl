(*
 * Functional Intermediate Representation formalized in MetaPRL.
 * Brian Emre Aydemir, emre@its.caltech.edu
 *
 * Define a limited version of the int_set type in the FIR.
 *)

include Base_theory
include Itt_theory
include Fir_ty

(*************************************************************************
 * Declarations.
 *************************************************************************)

(*
 * Intervals.
 * Represents a closed interval in the integers.
 * 'left and 'right should be numbers with 'left <= 'right.
 *)
declare interval{ 'left; 'right }

(*
 * The set.
 * 'intervals should be a list of intervals
 *)
declare int_set{ 'intervals }

(*
 * Member test.
 * in_interval reduces to btrue if 'num is in the interval and
 *    bfalse otherwise.
 * member reduces to btrue if 'num is in 'int_set and bfalse otherwise.
 *)
define unfold_in_interval : in_interval{ 'num; interval{'l; 'r} } <-->
   band{ le_bool{'l; 'num}; le_bool{'num; 'r} }
declare member{ 'num; 'int_set }

(*
 * int_set representations of ftrue and ffalse.
 * Placed here as a matter of convinience for evaluations "match"
 *    expressions.
 *)
define unfold_ftrueSet : ftrueSet <--> int_set{cons{interval{1; 1}; nil}}
define unfold_ffalseSet : ffalseSet <--> int_set{cons{interval{0; 0}; nil}}
