(*
 * Functional Intermediate Representation formalized in MetaPRL.
 * Brian Emre Aydemir, emre@its.caltech.edu
 *
 * Define a limited version of the int_set type in the FIR.
 *)

include Base_theory
include Itt_theory

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
 * 'intervals should be a list of intervals, or nil in order to
 *    represent the empty set.
 *)
declare int_set{ 'intervals }

(*
 * Member test.
 * in_interval reduces to btrue if 'num is in the interval and
 *    bfalse otherwise.
 * member reduces to btrue if 'num is in 'int_set and bfalse otherwise.
 *    'num is in 'int_set if it's in any one of the intervals of the set.
 *)
define unfold_in_interval : in_interval{ 'num; interval{'l; 'r} } <-->
   band{ le_bool{'l; 'num}; le_bool{'num; 'r} }
declare member{ 'num; 'int_set }
