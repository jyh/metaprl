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
 * Short form.
 * For convinience.  Declares a set consisting of the closed
 *    interval [a,b].
 *)
declare int_set{ 'a; 'b }

(*
 * Member test.
 * in_interval reduces to btrue if 'num is in the interval and
 *    bfalse otherwise.
 * member reduces to btrue if 'num is in 'int_set and bfalse otherwise.
 *    'num is in 'int_set if it's in any one of the intervals of the set.
 * not_in_interval and not_member are the negations of the above.
 *)
define unfold_in_interval :
   in_interval{ 'num; interval{'l; 'r} } <-->
   band{ le_bool{'l; 'num}; le_bool{'num; 'r} }
declare member{ 'num; 'int_set }
