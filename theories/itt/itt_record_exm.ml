(*!
 * @begin[doc]
 * @theory[Itt_record_exm]
 *
 * This theory contains some examples of how to use records.
 * @end[doc]
 *)

include Itt_record

(*! @docoff *)

include Itt_int_bool
include Itt_atom


open Printf
open Mp_debug
open Refiner.Refiner
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.TermSubst
open Refiner.Refiner.RefineError
open Mp_resource

open Var
open Tactic_type
open Tactic_type.Tacticals
open Base_dtactic
open Tactic_type.Conversionals

open Itt_int_bool
open Itt_struct
open Itt_record

(*!
 * @begin[doc]
 * First, let us define two record types: $<<plane>>$ and $<<space>>$.
 * @end[doc]
 *)

define unfold_plane:  plane <--> record["x":t]{int;record["y":t]{int}}

define unfold_space:  space <--> record["x":t]{int;record["y":t]{int;record["z":t]{int}}}

interactive planeType {|intro[] |} 'H :
   sequent['ext] {'H >- "type"{plane} }

interactive spaceType {|intro[] |} 'H :
   sequent['ext] {'H >- "type"{space} }


(*!
 * @begin[doc]
 * The elements of these types are records. E.g., the point $<<O>>$ is an element of the type $<<space>>$:
 * @end[doc]
 *)

define unfold_O: O <--> rcrd["x":t]{0; rcrd["y":t]{0; rcrd["z":t]{0}}}

interactive oInSpace {|intro[] |} 'H :
   sequent['ext] {'H >- O IN space }

(*!
 * @begin[doc]
 * $<<O>>$ is also can be considered as an element of the type $<<plane>>$:
 * @end[doc]
 *)

interactive oInPlane {|intro[] |} 'H :
   sequent['ext] {'H >- O IN plane }

(*!
 * @begin[doc]
 * In general $<<space>>$ is a subtype of $<<plane>>$.
 * @end[doc]
 *)

interactive spacePlane {|intro[] |} 'H :
   sequent['ext] {'H >- subtype{space;plane} }

(*!
 * @begin[doc]
 * Let us consider two points $<<A>>$ and $<<B>>$:
 * @end[doc]
 *)


define unfold_A: A <--> rcrd["x":t]{1; rcrd["y":t]{2; rcrd["z":t]{3;rcrd}}}
define unfold_B: B <--> rcrd["z":t]{0; rcrd["y":t]{2; rcrd["x":t]{1}}}

(*! @docoff *)

interactive aInSpace {|intro[] |} 'H :
   sequent['ext] {'H >- A IN space }

interactive bInSpace {|intro[] |} 'H :
   sequent['ext] {'H >- B IN space }


(*!
 * @begin[doc]
 * These points are equal in $<<plane>>$, since they have
 * the same $<<label["x":t]>>$ and $<<label["y":t]>>$ coordinates,
 * But they are not equal in $<<space>>$, since they differ in $<<label["z":t]>>$ coordinate.
 * @end[doc]
 *)

interactive abInPlane {|intro[] |} 'H :
   sequent['ext] {'H >- A = B in plane }

interactive abInSpace {|intro[] |} 'H :
   sequent['ext] {'H >- not{.A = B in space} }

(*!
 * @begin[doc]
 * We can change the order of fields with different labels. E.g.,
 * @end[doc]
 *)

interactive_rw a_rw  :
   A <--> rcrd["y":t]{2; rcrd["z":t]{3; rcrd["x":t]{1}}}

(*!
 * @begin[doc]
 * However if two fields have the same label, then the leftmost field covers others. E.g.,
 * @end[doc]
 *)

interactive_rw cover_rw  :
   rcrd["x":t]{2; rcrd["x":t]{3}} <-->    rcrd["x":t]{2}


(*!
 * @begin[doc]
 * The field operator $<<field[x:t]{'r}>>$ gets the field $<<label[x:t]>>$ of the record $<<'r>>$. E.g.,
 * @end[doc]
 *)

interactive_rw a_z_rw  :
   field["z":t]{A} <--> 3

(*!
 * @begin[doc]
 * Let us define
 * @end[doc]
 *)

define plane_point: point{'a;'b;'e} <--> rcrd["x":t]{'a; rcrd["y":t]{'b;'e }}
define space_point: point{'a;'b; 'c;'e} <--> rcrd["x":t]{'a; rcrd["y":t]{'b; rcrd["z":t]{'c;'e}}}

let unfold_point = plane_point orelseC space_point

let fold_point =
   makeFoldC <<point{'a;'b;'c;'e}>> space_point orelseC
   makeFoldC <<point{'a;'b;'e}>> plane_point

interactive planeIntro {|intro[] |} 'H :
   sequent[squash] {'H >- 'a IN int} -->
   sequent[squash] {'H >- 'b IN int} -->
   sequent['ext] {'H >- point{'a;'b;rcrd} IN plane}

interactive spaceIntro {|intro[] |} 'H :
   sequent[squash] {'H >- 'a IN int} -->
   sequent[squash] {'H >- 'b IN int} -->
   sequent[squash] {'H >- 'c IN int} -->
   sequent['ext] {'H >- point{'a;'b;'c;rcrd} IN space}

(*!
 * @begin[doc]
 * Then we have the following reductions:
 * @end[doc]
 *)


interactive_rw point_beta1_rw : field["x":t]{point{'a;'b;'e}} <--> 'a

interactive_rw point_beta2_rw : field["y":t]{point{'a;'b;'e}} <--> 'b

let resource reduce +=
   [<< field["x":t]{point{'a;'b;'e}}  >>, point_beta1_rw;
    << field["y":t]{point{'a;'b;'e}}  >>, point_beta2_rw]

interactive point_eta 'H :
   sequent[squash]{'H >- 'p IN plane } -->
   sequent['ext]{'H >-   point{field["x":t]{'p};field["y":t]{'p};'p} ~ 'p }


(*!
 * @begin[doc]
 * The last reduction says that any element of $<<plane>>$ is a point of the form $<<point{'a;'b;rcrd}>>$.
 * Therefore we have the following elimination rule:
 * @end[doc]
 *)

interactive planeElim {|elim[] |} 'H 'J:
   sequent['ext]{'H; a:int; b:int; e:record; 'J[point{'a;'b;'e}] >- 'C[point{'a;'b;'e}] } -->
   sequent['ext]  {'H; p:plane; 'J['p] >- 'C['p] }


(*! @docoff *)

interactive spaceElim {|elim[] |} 'H 'J:
   sequent['ext]{'H; a:int; b:int; c:int; e:record; 'J[point{'a;'b;'c;'e}] >- 'C[point{'a;'b;'c;'e}] } -->
   sequent['ext]  {'H; p:space; 'J['p] >- 'C['p] }


(*!
 * @begin[doc]
 * Now we can define length of a point:
 * @end[doc]
 *)


define unfold_length: length{'p} <--> (field["x":t]{'p}*@field["x":t]{'p} +@ field["y":t]{'p}*@field["y":t]{'p})

(*!
 * @begin[doc]
 * That is,
 * @end[doc]
 *)

interactive_rw reduce_length: length{point{'a;'b;'e}} <--> ('a *@ 'a +@ 'b *@ 'b)

let resource reduce += << length{point{'a;'b;'e}}  >>, reduce_length

(*!
 * @begin[doc]
 * For example,
 * @end[doc]
 *)

interactive length_A {|intro[] |} 'H :
   sequent['ext]  {'H >- length{point{3;4;'e}} = 25 in int }

(*!
 * @begin[doc]
 * Now, using the @tt{reduce_length} and @tt{planeElim} rule, we can prove that
 * @end[doc]
 *)

interactive length_wf {|intro[] |} 'H :
   sequent[squash]{'H >- 'p IN plane } -->
   sequent['ext]  {'H >- length{'p} IN int }

(*!
 * @begin[doc]
 * Record can be extended. For example we can define $<<cplane>>$ and $<<cspace>>$ types.
 * @end[doc]
 *)

define unfold_colored_plane:  cplane <--> record["color":t]{atom;plane}
define unfold_colored_space:  cspace <--> record["color":t]{atom;space}

define unfold_redA: redA <--> rcrd["color":t]{token["red":t]; A}

interactive redAInCSpace {|intro[] |} 'H :
   sequent['ext] {'H >- redA IN cspace }

(*! @docoff *)





interactive cspaceElim {|elim[] |} 'H 'J:
   sequent['ext]{'H; a:int; b:int; c:int; color:atom; e:record; 'J[rcrd["color":t]{'color;point{'a;'b; 'c; 'e}}] >- 'C[rcrd["color":t]{'color;point{'a;'b; 'c; 'e}}] } -->
   sequent['ext]  {'H; p:cspace; 'J['p] >- 'C['p] }




(*! @docoff *)

interactive tst 'H :
   sequent['ext]  { 'H >-  'C} -->
   sequent['ext]  { 'H >-  'C}



dform plane:  plane = mathbbP `"lane"
dform space:  space = mathbbS `"pace"
dform colored_plane:  cplane = mathbbC `"olored" plane
dform colored_space:  cspace = mathbbC `"olored" space

dform o: O = `"O"
dform a: A = `"A"
dform b: B = `"B"
dform redA: redA = `"redA"

dform point2: point{'a;'b;'e} = `"point(" 'a `"," 'b ")"
dform point3: point{'a;'b;'c;'e} = `"point(" 'a `"," 'b `"," 'c ")"

dform length: length{'p} = `"|" 'p `"|" subtwo




(*
let unfoldAllT = rwaAll [unfold_plane;unfold_space;unfoldColoredSpace;unfoldCol;unfoldField;unfoldRecordOrt]
*)
