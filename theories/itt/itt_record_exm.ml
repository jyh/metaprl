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

define unfold_plane:  plane <--> record["x"]{int;record["y"]{int}}

define unfold_space:  space <--> record["x"]{int;record["y"]{int;record["z"]{int}}}

interactive planeType {|intro_resource[] |} 'H :
   sequent['ext] {'H >- "type"{plane} }

interactive spaceType {|intro_resource[] |} 'H :
   sequent['ext] {'H >- "type"{space} }


(*!
 * @begin[doc]
 * The elements of these types are records. E.g., the point $<<O>>$ is an element of the type $<<space>>$:
 * @end[doc]
 *)

define unfold_0: O <--> rcrd["x"]{0; rcrd["y"]{0; rcrd["z"]{0}}}

interactive oInSpace {|intro_resource[] |} 'H :
   sequent['ext] {'H >- O IN space }

(*!
 * @begin[doc]
 * $<<O>>$ is also can be considered as an element of the type $<<plane>>$:
 * @end[doc]
 *)

interactive oInPlane {|intro_resource[] |} 'H :
   sequent['ext] {'H >- O IN plane }

(*!
 * @begin[doc]
 * In general $<<space>>$ is a subtype of $<<plane>>$.
 * @end[doc]
 *)

interactive spacePlane {|intro_resource[] |} 'H :
   sequent['ext] {'H >- subtype{space;plane} }

(*!
 * @begin[doc]
 * Let us consider two points $<<A>>$ and $<<B>>$:
 * @end[doc]
 *)


define unfold_A: A <--> rcrd["x"]{1; rcrd["y"]{2; rcrd["z"]{3;rcrd}}}
define unfold_B: B <--> rcrd["z"]{0; rcrd["y"]{2; rcrd["x"]{1}}}

(*! @docoff *)

interactive aInSpace {|intro_resource[] |} 'H :
   sequent['ext] {'H >- A IN space }

interactive bInSpace {|intro_resource[] |} 'H :
   sequent['ext] {'H >- B IN space }


(*!
 * @begin[doc]
 * These points are equal in $<<plane>>$, since they have
 * the same $<<label["x"]>>$ and $<<label["y"]>>$ coordinates,
 * But they are not equal in $<<space>>$, since they differ in $<<label["z"]>>$ coordinate.
 * @end[doc]
 *)

interactive abInPlane {|intro_resource[] |} 'H :
   sequent['ext] {'H >- A = B in plane }

interactive abInSpace {|intro_resource[] |} 'H :
   sequent['ext] {'H >- not{.A = B in space} }

(*!
 * @begin[doc]
 * We can change the order of fields with different labels. E.g.,
 * @end[doc]
 *)

interactive_rw a_rw  :
   A <--> rcrd["y"]{2; rcrd["z"]{3; rcrd["x"]{1}}}

(*!
 * @begin[doc]
 * However if two fields have the same label, then the leftmost field covers others. E.g.,
 * @end[doc]
 *)

interactive_rw cover_rw  :
   rcrd["x"]{2; rcrd["x"]{3}} <-->    rcrd["x"]{2}


(*!
 * @begin[doc]
 * The field operator $<<field[x:s]{'r}>>$ gets the field $<<label[x:s]>>$ of the record $<<'r>>$. E.g.,
 * @end[doc]
 *)

interactive_rw a_z_rw  :
   field["z"]{A} <--> 3

(*!
 * @begin[doc]
 * Let us define
 * @end[doc]
 *)

define plane_point: point{'a;'b;'e} <--> rcrd["x"]{'a; rcrd["y"]{'b;'e }}
define space_point: point{'a;'b; 'c;'e} <--> rcrd["x"]{'a; rcrd["y"]{'b; rcrd["z"]{'c;'e}}}

let unfold_point = plane_point orelseC space_point

let fold_point =
   makeFoldC <<point{'a;'b;'c;'e}>> space_point orelseC
   makeFoldC <<point{'a;'b;'e}>> plane_point

interactive planeIntro {|intro_resource[] |} 'H :
   sequent[squash] {'H >- 'a IN int} -->
   sequent[squash] {'H >- 'b IN int} -->
   sequent['ext] {'H >- point{'a;'b;rcrd} IN plane}

interactive spaceIntro {|intro_resource[] |} 'H :
   sequent[squash] {'H >- 'a IN int} -->
   sequent[squash] {'H >- 'b IN int} -->
   sequent[squash] {'H >- 'c IN int} -->
   sequent['ext] {'H >- point{'a;'b;'c;rcrd} IN space}

(*!
 * @begin[doc]
 * Then we have the following reductions:
 * @end[doc]
 *)


interactive_rw point_beta1_rw : field["x"]{point{'a;'b;'e}} <--> 'a

interactive_rw point_beta2_rw : field["y"]{point{'a;'b;'e}} <--> 'b


let reduce_info =
   [<< field["x"]{point{'a;'b;'e}}  >>, point_beta1_rw;
    << field["y"]{point{'a;'b;'e}}  >>, point_beta2_rw]

let reduce_resource = Top_conversionals.add_reduce_info reduce_resource reduce_info

interactive point_eta 'H :
   sequent[squash]{'H >- 'p IN plane } -->
   sequent['ext]{'H >-   point{field["x"]{'p};field["y"]{'p};'p} ~ 'p }


(*!
 * @begin[doc]
 * The last reduction says that any element of $<<plane>>$ is a point of the form $<<point{'a;'b;rcrd}>>$.
 * Therefore we have the following elimination rule:
 * @end[doc]
 *)

interactive planeElim {|elim_resource[] |} 'H 'J:
   sequent['ext]{'H; a:int; b:int; e:record; 'J[point{'a;'b;'e}] >- 'C[point{'a;'b;'e}] } -->
   sequent['ext]  {'H; p:plane; 'J['p] >- 'C['p] }


(*! @docoff *)

interactive spaceElim {|elim_resource[] |} 'H 'J:
   sequent['ext]{'H; a:int; b:int; c:int; e:record; 'J[point{'a;'b;'c;'e}] >- 'C[point{'a;'b;'c;'e}] } -->
   sequent['ext]  {'H; p:space; 'J['p] >- 'C['p] }


(*!
 * @begin[doc]
 * Now we can define length of a point:
 * @end[doc]
 *)


define unfold_length: length{'p} <--> (field["x"]{'p}*@field["x"]{'p} +@ field["y"]{'p}*@field["y"]{'p})

(*!
 * @begin[doc]
 * That is,
 * @end[doc]
 *)

interactive_rw reduce_length: length{point{'a;'b;'e}} <--> ('a *@ 'a +@ 'b *@ 'b)

let reduce_info =
   [<< length{point{'a;'b;'e}}  >>, reduce_length]

let reduce_resource = Top_conversionals.add_reduce_info reduce_resource reduce_info


(*!
 * @begin[doc]
 * For example,
 * @end[doc]
 *)

interactive length_A {|intro_resource[] |} 'H :
   sequent['ext]  {'H >- length{point{3;4;'e}} = 25 in int }

(*!
 * @begin[doc]
 * Now, using the @tt{reduce_length} and @tt{planeElim} rule, we can prove that
 * @end[doc]
 *)

interactive length_wf {|intro_resource[] |} 'H :
   sequent[squash]{'H >- 'p IN plane } -->
   sequent['ext]  {'H >- length{'p} IN int }

(*!
 * @begin[doc]
 * Record can be extended. For example we can define $<<cplane>>$ and $<<cspace>>$ types.
 * @end[doc]
 *)

define unfold_colored_plane:  cplane <--> record["color"]{atom;plane}
define unfold_colored_space:  cspace <--> record["color"]{atom;space}

define unfold_redA: redA <--> rcrd["color"]{token["red":t]; A}

interactive redAInCSpace {|intro_resource[] |} 'H :
   sequent['ext] {'H >- redA IN cspace }

(*! @docoff *)





interactive cspaceElim {|elim_resource[] |} 'H 'J:
   sequent['ext]{'H; a:int; b:int; c:int; color:atom; e:record; 'J[rcrd["color"]{'color;point{'a;'b; 'c; 'e}}] >- 'C[rcrd["color"]{'color;point{'a;'b; 'c; 'e}}] } -->
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
