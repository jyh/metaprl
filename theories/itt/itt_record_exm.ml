include Itt_equal
include Itt_record
include Itt_arith
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

open Itt_struct


define unfold_plane:  plane <--> record["x"]{int;record["y"]{int}}
define unfold_space:  space <--> record["x"]{int;record["y"]{int;record["z"]{int}}}
define unfold_colored_plane:  cplane <--> record["color"]{atom;plane}
define unfold_colored_space:  cspace <--> record["color"]{atom;space}

define unfold_0: O <--> rcrd["x"]{0; rcrd["y"]{0; rcrd["z"]{0}}}
define unfold_A: A <--> rcrd["x"]{1; rcrd["y"]{2; rcrd["z"]{3;rcrd}}}
define unfold_B: B <--> rcrd["z"]{3; rcrd["y"]{2; rcrd["x"]{0}}}
define unfold_redA: redA <--> rcrd["color"]{token["red":t]; A}


interactive planeType {|intro_resource[] |} 'H :
   sequent['ext] {'H >- "type"{plane} }

let planeTypeT p =
   planeType (Sequent.hyp_count_addr p) p

interactive spaceType {|intro_resource[] |} 'H :
   sequent['ext] {'H >- "type"{space} }


interactive aInSpace {|intro_resource[] |} 'H :
   sequent['ext] {'H >- A IN space }

interactive_rw a_rw  :
   A <--> rcrd["y"]{2; rcrd["z"]{3; rcrd["x"]{1}}}

interactive_rw a_z_rw  :
   field["z"]{A} <--> 3


interactive bInSpace {|intro_resource[] |} 'H :
   sequent['ext] {'H >- B IN space }

interactive oInSpace {|intro_resource[] |} 'H :
   sequent['ext] {'H >- O IN space }

interactive abInPlane {|intro_resource[] |} 'H :
   sequent['ext] {'H >- A = B in plane }

interactive abInSpace {|intro_resource[] |} 'H :
   sequent['ext] {'H >- not{.A = B in space} }

interactive planeSpace {|intro_resource[] |} 'H :
   sequent['ext] {'H >- subtype{plane;space} }


define plane_point: point{'a;'b;'e} <--> rcrd["x"]{'a; rcrd["y"]{'b;'e }}
define space_point: point{'a;'b; 'c;'e} <--> rcrd["x"]{'a; rcrd["y"]{'b; rcrd["z"]{'c;'e}}}

let unfold_point = plane_point orelseC space_point
let fold_point = makeFoldC <<point{'a;'b;'e}>> plane_point orelseC makeFoldC <<point{'a;'b;'c;'e}>> space_point

interactive planeElim {|elim_resource[] |} 'H 'J:
   sequent['ext]{'H; a:int; b:int; e:record; 'J[point{'a;'b;'e}] >- 'C[point{'a;'b;'e}] } -->
   sequent['ext]  {'H; p:plane; 'J['p] >- 'C['p] }

interactive cspaceElim {|elim_resource[] |} 'H 'J:
   sequent['ext]{'H; a:int; b:int; c:int; color:atom; e:record; 'J[rcrd["color"]{'color;point{'a;'b; 'c; 'e}}] >- 'C[rcrd["color"]{'color;point{'a;'b; 'c; 'e}}] } -->
   sequent['ext]  {'H; p:cspace; 'J['p] >- 'C['p] }

interactive_rw point_beta1_rw : field["x"]{point{'a;'b;'e}} <--> 'a

interactive_rw point_beta2_rw : field["y"]{point{'a;'b;'e}} <--> 'b

interactive point_eta 'H :
   sequent[squash]{'H >- 'p IN plane } -->
   sequent['ext]{'H >-  'p ~ point{field["x"]{'p};field["x"]{'p};'p} }

define unfold_length: length{'p} <--> (field["x"]{'p}*@field["x"]{'p} +@ field["y"]{'p}*@field["y"]{'p})

interactive_rw reduce_length: length{point{'a;'b;'e}} <--> ('a *@ 'a +@ 'b *@ 'b)

interactive length_wf {|intro_resource[] |} 'H :
   sequent[squash]{'H >- 'p IN plane } -->
   sequent['ext]  {'H >- length{'p} IN int }

interactive length_A {|intro_resource[] |} 'H :
   sequent['ext]  {'H >- length{point{3;4;'e}} = 25 in int }



interactive tst 'H :
   sequent['ext]  { 'H >-  'C} -->
   sequent['ext]  { 'H >-  'C}


dform plane:  plane = mathbbP `"lane"
dform space:  space = mathbbS `"pace"
dform colored_plane:  cplane = `"Colored" plane
dform colored_space:  cspace = `"Colored" space

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
