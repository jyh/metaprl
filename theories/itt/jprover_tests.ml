include Itt_logic

(* Propositional logic: intuitionistically AND clasically valid *)
(* ============================================================ *)

interactive ax :
   sequent ['ext] { >- 'A => 'A}

interactive notnot :
   sequent ['ext] { >- 'A => "not"{("not"{'A})} }


interactive notnot2 :
   sequent ['ext] { >- "not"{'A} or "not"{'B} => "not"{'B} or "not"{'A} }

interactive implies :
   sequent ['ext] { >- ('A => 'B) => ('A => 'B) } 


(* MULT=x *)

interactive mult2 :
   sequent ['ext] { >- "not"{("not"{('A or "not"{'A})})} }

interactive mult3 :
   sequent ['ext] { >- "not"{("not"{(('A & 'B) or "not"{'A} or "not"{'B})})} }

interactive mult4 :
   sequent ['ext] { >- "not"{("not"{(('A & 'B & 'C) or "not"{'A} or "not"{'B} or "not"{'C})})} }


(* Example in Jens paper (prop. case): *)
(* ----------------------------------- *)

interactive jen :
   sequent ['ext] { >- ('S & ("not"{('T => 'R)} => 'P)) => (("not"{(('P => 'Q) & ('T => 'R))}) => (("not"{("not"{'P})}) & 'S & 'S)) }


(* Prop. counter examples from FI99 paper: *)
(* --------------------------------------- *)

(* !!! Needs two atom instances of all 'Bi in (('Bi or 'Ai) or 'Bi), except for i=n-1. 
   --> implicitely done by substitution application/composition!!! *)

interactive n1 :
   sequent ['ext] { >- 'A1 & (('B0 or 'A0) or 'B0) => 'A0 or ('B0 & 'A1) }

interactive n2 :
   sequent ['ext] { >- 'A2 & (('B0 => (('B1 or 'A1) or 'B1)) & (('B0 or 'A0) or 'B0)) => 'A0 or ('B0 & 'A1) or ('B1 & 'A2) }

interactive n3 : 
   sequent ['ext] { >- 'A3 & (('B1 => (('B2 or 'A2) or 'B2)) & ('B0 => (('B1 or 'A1) or 'B1)) & (('B0 or 'A0) or 'B0)) => 'A0 or ('B0 & 'A1) or ('B1 & 'A2) or ('B2 & 'A3) }

interactive n4 : 
   sequent ['ext] { >- 'A4 & (('B2 => (('B3 or 'A3) or 'B3)) & ('B1 => (('B2 or 'A2) or 'B2)) & ('B0 => (('B1 or 'A1) or 'B1)) & (('B0 or 'A0) or 'B0)) => 'A0 or ('B0 & 'A1) or ('B1 & 'A2) or ('B2 & 'A3) or ('B3 & 'A4) }


(* First-order logic: intuitionistically AND clasically valid *)
(* ========================================================== *)

interactive ax_all :
   sequent ['ext] { >- ((all x:'T. 'A['x]) => (all x:'T. 'A['x])) }

interactive all_exst :
   sequent ['ext] { >- ((all x:'T. 'A['x]) => (exst x:'T. 'A['x])) }

(* Example in Jens paper (first-order case): *)
(* ----------------------------------------- *)

(* needs two instances of the (all x:'O. 'S['x]) subformula *)

interactive jen2 :
   sequent ['ext] { >- (all a:'O. all b:'O. ((all x:'O. 'S['x]) & (all y:'O. ("not"{('T['y] => 'R['y])} => 'P['y])) => "not"{(exst z:'O. (('P['z] => 'Q['z]) & ('T['z] => 'R['z])))} => "not"{("not"{('P['a])})} & 'S['a] & 'S['b])) }

(* Spitting substitutions: *)
(* ----------------------- *)

interactive subst :
   sequent ['ext] { >- (all x:'T. ('A['x] or 'B['x])) & ((exst y:'T. 'A['y]) => (exst z:'T. ("not"{'A['z]}))) & (all x:'T. "not"{'B['x]}) =>  'Dummy }

(* barber *)

interactive barber 'H 'barber :
   sequent [squash] { 'H >- "type"{'People} } -->
   sequent [squash] { 'H >- member{'People; 'barber} } -->
   sequent [squash] { 'H; p1: 'People; p2: 'People >- "type"{'shaves['p1;'p2]} } -->
   sequent ['ext] { 'H; x: all person:'People. "iff"{'shaves['barber;'person];."not"{'shaves['person;'person]}} >- "false" }

(* Eliminating given free variables: *)
(* --------------------------------- *)

interactive fv1 : 
   sequent ['ext] { >- 'A['x] => 'A['y] }

interactive fv2 : 
   sequent ['ext] { >- all x:'T. 'A['x,'b] => 'A['f('a),'b] }

interactive fv3 :
   sequent ['ext] { >- all x:'T. 'A['x,'b] => 'A['f('a),'a] } (* INVALID *)

(* Jens example with free variables 'a and 'b *)

interactive jen_fv :
   sequent ['ext] { >- (all x:'O. 'S['x]) & (all y:'O. ("not"{('T['y] => 'R['y])} => 'P['y])) => "not"{(exst z:'O. (('P['z] => 'Q['z]) & ('T['z] => 'R['z])))} => "not"{("not"{('P['a])})} & 'S['a] & 'S['b] }

(* Functions *)
(* --------- *)

interactive fun1 :
   sequent ['ext] { >- 'P['a] & (all x:'O. ('P['x] => 'P['f['x]])) => 'P['f['f['f['f['a]]]]] }

interactive fun2 :
   sequent ['ext] { >- 'A['a,'g['a]] & (all x:'O. ('A['x,'g['x]] => 'A['f['x],'g['f['x]]])) => 'A['f['f['f['a]]],'g['f['f['f['a]]]]] }


(* First-order counter examples from AISC'98 paper: *)
(* ------------------------------------------------ *)

interactive ce1 : 
   sequent ['ext] { >- (all w:'T. 'A1['w]) & (all x:'T. (('B0 or 'A0['x]) or 'B0)) & "not"{('B0 & (all y:'T. 'A1['y]))} => all z:'T. 'A0['z] }

interactive ce2 : 
   sequent ['ext] { >- (all w:'T. 'A2['w]) & (all x:'T. (('B0 or 'A0['x]) or 'B0)) & "not"{('B0 & (all y:'T. 'A1['y]))} & "not"{('B1 & (all y:'T. 'A2['y]))} & (all x:'T. (('B1 or 'A1['x]) or 'B1)) => all z:'T. 'A0['z] }

interactive ce3 :
   sequent ['ext] { >- (all w:'T. 'A3['w]) & (all x:'T. (('B0 or 'A0['x]) or 'B0)) & "not"{('B0 & (all y:'T. 'A1['y]))} &  "not"{('B1 & (all y:'T. 'A2['y]))} & (all x:'T. (('B1 or 'A1['x]) or 'B1)) &  "not"{('B2 & (all y:'T. 'A3['y]))} & (all x:'T. (('B2 or 'A2['x]) or 'B2)) => all z:'T. 'A0['z] }

interactive ce4 : (* takes really long *)
   sequent ['ext] { >- (all w:'T. 'A4['w]) & (all x:'T. (('B0 or 'A0['x]) or 'B0)) & "not"{('B0 & (all y:'T. 'A1['y]))} & (all x:'T. (('B1 or 'A1['x]) or 'B1)) & "not"{('B1 & (all y:'T. 'A2['y]))} & (all x:'T. (('B2 or 'A2['x]) or 'B2)) & "not"{('B2 & (all y:'T. 'A3['y]))} & (all x:'T. (('B3 or 'A3['x]) or 'B3)) & "not"{('B3 & (all y:'T. 'A4['y]))} => all z:'T. 'A0['z] }

(* Some weired LJ deadlocks:   !!! these examples do not work with NuPRL's calculus yet !!! *)
(* ------------------------- *)

interactive deadlock1 :
   sequent ['ext] { >- (all x:'T. ('A['x] or 'B['x])) & ((exst y:'T. 'A['y]) => (exst z:'T. ("not"{'A['z]}))) => (exst x:'T. 'B['x]) }

interactive deadlock2 :
   sequent ['ext] { >- (all x: 'T. all y:'T. ('P['x,'y] or 'B['x,'y])) & ((exst x:'T. exst y:'T. 'P['x,'y]) => (exst a:'T. 'A['a,'c])) & (all z:'T. ('A['z,'c] => (exst b:'T. "not"{('P['z,'b])}))) => exst x:'T. exst y:'T. 'B['x,'y] }

(* embedding LJ deadlocks into bigger non-deadlock proofs *)

interactive deadlock3 : 
   sequent ['ext] { >- 'P & (all x:'T. ('A['x] or 'B['x])) & ((exst y:'T. 'A['y]) => (exst z:'T. ("not"{'A['z]}))) => (exst x:'T. 'B['x]) & 'P }

interactive deadlock4 :
   sequent ['ext] { >- (all x:'T. (('A['x] or 'B['x]) & 'P)) & ((exst y:'T. 'A['y]) => (exst z:'T. ("not"{'A['z]}))) => (exst x:'T. 'B['x]) & 'P }

(* ebedding multiple use of eigenvariable formula WITHOUT eigenvariable renaming *)

interactive mult_norem :
   sequent ['ext] { >- (all x:'T. ('A['x] or (exst a:'T. 'B['x,'a]))) & ((exst y:'T. 'A['y]) => (exst z:'T. ("not"{'A['z]}))) => (exst x:'T. exst y:'T. 'B['x,'y]) }

interactive mult_norem2 :
   sequent ['ext] { >- (all x:'T. ('A['x] or ('B['x] & (exst a:'T. 'C['a])))) & ((exst y:'T. 'A['y]) => (exst z:'T. ("not"{'A['z]}))) => (exst x:'T. ('B['x] & (exst z:'T. 'C['z]))) }

(* ebedding multiple use of eigenvariable formula WITH eigenvariable rule deletion *)
(* -- identical eigenvarieble rule occurs in the same branch -- *)

interactive mult_del :
   sequent ['ext] { >- (all x:'T. (('A['x] or 'B['x]) & (exst a:'T. 'C['a]))) & ((exst y:'T. 'A['y]) => (exst z:'T. ("not"{'A['z]}))) => (exst x:'T. ('B['x] & (exst z:'T. 'C['z]))) }

(* ebedding multiple use of eigenvariable formula WITH eigenvariable renaming *)

interactive mult_ren :
   sequent ['ext] { >- (all x:'T. (('A['x] or 'B['x]) & (exst a:'T. 'C['a,'x]))) & ((exst y:'T. 'A['y]) => (exst z:'T. ("not"{'A['z]}))) => (exst x:'T. ('B['x] & (exst z:'T. 'C['z,'x]))) }


(* The following does not use single-conclusion ITT - saved for future reference

Dealing with LJmc deadlocks -- beta proofs
========================================== 

jtest <<(("not"{'A} or "not"{'D}) & ('A or 'B) & "not"{(('A or 'B) & 'B)} => "not"{'D})>> "J" "LJmc";;


(* Full deadlock in LJmc --> decomposition problem *)


jtest <<("not"{('B & ('A or 'B))} & ("not"{'A} or "not"{'D}) => "not"{('A or 'B)} or "not"{'D})>> "J" "LJmc";;



jtest <<(('A or 'A) & ("not"{('A)} or 'A) => 'A)>> "J" "LJmc";;
jtest <<(("not"{('A)} or 'A) & ('A or 'A) => 'A)>> "J" "LJmc";;







%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%






Propositional logic: ONLY clasically valid
===========================================





jtest << 'A or "not"{'A} >> "C" "LK";;
jtest << 'A or "not"{'A} >> "J" "LJmc";;
jtest << 'A or "not"{'A} >> "J" "LJ";;



jtest <<"not"{("not"{'A})} => 'A >> "C" "LK";;



test for search: 
---------------


jtest << 'A  or ("not"{'A} & 'B) or ("not"{'B} & 'C) or("not"{'C} & 'D) or ("not"{'A}) >> "C" "LK";;




complete matrices:
------------------


n=2


jtest << ('A & 'B) or ('A & "not"{'B}) or ("not"{'A} & 'B) or ("not"{'A} & "not"{'B}) >> "C" "LK";;


n=3


<< ('A & 'B & 'C) or ('A & "not"{'B} & 'C) or ("not"{'A} & 'B & 'C) or ("not"{'A} & "not"{'B} & 'C) or ('A & 'B & "not"{'C}) or ('A & "not"{'B} & "not"{'C}) or ("not"{'A} & 'B & "not"{'C}) or ("not"{'A} & "not"{'B} & "not"{'C}) >>


n=4


jtest << ('A & 'B & "not"{'C} & 'D) or ('A & "not"{'B} & "not"{'C} & 'D) or ("not"{'A} & 'B & "not"{'C} & 'D) or ('A & 'B & 'C & 'D) or ('A & "not"{'B} & 'C & 'D) or ("not"{'A} & 'B & 'C & 'D) or ("not"{'A} & "not"{'B} & 'C & 'D) or ("not"{'A} & "not"{'B} & "not"{'C} & 'D) or ('A & 'B & 'C & "not"{'D}) or ('A & "not"{'B} & 'C & "not"{'D}) or ("not"{'A} & 'B & 'C & "not"{'D}) or ("not"{'A} & "not"{'B} & 'C & "not"{'D}) or ('A & 'B & "not"{'C} & "not"{'D}) or ('A & "not"{'B} & "not"{'C} & "not"{'D}) or ("not"{'A} & 'B & "not"{'C} & "not"{'D}) or ("not"{'A} & "not"{'B} & "not"{'C} & "not"{'D}) >> "C" "LK";;


jtest << ('A & 'B & "not"{'C} & 'D) or ('A & "not"{'B} & "not"{'C} & 'D) or ("not"{'A} & 'B & "not"{'C} & 'D) or ('A & 'B & 'C & 'D) or ('A & "not"{'B} & 'C & 'D) or ("not"{'A} & 'B & 'C & 'D) or ("not"{'A} & "not"{'B} & 'C & 'D) or ("not"{'A} & "not"{'B} & "not"{'C} & 'D) or ('A & 'B & 'C & "not"{'D}) or ('A & "not"{'B} & 'C & "not"{'D}) or ("not"{'A} & 'B & 'C & "not"{'D}) or ("not"{'A} & "not"{'B} & 'C & "not"{'D}) or ('A & 'B & "not"{'C} & "not"{'D}) or ('A & "not"{'B} & "not"{'C} & "not"{'D}) or ("not"{'A} & 'B & "not"{'C} & "not"{'D}) or ("not"{'A} & "not"{'B} & "not"{'C} & "not"{'D}) >> "C" "LK";;

First-order logic: ONLY clasically valid
==========================================

--> needs two instances

jtest << (exst x:'T. all y:'T. ('A['x] => 'A['y])) >> "C" "LK";; 

First-order logic: invalid
==========================

jtest << (exst x:'T. all y:'T. ('A['x,'y] => 'A['y,'x])) >> "C" "LK";; 


*)

(* Some weird tests. I am not sure whether it's reasonable to keep them - nogin 

MISC: Not applicable to jprover!!!
===================================


Mult tests, tree increase
-------------------------


<< "not"{(all x:'T. ('A['x] or 'B['x]))} >>

<< "not"{(all x:'T. ('A['x] or "not"{('B['x])}))} >>


<< all x:'T. ('A['x] or 'B['x]) >>

<< (all x:'T. ('A['x] or 'B['x])) & ((exst y:'T. 'A['y]) => (exst z:'T. ("not"{'A['z]}))) => (exst x:'T. 'B['x]) >> 


T-String Unification: 
----------------------


ttest ["ct";"ca";"cb";"vU";"cl";"vA";"vR"] ["ct";"ca";"vS";"vT";"ce";"vF";"cu";"vL"] "e" "f" []

ttest ["ca";"vB";"cc";"vD";"vE";"cf"] ["ca";"vB";"vG";"ch";"ci";"vJ"] "d" "e" []

ttest ["vG";"ch";"ci";"vJ"] ["cc";"vD";"vE";"cf"] "d" "e" []

 
ttest ["ca";"vX"] ["vY";"cb"] "d" "e" []




Stepwise development of prop. Jens example
------------------------------------------


ttest ["c1";"c2";"v7";"c9";"v11";"c13"] ["c1";"c2";"c19";"v21";"c30";"v32"] "c13" "v32" []

ttest ["c1";"c2";"c19";"v21";"c24";"v26"] ["c1";"c2";"c19";"c37";"v39";"c41"] "v26" "c41" [(["c13";"v32"],(["v7";"c9";"v11";"c13"],["c19";"v21";"c30";"v32"]))]



ttest ["c1";"c2";"c19";"c44"] ["c1";"c2";"v5"] "c44" "v5" [(["v26";"c41"],(["v21";"c24";"v26"],["c37";"v39";"c41"]));(["c13";"v32"],(["v7";"c9";"v11";"c13"],["c19";"v21";"c30";"v32"]))]


ttest  ["c1";"c2";"c19";"c46"] ["c1";"c2";"v5"] "c46" "v5" [(["c44";"v5"],(["c19";"c44"],["v5"]));(["v26";"c41"],(["v21";"c24";"v26"],["c37";"v39";"c41"]));(["c13";"v32"],(["v7";"c9";"v11";"c13"],["c19";"v21";"c30";"v32"]))]


ttest ["c1";"c2";"v7";"c9";"v11";"v15"] ["c1";"c2";"c19";"v21";"c30";"c34"] "v15" "c34" [(["c46";"v5"],(["c19";"c46"],["v5"]));(["c44";"v5"],(["c19";"c44"],["v5"]));(["v26";"c41"],(["v21";"c24";"v26"],["c37";"v39";"c41"]));(["c13";"v32"],(["v7";"c9";"v11";"c13"],["c19";"v21";"c30";"v32"]))]



ttest ["c1";"c2";"c19";"v21";"c24";"v26"] ["c1";"c2";"c19";"c37";"v39";"c41"] "v26" "c41" [(["v15";"c34"],(["v7";"c9";"v11";"v15"],["c19";"v21";"c30";"c34"]));(["c46";"v5"],(["c19";"c46"],["v5"]));(["c44";"v5"],(["c19";"c44"],["v5"]));(["v26";"c41"],(["v21";"c24";"v26"],["c37";"v39";"c41"]));(["c13";"v32"],(["v7";"c9";"v11";"c13"],["c19";"v21";"c30";"v32"]))]



ttest ["c1";"c2";"v7";"v17"] ["c1";"c2";"c19";"c37";"v39";"c41"] "v17" "c41" [(["v15";"c34"],(["v7";"c9";"v11";"v15"],["c19";"v21";"c30";"c34"]));(["c46";"v5"],(["c19";"c46"],["v5"]));(["c44";"v5"],(["c19";"c44"],["v5"]));(["v26";"c41"],(["v21";"c24";"v26"],["c37";"v39";"c41"]));(["c13";"v32"],(["v7";"c9";"v11";"c13"],["c19";"v21";"c30";"v32"]))]




Counter example for cut flag: 
-------------------------------


ttest ["v1";"c1";"v2";"c2";"v3"] ["c3";"v4";"c4"] "v3" "c4" []



Reduction orderings as sets
---------------------------


("v7",["c4";"c5"]) 
[("a1",["v2";"c3";"c4";"c5"]);("v2",["c3";"c4";"c5"]);("c3",["c4";"c5"]);("c4",["c5"]);("c5",[]);("a6",["v7";"c8";"a9"]);("v7",["c8";"a9"]);("c8",["a9"]);("a9",[])]



First-order unification
-----------------------

(* test terms *)


let t1 = let t = mk_string_term (make_opname []) "c" in (subst <<'A['f['x,'z]]>> [t] ["x"]);;

*)

