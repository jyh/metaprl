extends Itt_logic

(* Propositional logic: classically AND intuitionistically valid *)
(* ============================================================ *)


(* simple formulae, just getting started *)

interactive ax :
   sequent ['ext] { >- 'A => 'A}

interactive notnot :
   sequent ['ext] { >- 'A => "not"{("not"{'A})} }


interactive notnot2 :
   sequent ['ext] { >- "not"{'A} or "not"{'B} => "not"{'B} or "not"{'A} }

interactive implies :
   sequent ['ext] { >- ('A => 'B) => ('A => 'B) }



(* MULT = x *)
(* Generating muliply used subformulae, i.e. the negation-left subformula has to *)
(* be used x times in a proof, for x = 2,3,4 *)
(* Remark: these formulae are generic and can easily be extended to multiple uses for x > 4 *)


interactive mult2 :
   sequent ['ext] { >- "not"{("not"{('A or "not"{'A})})} }

interactive mult3 :
   sequent ['ext] { >- "not"{("not"{(('A & 'B) or "not"{'A} or "not"{'B})})} }

interactive mult4 :
   sequent ['ext] { >- "not"{("not"{(('A & 'B & 'C) or "not"{'A} or "not"{'B} or "not"{'C})})} }




(* Example in Jens paper (prop. case): *)
(* ----------------------------------- *)

(* Simply a bigger propositional formula *)
(* Refers to the propositional structure of the example in the papers [1] and [2],*)
(* as documented in the file refiner/reflib/jall.mli *)


interactive jens_prop :
   sequent ['ext] { >- ('S & ("not"{('T => 'R)} => 'P)) => (("not"{(('P => 'Q) & ('T => 'R))}) => (("not"{("not"{'P})}) & 'S & 'S)) }



(* Prop. counter examples from FI99 paper: *)
(* --------------------------------------- *)


(* Generic formulae from the paper [10], as documented in the file *)
(* refiner/reflib/jall.mli, for n = 1,2,3,4. *)
(* These formulae cause exponential proof length in EVERY LJ proof wrt. the *)
(* proof length of a given LJmc proof in propositional intuitionistic logic *)
(* The examples can easily be extended to n > 4 *)


interactive prop_n1 :
   sequent ['ext] { >- 'A1 & (('B0 or 'A0) or 'B0) => 'A0 or ('B0 & 'A1) }

interactive prop_n2 :
   sequent ['ext] { >- 'A2 & (('B0 => (('B1 or 'A1) or 'B1)) & (('B0 or 'A0) or 'B0)) => 'A0 or ('B0 & 'A1) or ('B1 & 'A2) }

interactive prop_n3 :
   sequent ['ext] { >- 'A3 & (('B1 => (('B2 or 'A2) or 'B2)) & ('B0 => (('B1 or 'A1) or 'B1)) & (('B0 or 'A0) or 'B0)) => 'A0 or ('B0 & 'A1) or ('B1 & 'A2) or ('B2 & 'A3) }

interactive prop_n4 :
   sequent ['ext] { >- 'A4 & (('B2 => (('B3 or 'A3) or 'B3)) & ('B1 => (('B2 or 'A2) or 'B2)) & ('B0 => (('B1 or 'A1) or 'B1)) & (('B0 or 'A0) or 'B0)) => 'A0 or ('B0 & 'A1) or ('B1 & 'A2) or ('B2 & 'A3) or ('B3 & 'A4) }




(* First-order logic: classically AND intuitionistically      *)
(* ========================================================== *)


(* simple formula, just getting started *)

interactive ax_all :
   sequent ['ext] { >- ((all x:'T. 'A['x]) => (all x:'T. 'A['x])) }


(* involves the vo_jprover parameter with the cut rule *)

interactive all_exst :
   sequent ['ext] { >- ((all x:'T. 'A['x]) => (exst x:'T. 'A['x])) }




(* Example in Jens paper (first-order case): *)
(* ----------------------------------------- *)

(* Refers to the first-order example in the papers [1] and [2],*)
(* as documented in the file refiner/reflib/jall.mli *)
(* Only difference: all-closure wrt. the parameters a and b *)
(* It needs two instances of the (all x:'O. 'S['x]) subformula *)


interactive jens_fo :
   sequent ['ext] { >- (all a:'O. all b:'O. ((all x:'O. 'S['x]) & (all y:'O. ("not"{('T['y] => 'R['y])} => 'P['y])) => "not"{(exst z:'O. (('P['z] => 'Q['z]) & ('T['z] => 'R['z])))} => "not"{("not"{('P['a])})} & 'S['a] & 'S['b])) }



(* Spitting substitutions: *)
(* ----------------------- *)


(* Making branches independent from eigenvariables introduced in other branches *)
(* Involves the vo_jprover parameter with the cut rule *)

interactive subst :
   sequent ['ext] { >- (all x:'T. ('A['x] or 'B['x])) & ((exst y:'T. 'A['y]) => (exst z:'T. ("not"{'A['z]}))) & (all x:'T. "not"{'B['x]}) =>  'Dummy }


(* barber *)

interactive barber 'H 'barber :
   sequent [squash] { 'H >- "type"{'People} } -->
   sequent [squash] { 'H >- 'barber in 'People } -->
   sequent [squash] { 'H; p1: 'People; p2: 'People >- "type"{'shaves['p1;'p2]} } -->
   sequent ['ext] { 'H; x: all person:'People. "iff"{'shaves['barber;'person];."not"{'shaves['person;'person]}} >- "false" }



(* Eliminating given free variables: *)
(* --------------------------------- *)

(* These examples take care of previously constructed objects *)
(* during an interactive proof session *)


interactive fv1 bind{x.'A['x]} 'x 'y :
   sequent ['ext] { >- 'A['x] => 'A['y] }

interactive fv2 bind{x.'A['x]} 'a 'b 'f :
   sequent ['ext] { >- all x:'T. 'A['x,'b] => 'A['f('a),'b] }

interactive fv3 bind{x.'A['x]} 'a 'b 'f :
   sequent ['ext] { >- all x:'T. 'A['x,'b] => 'A['f('a),'a] }  (* INVALID *)



(* Jens first-order example with free variables 'a and 'b *)
(* --------------------------------------------------------- *)

(* Refers to the ORIGINAL first-order example in the papers [1] and [2],*)
(* as documented in the file refiner/reflib/jall.mli *)
(* It needs two instances of the (all x:'O. 'S['x]) subformula *)



interactive jens_fo_fv 'a 'b :
   sequent ['ext] { >- (all x:'O. 'S['x]) & (all y:'O. ("not"{('T['y] => 'R['y])} => 'P['y])) => "not"{(exst z:'O. (('P['z] => 'Q['z]) & ('T['z] => 'R['z])))} => "not"{("not"{('P['a])})} & 'S['a] & 'S['b] }



(* Functions *)
(* --------- *)

(* Some examples with function symbols *)
(* These formula are generic benchmarks if one increases the number *)
(* of function symbols in the righmost implication's conclusion *)


interactive fun1 'a bind{x.'f['x]} :
   sequent ['ext] { >- 'P['a] & (all x:'O. ('P['x] => 'P['f['x]])) => 'P['f['f['f['f['a]]]]] }

interactive fun2 bind{x.'A['x]} 'a bind{x.'f['x]} bind{x.'g['x]} :
   sequent ['ext] { >- 'A['a,'g['a]] & (all x:'O. ('A['x,'g['x]] => 'A['f['x],'g['f['x]]])) => 'A['f['f['f['a]]],'g['f['f['f['a]]]]] }





(* First-order counter examples from AISC'98 paper: *)
(* ------------------------------------------------ *)


(* Generic formulae from the paper [9], as documented in the file *)
(* refiner/reflib/jall.mli, for n = 1,2,3,4. *)
(* These formulae cause exponential proof length in EVERY LJ proof wrt. the *)
(* proof length of a given LJmc proof in first-order intuitionistic logic *)
(* The examples can easily be extended to n > 4 *)



interactive fo_n1 :
   sequent ['ext] { >- (all w:'T. 'A1['w]) & (all x:'T. (('B0 or 'A0['x]) or 'B0)) & "not"{('B0 & (all y:'T. 'A1['y]))} => all z:'T. 'A0['z] }

interactive fo_n2 :
   sequent ['ext] { >- (all w:'T. 'A2['w]) & (all x:'T. (('B0 or 'A0['x]) or 'B0)) & "not"{('B0 & (all y:'T. 'A1['y]))} & "not"{('B1 & (all y:'T. 'A2['y]))} & (all x:'T. (('B1 or 'A1['x]) or 'B1)) => all z:'T. 'A0['z] }

interactive fo_n3 :
   sequent ['ext] { >- (all w:'T. 'A3['w]) & (all x:'T. (('B0 or 'A0['x]) or 'B0)) & "not"{('B0 & (all y:'T. 'A1['y]))} &  "not"{('B1 & (all y:'T. 'A2['y]))} & (all x:'T. (('B1 or 'A1['x]) or 'B1)) &  "not"{('B2 & (all y:'T. 'A3['y]))} & (all x:'T. (('B2 or 'A2['x]) or 'B2)) => all z:'T. 'A0['z] }


interactive fo_n4 : (* takes really long *)
   sequent ['ext] { >- (all w:'T. 'A4['w]) & (all x:'T. (('B0 or 'A0['x]) or 'B0)) & "not"{('B0 & (all y:'T. 'A1['y]))} & (all x:'T. (('B1 or 'A1['x]) or 'B1)) & "not"{('B1 & (all y:'T. 'A2['y]))} & (all x:'T. (('B2 or 'A2['x]) or 'B2)) & "not"{('B2 & (all y:'T. 'A3['y]))} & (all x:'T. (('B3 or 'A3['x]) or 'B3)) & "not"{('B3 & (all y:'T. 'A4['y]))} => all z:'T. 'A0['z] }




(* Some weired LJ deadlocks: *)
(* ------------------------- *)


(* These formulae show a deeper difference between the rule non-permutabilities *)
(* of the sequent calculi LJmc and LJ.*)
(* As a consequence, it requires the permutation-based proof transformations *)
(* from the papers [9,10], as documented in the file refiner/reflib/jall.mli. *)


(* deadlock1 is the example presented in the papers [9,10] *)

interactive deadlock1 :
   sequent ['ext] { >- (all x:'T. ('A['x] or 'B['x])) & ((exst y:'T. 'A['y]) => (exst z:'T. ("not"{'A['z]}))) => (exst x:'T. 'B['x]) }



interactive deadlock2 bind{x,y.'A['x;'y]} 'c :
   sequent ['ext] { >- (all x: 'T. all y:'T. ('P['x;'y] or 'B['x;'y])) & ((exst x:'T. exst y:'T. 'P['x;'y]) => (exst a:'T. 'A['a;'c])) & (all z:'T. ('A['z;'c] => (exst b:'T. "not"{('P['z;'b])}))) => exst x:'T. exst y:'T. 'B['x;'y] }



(* The following 6 examples refer to some permutation techniques from the papers [9,10] *)
(* -----------------------------------------------------------------------------------  *)


(* embedding LJ deadlocks into bigger non-deadlock proofs *)


interactive deadlock3 :
   sequent ['ext] { >- 'P & (all x:'T. ('A['x] or 'B['x])) & ((exst y:'T. 'A['y]) => (exst z:'T. ("not"{'A['z]}))) => (exst x:'T. 'B['x]) & 'P }


interactive deadlock4 :
   sequent ['ext] { >- (all x:'T. (('A['x] or 'B['x]) & 'P)) & ((exst y:'T. 'A['y]) => (exst z:'T. ("not"{'A['z]}))) => (exst x:'T. 'B['x]) & 'P }



(* ebedding multiple use of eigenvariable formula WITHOUT eigenvariable renaming *)


interactive mult_no_rename :
   sequent ['ext] { >- (all x:'T. ('A['x] or (exst a:'T. 'B['x;'a]))) & ((exst y:'T. 'A['y]) => (exst z:'T. ("not"{'A['z]}))) => (exst x:'T. exst y:'T. 'B['x;'y]) }

interactive mult_no_rename2 :
   sequent ['ext] { >- (all x:'T. ('A['x] or ('B['x] & (exst a:'T. 'C['a])))) & ((exst y:'T. 'A['y]) => (exst z:'T. ("not"{'A['z]}))) => (exst x:'T. ('B['x] & (exst z:'T. 'C['z]))) }



(* ebedding multiple use of eigenvariable formula WITH eigenvariable rule deletion, *)
(* i.e. the identical eigenvarieble rule occurs on the same branch *)

interactive mult_eigen_del :
   sequent ['ext] { >- (all x:'T. (('A['x] or 'B['x]) & (exst a:'T. 'C['a]))) & ((exst y:'T. 'A['y]) => (exst z:'T. ("not"{'A['z]}))) => (exst x:'T. ('B['x] & (exst z:'T. 'C['z]))) }



(* ebedding multiple use of eigenvariable formula WITH eigenvariable renaming *)

interactive mult_rename :
   sequent ['ext] { >- (all x:'T. (('A['x] or 'B['x]) & (exst a:'T. 'C['a;'x]))) & ((exst y:'T. 'A['y]) => (exst z:'T. ("not"{'A['z]}))) => (exst x:'T. ('B['x] & (exst z:'T. 'C['z;'x]))) }




(* The following does not use single-conclusion ITT - saved for future reference


jtest <<(('A or 'A) & ("not"{('A)} or 'A) => 'A)>> "J" "LJmc";;
jtest <<(("not"{('A)} or 'A) & ('A or 'A) => 'A)>> "J" "LJmc";;



Dealing with LJmc / LJ deadlocks -- beta proofs (also for single-conclusioned ITT!!!)
=====================================================================================


(* The following examples require some sophisticated techniques for *)
(* a complete and search-free proof reconstruction process. *)
(* Namely, the integration of additional knowledge from the proof search *)
(* process is needed, the so-called beta-proofs.*)
(* Details can be found in the papers [7,8] (although the examples there are in *)
(* modal logic T), as documented in the file refiner/reflib/jall.mli. *)


jtest <<(("not"{'A} or "not"{'D}) & ('A or 'B) & "not"{(('A or 'B) & 'B)} => "not"{'D})>> "J" "LJmc";;



(* Full deadlock in LJmc --> decomposition problem *)



jtest <<("not"{('B & ('A or 'B))} & ("not"{'A} or "not"{'D}) => "not"{('A or 'B)} or "not"{'D})>> "J" "LJmc";;




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



Propositional logic: ONLY clasically valid
===========================================



jtest << 'A or "not"{'A} >> "C" "LK";;
jtest << 'A or "not"{'A} >> "J" "LJmc";;   (* INVALID *)
jtest << 'A or "not"{'A} >> "J" "LJ";;     (* INVALID *)



jtest <<"not"{("not"{'A})} => 'A >> "C" "LK";;



simple test for search:
-----------------------


jtest << 'A  or ("not"{'A} & 'B) or ("not"{'B} & 'C) or("not"{'C} & 'D) or ("not"{'A}) >> "C" "LK";;




complete matrices:
------------------


n=2


jtest << ('A & 'B) or ('A & "not"{'B}) or ("not"{'A} & 'B) or ("not"{'A} & "not"{'B}) >> "C" "LK";;


n=3


<< ('A & 'B & 'C) or ('A & "not"{'B} & 'C) or ("not"{'A} & 'B & 'C) or ("not"{'A} & "not"{'B} & 'C) or ('A & 'B & "not"{'C}) or ('A & "not"{'B} & "not"{'C}) or ("not"{'A} & 'B & "not"{'C}) or ("not"{'A} & "not"{'B} & "not"{'C}) >>


n=4   (* Jprover cannot solve this -- I run it several days *)


jtest << ('A & 'B & "not"{'C} & 'D) or ('A & "not"{'B} & "not"{'C} & 'D) or ("not"{'A} & 'B & "not"{'C} & 'D) or ('A & 'B & 'C & 'D) or ('A & "not"{'B} & 'C & 'D) or ("not"{'A} & 'B & 'C & 'D) or ("not"{'A} & "not"{'B} & 'C & 'D) or ("not"{'A} & "not"{'B} & "not"{'C} & 'D) or ('A & 'B & 'C & "not"{'D}) or ('A & "not"{'B} & 'C & "not"{'D}) or ("not"{'A} & 'B & 'C & "not"{'D}) or ("not"{'A} & "not"{'B} & 'C & "not"{'D}) or ('A & 'B & "not"{'C} & "not"{'D}) or ('A & "not"{'B} & "not"{'C} & "not"{'D}) or ("not"{'A} & 'B & "not"{'C} & "not"{'D}) or ("not"{'A} & "not"{'B} & "not"{'C} & "not"{'D}) >> "C" "LK";;


jtest << ('A & 'B & "not"{'C} & 'D) or ('A & "not"{'B} & "not"{'C} & 'D) or ("not"{'A} & 'B & "not"{'C} & 'D) or ('A & 'B & 'C & 'D) or ('A & "not"{'B} & 'C & 'D) or ("not"{'A} & 'B & 'C & 'D) or ("not"{'A} & "not"{'B} & 'C & 'D) or ("not"{'A} & "not"{'B} & "not"{'C} & 'D) or ('A & 'B & 'C & "not"{'D}) or ('A & "not"{'B} & 'C & "not"{'D}) or ("not"{'A} & 'B & 'C & "not"{'D}) or ("not"{'A} & "not"{'B} & 'C & "not"{'D}) or ('A & 'B & "not"{'C} & "not"{'D}) or ('A & "not"{'B} & "not"{'C} & "not"{'D}) or ("not"{'A} & 'B & "not"{'C} & "not"{'D}) or ("not"{'A} & "not"{'B} & "not"{'C} & "not"{'D}) >> "C" "LK";;





First-order logic: ONLY clasically valid
==========================================

(* needs two instances of the exists-right formula *)


jtest << (exst x:'T. all y:'T. ('A['x] => 'A['y])) >> "C" "LK";;



First-order logic: INVALID
==========================

jtest << (exst x:'T. all y:'T. ('A['x,'y] => 'A['y,'x])) >> "C" "LK";;  (* INVALID *)


*)

interactive agatha 'H 'Butler 'Agatha 'Charles:
   sequent ['ext] {'H >- "type"{'Person} } -->
   sequent ['ext] {'H; x: 'Person >- "type"{'Lives['x]} } -->
   sequent ['ext] {'H; x: 'Person; y:'Person >- "type"{'Hates['x; 'y]} } -->
   sequent ['ext] {'H; x: 'Person; y:'Person >- "type"{'Richer['x; 'y]} } -->
   sequent ['ext] {'H; x: 'Person; y:'Person >- "type"{'Killed['x; 'y]} } -->
   sequent ['ext] {'H >- 'Butler in 'Person } -->
   sequent ['ext] {'H >- 'Agatha in 'Person } -->
   sequent ['ext] {'H >- 'Charles in 'Person } -->
   sequent ['ext] { 'H >-
      'Lives['Butler] =>
      'Hates['Agatha; 'Agatha] =>
      'Hates['Agatha; 'Charles] =>
      all x:'Person. (('Lives['x] => 'Hates['Butler; 'x]) or ('Richer['x; 'Agatha])) =>
      all x:'Person. ('Hates['Agatha; 'x] => not{'Hates['Charles; 'x]}) =>
      all x:'Person.(all y:'Person. ('Killed['x;'y] => 'Hates['x;'y])) =>
      all x: 'Person. (not{'Hates['x;'Agatha]} or not{'Hates['x;'Butler]} or not{'Hates['x;'Charles]}) =>
      all x: 'Person.(all y:'Person. ('Killed['x;'y] => not{'Richer['x;'y]})) =>
      all x: 'Person. ('Hates['Agatha;'x] => 'Hates['Butler; 'x]) =>
      ( not{'Killed['Butler; 'Agatha]} and not{'Killed['Charles; 'Agatha]} ) }

