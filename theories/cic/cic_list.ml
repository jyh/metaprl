extends Cic_ind_type
extends Cic_ind_elim
open Basic_tactics
open Dtactic

(*extends Cic_ind_cases
open Cic_ind_cases*)

extends Cic_ind_elim_dep
open Cic_ind_elim_dep

define unfold_List: List <-->
	sequent [IndParams] { B: Set >-
	   sequent [IndTypes] { List: Set >-
		   sequent [IndConstrs] { nil: 'List ; cons: ('B -> 'List -> 'List) >- 'List}}}

define unfold_nil: nil <-->
	sequent [IndParams] { B: Set >-
	   sequent [IndTypes] { List: Set >-
		   sequent [IndConstrs] { nil: 'List; cons: 'B -> 'List -> 'List >- 'nil}}}

define unfold_cons: cons <-->
	sequent [IndParams] { B: Set >-
	   (sequent [IndTypes] { List: Set >-
		   (sequent [IndConstrs] { nil: 'List; cons: 'B -> 'List -> 'List >- 'cons })})}

dform list_df : List = `"List"
dform nil_df : nil = `"[]"
dform nil_app_df : (nil 'T) = `"[]_" slot{'T}
dform cons_df : cons = `"cons"
dform cons_app_df : apply{apply{apply{cons;'T}; 'a}; 'l} = slot{'a} `" ::_" slot{'T} " " slot{'l}

interactive listDef_wf {| intro [] |} :
	sequent { <H> >-
	   sequent [IndParamsWF] { B : Set >-
			sequent [IndTypesWF] { List : Set >-
				sequent [IndConstrsWF] { nil: 'List ; cons: ('B -> 'List -> 'List) >- it } } } }

interactive list_wf {| intro [] |} :
   sequent { <H> >- List in (Set -> Set) }

interactive nil_wf {| intro [] |} :
   sequent { <H> >- nil in (C:Set ->  (List 'C)) }

interactive cons_wf {| intro [] |} :
	sequent { <H> >- cons in (C:Set -> ('C -> (List 'C) -> (List 'C))) }

interactive foo :
sequent { <J> >-
	sequent [IndParamsSubst] { B: Set >-
	   sequent [IndTypesSubst] { List: Set >-
		   sequent [IndConstrsSubst] { nil: 'List ; cons: ('B -> 'List -> 'List) >- 'nil in 'List}}}
}

(*
prim case_wf 'A 's :
	sequent { <H> >- 'l in (List 'A) } -->
	sequent { <H> >- 'P in ((List 'A) -> 's) } -->
	sequent { <H> >- is_sort{'s} } -->
	sequent { <H> >- 'f1 in ('P (nil 'A)) } -->
	sequent { <H> >- 'f2 in ( a:'A -> l:(List 'A) -> ('P (cons 'A 'a 'l))) } -->
	sequent { <H> >- case{'l;'P; sequent [cases] { 'f1; 'f2 >- it} } in ('P 'l) } = it

prim_rw nil_reduce :
	case{nil 'A;'P; sequent [cases] { 'f1; 'f2 >- it} } <-->
	'f1

prim_rw cons_reduce :
	case{cons 'A 'a 'l;'P; sequent [cases] { 'f1; 'f2 >- it} } <-->
	('f2 'a 'l)
*)

interactive list_nodep_elim_wf {| intro [] |} :
	sequent { <H> >- 'A in Set } -->
	sequent { <H> >- 'l in (List 'A) } -->
	sequent { <H> >- 'Q in (Set -> Prop) } -->
	sequent { <H> >- 'base in ('Q 'A) } -->
	sequent { <H>; a: 'A; l: (List 'A) >- 'step in ('Q 'A 'a 'l) } -->
	sequent { <H> >- Elim{'l; ElimPredicates{| p:'Q >- it|}; ElimCases{| x:'base; y:'step >- it|}} in ('Q 'A) }

interactive list_dep_elim_prop_wf {| intro [] |} :
	sequent { <H> >- 'A in Set } -->
	sequent { <H> >- 'l in (List 'A) } -->
	sequent { <H> >- 'Q in (a: Set -> (List 'a) -> Prop) } -->
	sequent { <H> >- 'base in (C: Set -> ('Q 'C (nil 'C))) } -->
	sequent { <H> >- 'step in (C: Set -> a: 'C -> l: (List 'C) -> ('Q 'C 'l) -> ('Q 'C (cons 'C 'a 'l))) } -->
	sequent { <H> >- Elim{'l; ElimPredicates{| p:'Q >- it|}; ElimCases{| x:'base; y:'step >- it|}} in ('Q 'A 'l) }

interactive list_dep_elim_set_wf {| intro [] |} :
	sequent { <H> >- 'A in Set } -->
	sequent { <H> >- 'l in (List 'A) } -->
	sequent { <H> >- 'Q in (a: Set -> (List 'a) -> Set) } -->
	sequent { <H> >- 'base in (C: Set -> ('Q 'C (nil 'C))) } -->
	sequent { <H> >- 'step in (C: Set -> a: 'C -> l: (List 'C) -> ('Q 'C 'l) -> ('Q 'C (cons 'C 'a 'l))) } -->
	sequent { <H> >- Elim{'l; ElimPredicates{| p:'Q >- it|}; ElimCases{| x:'base; y:'step >- it|}} in ('Q 'A 'l) }


interactive_rw elim_nil :
	Elim{nil 'A; ElimPredicates{| p:'Q >- it|}; ElimCases{| 'base; 'step >- it|}} <-->
	('base 'A)

interactive_rw elim_cons :
	Elim{cons 'A 'a 'l; ElimPredicates{| p:'Q >- it|}; ElimCases{| 'base; 'step >- it|}} <-->
	('step 'A 'a 'l Elim{'l; ElimPredicates{| p:'Q >- it|}; ElimCases{| 'base; 'step >- it|}})
(*
define unfold_append : append <-->
	lambda{}
	Elim{
		'l;
		ElimPredicates{|lambda{Set; C.lambda{List 'C; List }} >-it|};
		ElimCases{|nil; lambdaH{|C: Set; a: 'C; l: List 'C; fix: Q C 'l >- cons 'C ('f 'a) 'fix|} >-it|}
	}

define unfold_map : map <-->
	lambdaH{|A: Set; B: Set; f: 'A -> 'B; l: List 'A >-
		Elim{
			'l;
			ElimPredicates{|lambda{Set; C.lambda{List 'C; List }} >-it|};
			ElimCases{|nil; lambdaH{|C: Set; a: 'C; l: List 'C; fix: Q C 'l >- cons 'C ('f 'a) 'fix|} >-it|}
		}
	|}
*)

(*
cons in (C:Set -> ('C -> (List 'C) -> (List 'C)))
*)

interactive prodH_test1 :
	sequent { <H> >- prodH{|x: 'A >- 'x |} }

interactive prodH_test2 :
	sequent { <H> >- prodH{|x: 'A >- Set |} }

define unfold_nat: nat <-->
	sequent [IndParams] { >-
	   sequent [IndTypes] { nat: Set >-
		   sequent [IndConstrs] { zero: 'nat ; succ: ('nat -> 'nat) >- 'nat}}}

define unfold_zero: zero <-->
	sequent [IndParams] { >-
	   sequent [IndTypes] { nat: Set >-
		   sequent [IndConstrs] { zero: 'nat ; succ: ('nat -> 'nat) >- 'zero}}}

define unfold_succ: succ <-->
	sequent [IndParams] { >-
	   sequent [IndTypes] { nat: Set >-
		   sequent [IndConstrs] { zero: 'nat ; succ: ('nat -> 'nat) >- 'succ}}}

interactive nat_wf {| intro [] |} :
   sequent { <H> >- nat in Set }

interactive zero_wf {| intro [] |} :
   sequent { <H> >- zero in nat }

interactive succ_wf {| intro [] |} :
	sequent { <H> >- succ in (nat -> nat) }

define unfold_Listn: Listn <-->
	sequent [IndParams] { A : Set >-
	   sequent [IndTypes] { Listn: nat -> Set >-
		   sequent [IndConstrs] { niln: ('Listn zero) ; consn: (n: nat -> 'A -> ('Listn 'n) -> ('Listn (succ 'n))) >- 'Listn}}}

define unfold_niln : niln <-->
	sequent [IndParams] { A : Set >-
	   sequent [IndTypes] { Listn: nat -> Set >-
		   sequent [IndConstrs] { niln: ('Listn zero) ; consn: (n: nat -> 'A -> ('Listn 'n) -> ('Listn (succ 'n))) >- 'niln}}}

define unfold_consn : consn <-->
	sequent [IndParams] { A : Set >-
	   sequent [IndTypes] { Listn: nat -> Set >-
		   sequent [IndConstrs] { niln: ('Listn zero) ; consn: (n: nat -> 'A -> ('Listn 'n) -> ('Listn (succ 'n))) >- 'consn}}}

interactive listn_wf {| intro [] |} :
   sequent { <H> >- Listn in (Set -> nat -> Set) }

interactive niln_wf {| intro [] |} :
   sequent { <H> >- niln in (A:Set -> (List 'A zero)) }

interactive consn_wf {| intro [] |} :
	sequent { <H> >- cons in (A:Set -> n:nat -> 'A -> (Listn 'A 'n) -> (Listn 'A (succ 'n))) }
