extends Cic_ind_type
extends Cic_ind_cases
open Cic_ind_cases

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
dform cons_df : cons = `"cons"
dform cons_df : apply{apply{cons; 'a}; 'l} = slot{'a} `"::" slot{'l}

interactive listDef_wf :
	sequent { <H> >-
	   sequent [IndParamsWF] { B : Set >-
			sequent [IndTypesWF] { List : Set >-
				sequent [IndConstrsWF] { nil: 'List ; cons: ('B -> 'List -> 'List) >- it } } } }

interactive list_wf :
   sequent { <H> >- List in (Set -> Set) }

interactive nil_wf :
   sequent { <H> >- nil in (C:Set ->  (List 'C)) }

interactive cons_wf :
	sequent { <H> >- cons in (C:Set -> ('C -> (List 'C) -> (List 'C))) }

interactive foo :
sequent { <J> >-
	sequent [IndParamsSubst] { B: Set >-
	   sequent [IndTypesSubst] { List: Set >-
		   sequent [IndConstrsSubst] { nil: 'List ; cons: ('B -> 'List -> 'List) >- 'nil in 'List}}}
}

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
