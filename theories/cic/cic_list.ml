extends Cic_ind_type

define unfold_List: List <-->
	sequent [IndParams] { B: Set >-
	   sequent [IndTypes] { List: Set >-
		   sequent [IndConstrs] { nil: 'List ; cons: ('B -> 'List -> 'List) >- 'List}}}

define unfold_nil: nil <-->
	sequent [IndParams] { B: Set >-
	   sequent [IndTypes] { List: Set >-
		   sequent [IndConstrs] { nil: 'List; cons: 'B -> 'List -> 'List >- 'nil}}}

define unfold_cons: cons{'a; 'l} <-->
	sequent [IndParams] { B: Set >-
	   (sequent [IndTypes] { List: Set >-
		   (sequent [IndConstrs] { nil: 'List; cons: 'B -> 'List -> 'List >- 'cons 'a 'l })})}

dform list_df : List = `"List"
dform nil_df : nil = `"[]"
dform cons_df : cons{'a; 'l} = slot{'a} `"::" slot{'l}

interactive listDef_wf :
	sequent { <H> >-
	   sequent [IndParamsWF] { B : Set >-
			sequent [IndTypesWF] { List : Set >-
				sequent [IndConstrsWF] { nil: 'List ; cons: ('B -> 'List -> 'List) >- it } } } }

interactive list_wf :
   sequent { <H> >- List in (Set -> Set) }

interactive nil_wf :
   sequent { <H> >- 'C in Set } -->
   sequent { <H> >- nil in (List 'C) }

interactive cons_wf :
	sequent { <H> >- 'C in Set } -->
	sequent { <H> >- 'l in (List 'C) } -->
	sequent { <H> >- 'a in 'C } -->
	sequent { <H> >- cons{'a; 'l} in (List 'C) }


