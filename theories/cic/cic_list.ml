extends Cic_ind_type

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
   sequent { <H> >- nil in dfun{Set; C.(List 'C)} }

interactive cons_wf :
	sequent { <H> >- cons in dfun{Set; C.('C -> (List 'C) -> (List 'C))} }
