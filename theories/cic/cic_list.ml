extends Cic_ind_type

define unfold_List: List <-->
	sequent [IndParams] { A: Set >-
	   sequent [IndTypes] { List: Set >-
		   sequent [IndConstrs] { nil: 'List ; cons: ('A -> 'List -> 'List) >- 'List}}}

define unfold_nil: nil <-->
	sequent [IndParams] { A: Set >-
	   sequent [IndTypes] { List: Set >-
		   sequent [IndConstrs] { nil: 'List; cons: 'A -> 'List -> 'List >- 'nil}}}

define unfold_cons: cons{'a; 'l} <-->
	sequent [IndParams] { A: Set >-
	   (sequent [IndTypes] { List: Set >-
		   (sequent [IndConstrs] { nil: 'List; cons: 'A -> 'List -> 'List >- 'cons 'a 'l })})}

dform list_df : List = `"List"
dform nil_df : nil = `"[]"
dform cons_df : cons{'a; 'l} = slot{'a} `"::" slot{'l}

interactive list_wf :
   sequent { <H> >- 'A in Set } -->
	sequent { <H> >- List in ('A -> Set) }

interactive nil_wf :
   sequent { <H> >- 'A in Set } -->
   sequent { <H> >- nil in (List 'A) }
