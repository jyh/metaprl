extends Cic_ind_type

define unfold_List: List <-->
	sequent [IndParams] { A: Set >-
	   sequent [IndTypes] { List: Set >-
		   sequent [IndConstrs] { nil: 'List ; cons: ('A -> 'List -> 'List) >- it}}}

define unfold_nil: nil <-->
	sequent [IndParams] { A: Set >-
	   sequent [IndTypes] { List: Set >-
		   sequent [IndConstrs] { nil: 'List; cons: 'A -> 'List -> 'List >- 'nil}}}

define unfold_cons: cons{'a; 'l} <-->
	sequent [IndParams] { A: Set >-
	   (sequent [IndTypes] { List: Set >-
		   (sequent [IndConstrs] { nil: 'List; cons: 'A -> 'List -> 'List >- 'cons 'a 'l })})}

interactive list_wf :
   sequent { <H> >- 'A in Set } -->
	sequent { <H> >- List in ('A -> Set) }

interactive nil_wf :
   sequent { <H> >- 'A in Set } -->
   sequent { <H> >- nil in (List 'A) }
