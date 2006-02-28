extends Itt_ring_uce
extends Itt_mpoly2

open Basic_tactics

open Itt_equal
open Itt_struct
open Itt_list
open Itt_list2
open Itt_int_base
open Itt_int_ext
open Itt_int_arith
open Itt_mpoly2

interactive dualSubst 'H :
	sequent { <H>; 'a1 >= 'b1; <J>; 'a='a1<|H|> in Z^car; 'b='b1<|H|> in Z^car >- 'C } -->
	sequent { <H>; 'a >= 'b; <J>; 'a='a1<|H|> in Z^car; 'b='b1<|H|> in Z^car >- 'C }

let rec int_list n =
	if n=0 then [0]
	else
		let n'=pred n in
		n' :: (int_list n')

let stdT i = funT (fun p ->
	let i = Sequent.get_pos_hyp_num p i in
	let t = if i=0 then Sequent.concl p else Sequent.nth_hyp p i in
	let a,b = dest_ge t in
	let vars0 = vars_of_term (empty ()) <<Z>> a in
	let vars1 = vars_of_term vars0 <<Z>> b in
	let vars2 = var_list vars1 in
	let vars = List.filter (fun x -> not (is_number_term x)) vars2 in
	let varlist = mk_list_of_list vars in
	let len = mk_length_term varlist in
	let len_wf = mk_equal_term <<nat>> len len in
	let mpoly_t = mk_mpolyTerm_term <<Z>> len in
	let var_terms = List.map (fun i -> mk_varTerm_term (mk_intnum_term i)) (int_list (List.length vars)) in
	assertT <<Z in unitringCE[i:l]>> thenMT
	proveVarTypesT <<Z^car>> vars thenMT
	assertT len_wf thenMT
	proveVarTypesT mpoly_t var_terms thenMT
	standardizeT <<unitringCE[i:l]>> <<Z>> <<Z^car>> vars varlist a thenMT
	standardizeT <<unitringCE[i:l]>> <<Z>> <<Z^car>> vars varlist b thenMT
	dualSubst i thenMT
	(thinT (-1) thenT thinT (-1)) thenMT
	rw reduceC i
)

interactive_rw fold_add :
	('a +@ 'b) <--> ('a +[Z] 'b)

interactive_rw fold_mul :
	('a *@ 'b) <--> ('a *[Z] 'b)

let prepareT i = rw ((addrC [Subterm 1] reduceC) thenC (addrC [Subterm 2] reduceC)) i thenMT rw (sweepDnC fold_add) i thenMT rw (sweepDnC fold_mul) i

(*
let arithT = preArithT thenMT reduceContradRelT (-1)
let arithAT = arithT ttca
*)

let arithT = preArithT thenMT prepareT (-1) thenMT stdT (-1)
(*let arithAT = arithT ta thenT repeatT (rw reduceC 0) ttca*)
(*let arithAT = arithT ta thenT rw mpoly_evalC 0 ttca*)
let arithAT = arithT ttca


interactive test 'a 'b 'c :
sequent { <H> >- 'a in int } -->
sequent { <H> >- 'b in int } -->
sequent { <H> >- 'c in int } -->
sequent { <H>; x: ('a >= ('b +@ 1));
                     t: ('c >= ('b +@ 3));
                     u: ('b >= ('a +@ 0))
                >- "assert"{bfalse} }

interactive test2 'a 'b 'c :
sequent { <H> >- 'a in int } -->
sequent { <H> >- 'b in int } -->
sequent { <H> >- 'c in int } -->
sequent { <H>; x: (('b +@ 1) <= 'a);
                     t: ('c > ('b +@ 2));
                     u: ('b >= ('a +@ 0))
                >- "assert"{bfalse} }

interactive test3 'a 'b 'c :
sequent { <H> >- 'a in int } -->
sequent { <H> >- 'b in int } -->
sequent { <H> >- 'c in int } -->
sequent { <H>; x: (('b +@ 1) <= 'a);
                     t: ('c > ('b +@ 2))
                >- ('b < ('a +@ 0))  }

interactive test4 'a 'b :
sequent { <H> >- 'a in int } -->
sequent { <H> >- 'b in int } -->
sequent { <H>; x: ('a >= 'b);
                     t: ('a < 'b)
                >- "assert"{bfalse} }

interactive test5 'a 'b :
sequent { <H> >- 'a in int } -->
sequent { <H> >- 'b in int } -->
sequent { <H>; x: ('a >= 'b +@ 0);
                     t: ('a < 'b)
                >- "assert"{bfalse} }

interactive test6 'b 'c :
sequent { <H> >- 'a in int } -->
sequent { <H> >- 'b in int } -->
sequent { <H> >- 'c in int } -->
sequent { <H>; x: (('c *@ ('b +@ ('a *@ 'c)) +@ ('b *@ 'c)) >= 'b +@ 0);
                     t: (((((('c *@ 'b) *@ 1) +@ (2 *@ ('a *@ ('c *@ 'c)))) +@
 (('c *@ ((-1) *@ 'a)) *@ 'c)) +@ ('b *@ 'c)) < 'b)
                >- "assert"{bfalse} }

interactive test7 :
sequent { <H> >- 'a in int } -->
sequent { <H> >- 'b in int } -->
sequent { <H>; 'a < 'b >- 'a <> 'b }

interactive test8 :
sequent { <H> >- 'a in int } -->
sequent { <H> >- 'b in int } -->
sequent { <H>; 'a < 'b >- not{'a = 'b in int} }

interactive test9 :
sequent { <H> >- 'a in int } -->
sequent { <H> >- 'b in int } -->
sequent { <H>; not{'a < 'b} >- 'a >= 'b }

interactive test10 :
sequent { <H> >- 'a in int } -->
sequent { <H> >- 'b in int } -->
sequent { <H>; 'a <> 'b >- 'a <> 'b }

interactive testn :
	sequent {'v  in int;
				'v1 in int;
				'v2 in int;
				'v3 in int;
				'v4 in int;
				'v5 in int;
				'v6 in int;
				'v7 in int;
				'v8 in int;
				'v9 in int; "assert"{bfalse} >- "assert"{bfalse} }
