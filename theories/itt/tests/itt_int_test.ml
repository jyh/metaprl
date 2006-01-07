extends Itt_struct
extends Itt_int_ext
extends Itt_int_arith
extends Itt_supinf
extends Itt_omega

open Lm_debug
open Lm_printf
open Lm_num
open Basic_tactics

open Itt_struct
open Itt_int_base
open Itt_int_ext
open Itt_int_arith
open Itt_supinf
open Itt_omega

let debug_test_arith =
   create_debug (**)
      { debug_name = "test_arith";
        debug_description = "Use arithT to prove tests";
        debug_value = false
      }

let debug_test_supinf =
   create_debug (**)
      { debug_name = "test_supinf";
        debug_description = "Use Itt_supinf to prove tests";
        debug_value = false
      }

let debug_test_omega =
   create_debug (**)
      { debug_name = "test_omega";
        debug_description = "Use omegaT to prove tests";
        debug_value = true
      }

let debug_test_no_ttca =
   create_debug (**)
      { debug_name = "test_no_ttca";
        debug_description = "Do not use ttca as a suffix to prove tests";
        debug_value = false
      }

let test tac = funT (fun p ->
	if !debug_test_no_ttca then
		tac
	else
		tac ttca
)

let testT = funT (fun p ->
	if !debug_test_supinf then
		test supinfT
	else if !debug_test_omega then
		test omegaT
	else if !debug_test_arith then
		test arithT
	else
		begin
			eprintf "Itt_int_test.testT: No tactic has been chosen@.";
			failT
		end
)

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

interactive test11 :
	sequent { <H> >- 'a in int } -->
	sequent { <H> >- 'b in int } -->
	sequent { <H> >- 'c in int } -->
	sequent { <H>; 'a +@ 'b >= 'c; 'c >= 'a +@ 'b +@ 1 >- "false" }

interactive test12 :
	sequent { <H> >- 'a in int } -->
	sequent { <H>; 3 *@ 'a >= 1; 1 >= 2 *@ 'a >- "false" }

interactive test13 :
	sequent { <H> >- 'a in int } -->
	sequent { <H>; 'a >= 0;
                  1 >= 5 *@ 'a
						>- "assert"{bfalse} }

interactive test14 :
	sequent { <H>; 'a in int >- 2 *@ 'a = (2 *@ 'a) +@ 0 in int }

interactive test15 :
	sequent { <H>; 'a in int >- 2 *@ 'a <> (2 *@ 'a) +@ 1 }

let rec gen_term nvars vars intrange maxdepth =
	let choice=Random.int 2 in
	if maxdepth>0 && choice=0 then
		mk_add_term (gen_term nvars vars intrange (maxdepth-1)) (gen_term nvars vars intrange (maxdepth-1))
	else if maxdepth>0 && choice=1 then
		mk_mul_term (gen_term nvars vars intrange (maxdepth-1)) (gen_term nvars vars intrange (maxdepth-1))
	else
		let choice=Random.int 1 in
		if choice=0 then
			let i=Random.int (nvars-1) in
			vars.(i)
		else
			mk_number_term (num_of_int (Random.int intrange))

let gen_ineq nvars intrange =
	(Random.int (nvars-1), Random.int (nvars-1), Random.int intrange)

let rec gen nvars intrange left =
	if left=0 then []
	else (gen_ineq nvars intrange)::(gen nvars intrange (left-1))

let triple2term vars (v1,v2,n) =
	mk_ge_term vars.(v1) (mk_add_term vars.(v2) (mk_number_term (num_of_int n)))

let rec assertListT vars = function
	[triple] -> assertT (triple2term vars triple)
 | hd::tl -> assertT (triple2term vars hd) thenMT (assertListT vars tl)
 | _ -> failT

let genT vl seed nvars nineq intrange maxdepth =
	Random.init seed;
	let vars=Array.of_list vl in
(*	let vars=Array.init nvars (fun i -> mk_var_term (Lm_symbol.make "v" i)) in*)
	let terms=Array.init nvars (fun i -> gen_term nvars vars intrange maxdepth) in
	let l=gen nvars intrange nineq in
	assertListT terms l

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
