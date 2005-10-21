open Printf

(******************************************
 * Benchmark
 ******************************************)

let print_var co k v =
	if v = 0 then
		fprintf co "%i" k
	else
		fprintf co "%i *@ 'v%i" k v

type expr = Var of int * int | Add of expr * expr

let rec print_expr co = function
	Var(k,v) -> print_var co k v
 | Add(e1,e2) -> fprintf co "(%a) +@ (%a)" print_expr e1 print_expr e2

let rec gen_expr nvars intrange maxdepth =
	if maxdepth>0 && (Random.bool ()) then
		Add(gen_expr nvars intrange (maxdepth-1), gen_expr nvars intrange (maxdepth-1))
	else
		Var(Random.int intrange, Random.int (nvars+1))

let print_seq printer co arg =
	fprintf co "sequent { <H> >- %a }" printer arg

let print_assum printer co arg =
	fprintf co "%a -->\n" (print_seq printer) arg

let print_decl co v =
	fprintf co "v%i : int; " v

let print_goal co printer =
	fprintf co "sequent { %t >- \"false\" }\n" printer

type ineq = Ge | Gt | Le | Lt | Eq | Ne

let gen_ineq () =
	match Random.int 6 with
		0 -> Ge
	 | 1 -> Gt
	 | 2 -> Le
	 | 3 -> Lt
	 | 4 -> Eq
	 | _ -> Ne

let print_ineq ineq e1 e2 co =
	match ineq with
		Ge -> fprintf co "%a >= %a" print_expr e1 print_expr e2
	 | Gt -> fprintf co "%a > %a" print_expr e1 print_expr e2
	 | Le -> fprintf co "%a <= %a" print_expr e1 print_expr e2
	 | Lt -> fprintf co "%a < %a" print_expr e1 print_expr e2
	 | Eq -> fprintf co "%a = %a in int" print_expr e1 print_expr e2
	 | Ne -> fprintf co "%a <> %a" print_expr e1 print_expr e2

let print_all nineq nvars intrange maxdepth co =
	for i=1 to nvars do
		print_decl co i
	done;
	for i=1 to nineq do
		let e1 = gen_expr nvars intrange maxdepth in
		let e2 = gen_expr nvars intrange maxdepth in
		let ineq = gen_ineq () in
		fprintf co "\n%t" (print_ineq ineq e1 e2);
		if i<nineq then
			fprintf co ";"
	done

let gen_rule co n nineq nvars intrange maxdepth =
	fprintf co "\ninteractive test%i :\n" n;
	print_goal co (print_all nineq nvars intrange maxdepth)

let gen_bench ~name ~seed ~nrules ~nineq ~nvars ~intrange ~maxdepth =
	Random.init seed;
	let co = open_out name in
	fprintf co "extends Itt_int_test\n\n";
	fprintf co "open Itt_int_test\n\n";
	for i=0 to nrules - 1 do
		gen_rule co i nineq nvars intrange maxdepth
	done;
	flush co

(* XXX: JYH: is there some reason to go up and back down for these pathnames? *)
let _ = gen_bench ~name:"../../../theories/itt/tests/itt_int_bench.ml"
	~seed:0 ~nrules:10 ~nineq:10 ~nvars:5 ~intrange:10 ~maxdepth:3

let _ = gen_bench ~name:"../../../theories/itt/tests/itt_int_bench2.ml"
	~seed:0 ~nrules:10 ~nineq:15 ~nvars:5 ~intrange:10 ~maxdepth:2

let _ = gen_bench ~name:"../../../theories/itt/tests/itt_int_bench3.ml"
	~seed:0 ~nrules:100 ~nineq:15 ~nvars:5 ~intrange:10 ~maxdepth:2
