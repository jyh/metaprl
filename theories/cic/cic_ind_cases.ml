extends Cic_ind_type
open Basic_tactics
open Dtactic
open Cic_lambda
open Cic_ind_type

declare case{'t;'P;'F}
(*declare cases*)
declare sequent [cases] { Term : Term >- Term } : Term

let case_term = << case{'t; 'P; 'F} >>
let case_opname = opname_of_term case_term
let is_case_term = is_dep0_dep0_dep0_term case_opname
let dest_case = dest_dep0_dep0_dep0_term case_opname
let mk_case_term = mk_dep0_dep0_dep0_term case_opname

declare brackets{'I;'A;'B}

let brackets3_term = << brackets{'I; 'A; 'B} >>
let brackets3_opname = opname_of_term brackets3_term
let is_brackets3_term = is_dep0_dep0_dep0_term brackets3_opname
let dest_brackets3 = dest_dep0_dep0_dep0_term brackets3_opname
let mk_brackets3_term = mk_dep0_dep0_dep0_term brackets3_opname

declare brackets{'I;'A}
let brackets2_term = << brackets{'I; 'A} >>
let brackets2_opname = opname_of_term brackets2_term
let is_brackets2_term = is_dep0_dep0_term brackets2_opname
let dest_brackets2 = dest_dep0_dep0_term brackets2_opname
let mk_brackets2_term = mk_dep0_dep0_term brackets2_opname

(*declare branchCases*)
declare sequent [branchCases] { Term : Term >- Term } : Term
declare sequent [branchConstrs] { Term : Term >- Term } : Term

declare emptyDef{'I}
declare singletonDef{'I}

declare with_sort{s.'T['s]}

prim with_sortSet {| intro [AutoMustComplete] |} :
	sequent { <H> >- 'T[Set] } -->
	sequent { <H> >- with_sort{s.'T['s]} } = it

prim with_sortProp {| intro [AutoMustComplete] |} :
	sequent { <H> >- 'T[Prop] } -->
	sequent { <H> >- with_sort{s.'T['s]} } = it

prim with_sortType "type"[i:l] :
	sequent { <H> >- 'T["type"[i:l]] } -->
	sequent { <H> >- with_sort{s.'T['s]} } = it

(* definition of a relation [I:A|B] *)

(* derivation rule [(I x) : A'|B']
                   ---------------  denotation (--->)
					 [I : (x:A)A'|(x:A)B']   *)
prim bracketsProd {| intro [] |} :
	sequent { <H>; x:'C >- brackets{'I 'x; 'A['x]; 'B['x]} } -->
	sequent { <H> >- brackets{'I;(x:'C -> 'A['x]); (x:'C -> 'B['x])} } = it

prim_rw bracketsProd_rw (*{| reduce |}*) :
	sequent { <H> >- brackets{'I;(x:'C -> 'A['x]); (x:'C -> 'B['x])} } <-->
	sequent { <H>; x:'C >- brackets{'I 'x; 'A['x]; 'B['x]} }

prim_rw bracketsProd2_rw {| reduce |} :
	brackets{'I; (x:'C -> 'A['x])} <-->
	(x: 'C -> brackets{'I 'x; 'A['x]})

(* [I:Set | I -> Prop] *)
prim bracketsSetProp {| intro [] |} :
	sequent { <H> >- brackets{'I;Set;'I -> Prop} } = it

prim_rw bracketsSetProp_rw (*{| reduce |}*) :
	sequent { <H> >- brackets{'I;Set;'I -> Prop} } <-->
	sequent { <H> >- it }

prim_rw bracketsSet2_rw {| reduce |} :
	brackets{'I;Set} <--> with_sort{s.('I -> 's)}

(* [I:Set | I -> Prop] *)
prim bracketsSetSet {| intro [] |} :
	sequent { <H> >- brackets{'I;Set;'I -> Set} } = it

prim_rw bracketsSetSet_rw (*{| reduce |}*) :
	sequent { <H> >- brackets{'I;Set;'I -> Set} } <-->
	sequent { <H> >- it }

(*! I is a small inductive definition s belongs to {Type(i)} --->
   [I : Set | I- > s]*)
prim bracketsSetType {| intro [] |} :
	sequent { <H> >- brackets{'I;Set;'I -> "type"[i:l]} } = it

prim_rw bracketsSetType_rw (*{| reduce |}*) :
	sequent { <H> >- brackets{'I;Set;'I -> "type"[i:l]} } <-->
	sequent { <H> >- it }

prim bracketsTypeProp {| intro [] |} :
	sequent { <H> >- brackets{'I;"type"[j:l];'I -> Prop} } = it

prim_rw bracketsTypeProp_rw (*{| reduce |}*) :
	sequent { <H> >- brackets{'I;"type"[j:l];'I -> Prop} } <-->
	sequent { <H> >- it }

prim bracketsTypeSet {| intro [] |} :
	sequent { <H> >- brackets{'I;"type"[j:l];'I -> Set} } = it

prim_rw bracketsTypeSet_rw (*{| reduce |}*) :
	sequent { <H> >- brackets{'I;"type"[j:l];'I -> Set} } <-->
	sequent { <H> >- it }

prim bracketsTypeType {| intro [] |} :
	sequent { <H> >- brackets{'I;"type"[j:l];'I -> "type"[i:l]} } = it

prim_rw bracketsTypeType_rw (*{| reduce |}*) :
	sequent { <H> >- brackets{'I;"type"[j:l];'I -> "type"[i:l]} } <-->
	sequent { <H> >- it }

prim_rw bracketsType2_rw {| reduce |} :
	brackets{'I;"type"[j:l]} <--> with_sort{s.('I -> 's)}

prim bracketsProp {| intro [] |} :
	sequent { <H> >- brackets{'I;Prop;'I -> Prop} } = it

prim_rw bracketsProp_rw (*{| reduce |}*) :
	sequent { <H> >- brackets{'I;Prop;'I -> Prop} } <-->
	sequent { <H> >- it }

prim_rw bracketsProp2_rw {| reduce |} :
	brackets{'I;Prop} <--> ('I -> Prop)

let reduce_bracketsC = repeatC (higherC (firstC [bracketsProd2_rw; bracketsSet2_rw; bracketsType2_rw; bracketsProp2_rw]))

prim emptyDefSimple :
	sequent { <H> >-
	   sequent [IndParamsWF] { <Hp> >-
		   sequent [IndTypesWF] { I: 'A >-
	         sequent [IndConstrsWF] { >- it } }}}   -->
	sequent { <H> >-
	   sequent [IndParamsSubst] { <Hp> >-
		   sequent [IndTypesSubst] { I: 'A >-
	         sequent [IndConstrsSubst] { >- emptyDef{'I} } } } } = it

(*
prim emptyDefMutual :
	sequent { <H> >-
	   sequent [IndParamsWF] { <Hp> >-
		   sequent [IndTypesWF] { <Hi>; I: 'A; <Ji> >-
	         sequent [IndConstrsWF] { <Hc['I]> >- it } }}}   -->
	sequent { <H> >-
	   sequent [IndParamsSubst] { <Hp> >-
		   sequent [IndTypesSubst] { <Hi>; I: 'A; <Ji> >-
	         sequent [IndConstrsSubst] { <Hc['I]> >- emptyDef{'I} } } } } = it
*)


(*declare branchType*)
declare branchType{'P;'c;'C}
declare sequent [branchType] { Term : Term >- Term } : Term

prim_rw branchTypeApp :
	sequent [branchType] { <Hp> >-
		branchType{ 'P<||>; 'c<||>; sequent [applH] { <Hp>;<T<| |> > >- 'I} } } <-->
	sequent [applH] { <T>; 'c >- 'P }

prim_rw branchTypeFun :
	sequent [branchType] { <Hp> >-
		branchType{ 'P<||>; 'c<||>; (x:'T<||> -> 'C['x]) } } <-->
	(x: 'T -> sequent [branchType] { <Hp> >- branchType{'P; 'c 'x; 'C['x]}} )

let reduce_branchType = repeatC (higherC (firstC [branchTypeApp; branchTypeFun]))

let branchType_term = << branchType{'P; 'c; 'C} >>
let branchType_opname = opname_of_term branchType_term
let is_branchType_term = is_dep0_dep0_dep0_term branchType_opname
let dest_branchType = dest_dep0_dep0_dep0_term branchType_opname
let mk_branchType_term = mk_dep0_dep0_dep0_term branchType_opname

let mk_branchType_sequent args p c c_type =
	let br = mk_branchType_term p c c_type in
	let label = <<branchType>> in
	TermMan.mk_sequent_term {sequent_args=label; sequent_hyps=args; sequent_concl = br}

(*
prim branchTypes :
	f in  sequent [branchType] { <Hp> >-
		branchType{'P; sequent[applH]{ <Hp> >- 'c}; sequent[applH]{ <Hp> >- 'C} } } -->
	sequent { <H> >-
		sequent [IndParams] { <Hp> >-
			sequent [IndTypes] { <Hi>; I: 'A<|H|>; <Ji<|H|> > >-
				sequent [IndConstrs] { <Hc['I]>; c: 'C['I]; <Jc['I]> >-
					sequent [branchConstrs] { <HcI>; 'C['I] >-
						sequent [branchCases] { <F>; 'f >- 'P} } } } } }
*)


(**********************************************************************
 *    typing rules for case-analysis                                  *
 **********************************************************************)

prim indCases 'Hi 'B sequent [branchConstrs] { <HcI> >- it } :
	sequent { <H> >-
	   sequent [IndParamsWF] { <Hp> >-
			sequent [IndTypesWF] { <Hi>; I: 'A<|H|>; <Ji<|H|> > >-
				sequent [IndConstrsWF] { <Hc['I]> >- it } } } } -->
	sequent { <H> >-
		sequent [IndParams] { <Hp> >-
			sequent [IndTypes] { <Hi>; I: 'A<|H|>; <Ji<|H|> > >-
				sequent [IndConstrs] { <Hc['I]> >-
					'c in sequent [applH] { <Hp>; <T> >- 'I } } } } } -->
	sequent { <H> >-
		sequent [IndParams] { <Hp> >-
			sequent [IndTypes] { <Hi>; I: 'A<|H|>; <Ji<|H|> > >-
				sequent [IndConstrs] { <Hc['I]> >-
					'P in 'B } } } } -->
	sequent { <H> >-
		sequent [IndParams] { <Hp> >-
			sequent [IndTypes] { <Hi>; I: 'A<|H|>; <Ji<|H|> > >-
				sequent [IndConstrs] { <Hc['I]> >-
					brackets{sequent [applH] { <Hp> >- 'I }; 'B} } } } } -->
	sequent { <H> >-
		sequent [IndParams] { <Hp> >-
			sequent [IndTypes] { <Hi>; I: 'A<|H|>; <Ji<|H|> > >-
				sequent [IndConstrs] { <Hc['I]> >-
					sequent [branchConstrs] { <HcI> >-
						sequent [branchCases] { <F> >- 'P} } } } } } -->
	sequent { <H> >-
		sequent [IndParams] { <Hp> >-
			sequent [IndTypes] { <Hi>; I: 'A<|H|>; <Ji<|H|> > >-
				sequent [IndConstrs] { <Hc['I]> >-
					case{'c;'P; sequent [cases] { <F> >- it} }
					in (sequent [applH] { <T>; 'c >- 'P }) } } } } = it

open Lm_printf
open Simple_print

let print_hyp = function
	Hypothesis (v,t) ->
		eprintf "%a : %s; "
			Lm_symbol.output_symbol v
			(SimplePrint.short_string_of_term t)
 | Context (c,_,_) ->
		eprintf "%a; " Lm_symbol.output_symbol c

let print_hyps hyps =
	SeqHyp.iter print_hyp hyps;
	eprintf "@."

(* *)

let rec type_of_constr indName ctype =
   match explode_term ctype with
		<< 'f 'p >> -> type_of_constr indName f
	 | << x: 't -> 'c >> -> type_of_constr indName c
	 | << 't -> 'c >> -> type_of_constr indName c
	 | _ ->
			if is_fso_var_term ctype then
            Lm_symbol.eq (dest_fso_var ctype) indName
			else
				false

(* returns type of a given hypothesis v:t *)
let term_of_hyp = function
	Hypothesis (v,t) -> t
 | Context _ ->
		raise (Invalid_argument "term_of_hyp is undefined on a context")

(* returns name of a given hypothesis v:t *)
let name_of_hyp = function
	Hypothesis (v,t) -> v
 | Context _ ->
		raise (Invalid_argument "name_of_hyp is undefined on a context")

(* returns name and type of a given hypothesis v:t *)
let explode_hyp = function
	Hypothesis (v,t) -> v, t
 | Context _ ->
		raise (Invalid_argument "explode_hyp is undefined on a context")

(* extracts definiton of a type with index i, meaning the name,
   its type and its constructors,
	returns:
	  params - list of parameters of the inductive definition,
	  ti_name - name of the type,
	  ti_type - type of the type
	  constr_list - list of its constructors*)

let extract_type_def def i =
	let {sequent_args=arg;
	     sequent_hyps=params;
		  sequent_concl=goal} = TermMan.explode_sequent def in
	let {sequent_args=arg;
	     sequent_hyps=types;
		  sequent_concl=goal} = TermMan.explode_sequent goal in
	let {sequent_args=arg;
	     sequent_hyps=constrs} = TermMan.explode_sequent goal in
	print_hyps params;
	print_hyps types;
	print_hyps constrs;
	let ti = SeqHyp.get types i in
	match ti with
		Hypothesis (ti_name,ti_type) ->
			let constr_list = SeqHyp.to_list constrs in
			let constr_list = List.filter (fun x -> type_of_constr ti_name (term_of_hyp x)) constr_list in
			begin
				List.iter print_hyp constr_list;
				(params, ti_name, ti_type, constr_list)
			end
	 | Context _ ->
			raise (Invalid_argument "gen: contexts are not supported in inductive definitions")

(* takes the provided inductive definition (def) disassembles it, then
   assembles it back, changing labels of each sequent and changing the conclusion*)
let morph_type_def def params_label types_label constrs_label concl =
	let {sequent_args=arg;
	     sequent_hyps=params;
		  sequent_concl=goal} = TermMan.explode_sequent def in
	let {sequent_args=arg;
	     sequent_hyps=types;
		  sequent_concl=goal} = TermMan.explode_sequent goal in
	let {sequent_args=arg;
	     sequent_hyps=constrs} = TermMan.explode_sequent goal in
	let constrs_seq = TermMan.mk_sequent_term
			{sequent_args=constrs_label; sequent_hyps=constrs; sequent_concl=goal} in
	let types_seq = TermMan.mk_sequent_term
			{sequent_args=types_label; sequent_hyps=types; sequent_concl=constrs_seq} in
	let params_seq = TermMan.mk_sequent_term
			{sequent_args=params_label; sequent_hyps=params; sequent_concl=types_seq} in
	params_seq

(* extracts conclusion from any inductive sequent (we need it to extract the conclusion
	from an inductive definition (def))*)
let extract_ind_concl ind_seq =
	let {sequent_concl=goal} = TermMan.explode_sequent ind_seq in
	let {sequent_concl=goal} = TermMan.explode_sequent goal in
	let {sequent_concl=concl} = TermMan.explode_sequent goal in
	concl

let apply_rewrite conv t =
	let es={sequent_args= <<sequent_arg>>; sequent_hyps=SeqHyp.empty; sequent_concl=t} in
	let s=mk_sequent_term es in
	let b=Mp_resource.theory_bookmark "cic_ind_cases" in
	let r=Mp_resource.find b in
	let s'=Tactic_type.Conversionals.apply_rewrite r (higherC conv) s in
	(TermMan.explode_sequent s').sequent_concl

(* extracts conclusion "c in C'" from ind. definition *)
let get_c_in_C' def c_type c =
	let concl = mk_member_term c c_type in
	let subst = morph_type_def def <<IndParamsSubst>> <<IndTypesSubst>>
			<<IndConstrsSubst>> concl in
	let s'=apply_rewrite substC subst in
	let result = extract_ind_concl s' in
	result

(* *)
(*declare AppMember*)
declare sequent [AppMember] { Term : Term >- Term } : Term

prim_rw app_member_rw :
  sequent [AppMember] { 'q; <Hp> >- 'c in (p:'P -> 'C['p]) } <-->
  sequent [AppMember] { <Hp> >- ('c 'q) in 'C['q] }

let apply_context t params =
   let app_seq = TermMan.mk_sequent_term
			{ sequent_args= <<AppMember>>;
			 sequent_hyps=params;
			 sequent_concl=t} in
	let length = SeqHyp.length params in
	let s = apply_rewrite (repeatForC length app_member_rw) app_seq in
	let {sequent_concl=concl} = TermMan.explode_sequent s in
	concl

let gen_c_type subst args ts indName c p =
	let all_args = SeqHyp.append_list args ts (SeqHyp.empty) in
	let indName_args = TermMan.mk_sequent_term
			{ sequent_args = <<applH>>;
			 sequent_hyps = all_args;
			 sequent_concl = indName} in
	let indName_args' = apply_rewrite (repeatC (higherC applHC)) indName_args in
	let member = mk_member_term c indName_args' in
	printf "%s@." (SimplePrint.string_of_term member)

(*****
brackets
****)
let gen_brackets def subst args indName indNameType p =
	let {sequent_hyps=params} = TermMan.explode_sequent def in
   let indNameType' = TermMan.mk_sequent_term
			{ sequent_args = <<prodH>>;
			 sequent_hyps = params;
			 sequent_concl = indNameType} in
	let indNameType'' = apply_rewrite reduceC indNameType' in
	let member = mk_member_term indName indNameType'' in
	let member' = apply_context member args in
	let t, t_type = dest_member member' in
	let brackets = mk_brackets2_term t t_type in
	let b = apply_rewrite reduceC brackets in
	let t = mk_member_term p b in
	let t' = TermSubst.apply_subst subst t in
	printf "%s@." (SimplePrint.string_of_term t')

(***********************************************************
 * generates type of f_i, which is {(c_pi q_1 ... q_r)}^P,
 *	r is number of elements in parameters Hp,
 *	constr is the i-th constructor of indName
 ***********************************************************)

let gen_f_type def subst args fs p i constr =
	let v, t = explode_hyp constr in
	let xxx = apply_context (get_c_in_C' def t (mk_var_term v)) args in
	let t', t_type = dest_member xxx in
	let t_type' = apply_rewrite (repeatC (higherC (firstC [unfold_funC; fold_applH]))) t_type in
	let br = mk_branchType_sequent args p t' t_type' in
	let br' = apply_rewrite reduce_branchType br in
	let br'' = apply_rewrite (repeatC (higherC applHC)) br' in
	let member = mk_member_term fs.(i) br'' in
	let member' = TermSubst.apply_subst subst member in
	printf "%s@." (SimplePrint.string_of_term member')

let gen_case fs ts c p =
	let fs' = TermMan.mk_sequent_term
			{ sequent_args = <<cases>>;
			 sequent_hyps = fs;
			 sequent_concl = <<it>>} in
	let case_term = mk_case_term c p fs' in
	let p_type = TermMan.mk_sequent_term
			{ sequent_args = <<applH>>;
			 sequent_hyps = ts;
			 sequent_concl = p} in
	let p_type' = apply_rewrite (repeatC (higherC applHC)) p_type in
	let p_type'' = mk_apply_term p_type' c in
	let member = mk_member_term case_term p_type'' in
	printf "%s@." (SimplePrint.string_of_term member)

(* ----  *)

let rec iteri_aux f i = function
	[] -> ()
 | hd::tl ->
		f i hd;
		iteri_aux f (succ i) tl

let iteri f = iteri_aux f 0

let rec init_aux n f i =
	if i<n then
		(f i)::(init_aux n f (succ i))
	else
		[]

let init n f = init_aux n f 0

let gen_hyp t = Hypothesis(Lm_symbol.new_symbol_string "", t)

let gen_t j = mk_var_term (Lm_symbol.make "t" (succ j))

let rec vars_of_hyps tail = function
	(Hypothesis (v,_))::tl -> v::(vars_of_hyps tail tl)
 | (Context _)::tl -> vars_of_hyps tail tl
 | [] -> tail

let var2comb theory v =
	let name = Lm_symbol.to_string v in
	let opname = Opname.make_opname [name; theory] in
	mk_term (mk_op opname []) []

let comb_subst theory def =
	let {sequent_concl=goal} = TermMan.explode_sequent def in
	let {sequent_hyps=types;
		  sequent_concl=goal} = TermMan.explode_sequent goal in
	let {sequent_hyps=constrs} = TermMan.explode_sequent goal in
	let tvars = vars_of_hyps [] (SeqHyp.to_list types) in
	let allvars = vars_of_hyps tvars (SeqHyp.to_list constrs) in
	List.map (fun v -> (v, var2comb theory v)) allvars

let mk_simple_sequent concl =
	let context = Context (Lm_symbol.add "H", [], []) in
   TermMan.mk_sequent_term
	 { sequent_args = <<sequent_arg>>;
		sequent_hyps = SeqHyp.singleton context;
		sequent_concl = concl}

(* iota - reduction *)

let gen_iota theory def subst args fs_hyps ts_hyps p i constr =
	let v, t = explode_hyp constr in
	let cpi = mk_var_term v in
	let c = TermMan.mk_sequent_term
			{ sequent_args = <<applH>>;
			 sequent_hyps = args;
			 sequent_concl = cpi} in
	let c' = TermMan.mk_sequent_term
			{ sequent_args = <<applH>>;
			 sequent_hyps = ts_hyps;
			 sequent_concl = c} in
	let c'' = apply_rewrite (repeatC (higherC applHC)) c' in
	let fs' = TermMan.mk_sequent_term
			{ sequent_args = <<cases>>;
			 sequent_hyps = fs_hyps;
			 sequent_concl = <<it>>} in
	let lhs = mk_case_term c'' p fs' in
	let lhs' = TermSubst.apply_subst subst lhs in
	let fi_hyp = SeqHyp.get fs_hyps i in
	let _,fi = explode_hyp fi_hyp in
	let rhs = TermMan.mk_sequent_term
			{ sequent_args = <<applH>>;
			 sequent_hyps = ts_hyps;
			 sequent_concl = fi} in
	let rhs' = apply_rewrite (repeatC (higherC applHC)) rhs in
	printf "redex:\n%s@." (SimplePrint.string_of_term lhs');
	printf "contractum:\n%s@." (SimplePrint.string_of_term rhs')

(********************************************************
 *  generates case-analysis's fourth assumption for the
 *  given inductive type with index i
 ********************************************************)

let gen theory def s i =
	let subst = comb_subst theory def in
	let params, ti_name, ti_type, constr_list = extract_type_def def i in
	let ti_name_comb = var2comb theory ti_name in
	let ti_type' = TermSubst.apply_subst subst ti_type in
	let n = List.length constr_list in
	(*let {sequent_hyps=args'} = TermMan.explode_sequent args in*)
	let params_vars = vars_of_hyps [] (SeqHyp.to_list params) in
	let params' = List.map (fun v -> gen_hyp (mk_var_term v)) params_vars in
	let args = SeqHyp.of_list params' in
	let ts_hyps = SeqHyp.init s (fun j -> gen_hyp (gen_t j)) in
	let ts = SeqHyp.to_list ts_hyps in
	let p = mk_var_term (Lm_symbol.add "P") in
	let c = mk_var_term (Lm_symbol.add "c") in
	let fs = Array.init n (fun j -> mk_var_term (Lm_symbol.make "f" (succ j))) in
	let fs_hyps = SeqHyp.init n (fun j -> gen_hyp fs.(j)) in
	gen_c_type subst args ts ti_name_comb c p;
	gen_brackets def subst args ti_name_comb ti_type' p;
	iteri (gen_f_type def subst args fs p) constr_list;
	gen_case fs_hyps ts_hyps c p;
	eprintf "\ngeneration of iota reductions@.";
	iteri (gen_iota theory def subst args fs_hyps ts_hyps p) constr_list;
	failT
(*
module Shell = Shell.Shell(Shell_shell.ShellP4)

let gen2 = funT (fun p ->
   let goal = TermMan.mk_sequent_term
			{ sequent_args = <<sequent_arg>>;
			 sequent_hyps = SeqHyp.empty;
			 sequent_goals = <<it>>} in
	Shell.Edit.create_thm "cic_list" "foo3";
	Shell.Edit.set_goal "cic_list" "foo3" goal;
	idT
)
*)

declare caseAux{'S1;'P;'S2}

(*declare IndParamsIota*)
declare sequent [IndParamsIota] { Term : Term >- Term } : Term


prim_rw iotaStart 'Hc :
	case{ sequent [IndParams] { <Hp> >-
				sequent [IndTypes] { <Hi> >-
					sequent [IndConstrs] { <Hc>; c: 'C; <Jc> >-
						sequent [applH] { <Q> >- 'c} } } };
			'P; sequent [cases] { <F> >- it} } <-->
	caseAux{
		sequent [IndParams] { <Hp> >-
			sequent [IndParamsIota] { >-
				sequent [IndTypes] { <Hi> >-
					sequent [IndConstrs] { <Hc>; c: 'C; <Jc> >-
						sequent [applH] { <Q> >- 'c} } } } };
			'P; sequent [cases] { <F> >- it} }

(*
prim_rw iotaStep 'Hc :
	caseAux{
		sequent [IndParams] { <Hp>; p:'P >-
			sequent [IndParamsIota] { <Jp['p]> >-
				sequent [IndTypes] { <Hi['p]> >-
					sequent [IndConstrs] { <Hc['p]>; c: 'C['p]; <Jc['p]> >-
						sequent [applH] { 'q; <Q> >- 'c} } } } };
			'P; sequent [cases] { <F> >- it} } <-->
	caseAux{
		sequent [IndParams] { <Hp> >-
			sequent [IndParamsIota] { p:'P; <Jp['p]> >-
				sequent [IndTypes] { <Hi['p]> >-
					sequent [IndConstrs] { <Hc['p]>; c: 'C['p]; <Jc['p]> >-
						sequent [applH] { <Q> >- 'c} } } } };
			'P; sequent [cases] { <F> >- it} }

prim_rw iotaFinal 'Hc :
	caseAux{
		sequent [IndParams] { >-
			sequent [IndParamsIota] { <Jp> >-
				sequent [IndTypes] { <Hi> >-
					sequent [IndConstrs] { <Hc>; c: 'C; <Jc> >-
						sequent [applH] { <Q> >- 'c} } } } };
			'P; sequent [cases] { <F> >- it} } <-->
	sequent [applH] { <Q> >- 'f }
*)
(*
declare struct_smaller{'T; y.'t['y]}

prim struct_smaller_const {| intro [] }| :
	sequent { <H> >- struct_smaller{'T; y.'t} }

prim struct_smaller_app {| intro [] }| :
	sequent { <H> >- struct_smaller{'T; y.'t['y]} } -->
	sequent { <H> >- struct_smaller{'T; y.('t['y] 'u['y])} }

(* may be 'T has to depend on 'y then we probably need struct_smaller{'y; 't} *)
prim struct_smaller_lambda {| intro [] }| :
	sequent { <H>; x: 'S >- struct_smaller{'T; y.'t['x;'y]} } -->
	sequent { <H> >- struct_smaller{'T; y.lambda{'S; x.'t['x;'y]}} }

prim struct_smaller_cases_base {| intro [] }| :
	sequent { <H> >- struct_smaller{'T; y.(sequent [cases] { >- it})} } -->

prim struct_smaller_cases_step {| intro [] }| :
	sequent { <H> >- struct_smaller{'T; y.'f['y]} } -->
	sequent { <H> >- struct_smaller{'T; y.(sequent [cases] { <F['y]> >- it})} } -->
	sequent { <H> >- struct_smaller{'T; y.(sequent [cases] { 'f['y]; <F['y]> >- it})} } -->

prim struct_smaller_case {| intro [] }| :
	sequent { <H> >- struct_smaller{'T; y.'c['y]} } -->
	sequent { <H> >- struct_smaller{'T; y.(sequent [cases] { <F['y]> >- it}} } -->
	sequent { <H> >- struct_smaller{'T; y.case{'S;'c['y];'P; sequent [cases] { <F['y]> >- it} }} }

declare D{<V>; f,x.M['f;'x]}
(*declare DummyType*)
declare sequent [DummyType] { Term : Term >- Term } : Term

prim
	D{<V>; f,x.M['x]}

prim
	D{<V>; f,x.'P['f;'x]} -->
	z: DummyType >- D{<V>; f,x.'Q['f;'x;'z]} -->
	D{<V>; f,x.lambda{'P['f;'x]; z.Q['f;'x;'z]}

prim
	ForEach{sequent{<F1>; g: A['f;'x] := N['f;'x;'g]; <F2> >- it}; D{<V>; f,x.'N['f;'x;'g]} } -->
	ForEach{sequent{<F1>; g: A['f;'x] := N['f;'x;'g]; <F2> >- it}; D{<V>; f,x.'A['f;'x]} } -->
	D{<V>; f,x.(sequent [fixpoint] {<F['f;'x]> >- 'g['f;'x]})}

(*declare D_ForAll*)
declare sequent [D_ForAll] { Term : Term >- Term } : Term

prim D_sequent_base :
	D{<V>; f,x.'C['f;'x]} -->
	D{<V>; f,x.(sequent [D_ForAll] { >- 'C['f;'x]})}

prim D_sequent_step :
	D{<V>; f,x.'T['f;'x]} -->
	v: DummyType >- D{<V>; f,x.(sequent [D_ForAll] {<H['f;'x;'v]> >- 'C['f;'x]})} -->
	D{<V>; f,x.(sequent [D_ForAll] {v: 'T['f;'x]; <H['f;'x;'v]> >- 'C['f;'x]})}

prim
	D{<V>; f,x.(sequent[D_ForAll]{ <Hp['f;'x]>; <Hi['f;'x]> <Hc['f;'x]> >- it}) } -->
	D{<V>; f,x.
		sequent [IndParams] { <Hp['f;'x]> >-
			sequent [IndTypes] { <Hi['f;'x]> >-
				sequent [IndConstrs] { <Hc['f;'x]> >- it } } }

prim DD_base :
	DD{<V>; <Hp>; <Hi>; <Hc>; <>; f,x.<>}

prim DD_step :
	D{(<V>; RP{<Hp>; (<Hi>; I: 'A; <Ji>); (<Hc>; c: prodH{<T> >- applH{<Hargs> >- 'I} } ; <Jc>);<T>}; f,x.'E['f;'x]} -->
	DD{<V>; <Hp>; (<Hi>; I: 'A; <Ji>); <Hc>; (c: prodH{<T> >- applH{<Hargs> >- 'I} } ; <Jc>); f,x.(prodH{<T['I <- Ind()]> >- 'E['f;'x]}; <F['f;'x]>)}

prim D_case_rec_position :
	D{(<V1>; z: 'T; <V2>); f,x.'Pred['f;'x]} -->
	D{(<V1>; z: 'T; <V2>); f,x.applH{Ind{...}; <R>}} -->
	D{(<V1>; z: 'T; <V2>); f,x.<P['f;'x]>} -->
	DD{(<V1>; z: 'T; <V2>); <Hp>; <Hi>; <>; <Hc>; f,x.<F['f;'x]>} -->
	D{(<V1>; z: 'T; <V2>); f,x.case{applH{Ind{...}; <R>}; applH{'z; <P['f;'x]>};'Pred['f;'x]; sequent [cases] { <F['f;'x]> >- it} }}

prim D_case_rec_on :
	D{<V>; f,x.'Pred['f;'x]} -->
	D{<V>; f,x.applH{Ind{...}; <R>}} -->
	D{<V>; f,x.<P['f;'x]>} -->
	DD{<V>; <Hp>; <Hi>; <>; <Hc>; f,x.<F['f;'x]>} -->
	D{<V>; f,x.case{applH{Ind{...}; <R>}; applH{'x; <P>};'Pred['f;'x]; sequent [cases] { <F['f;'x]> >- it} }}

prim D_case_general :
	D{<V>; f,x.'Pred['f;'x]} -->
	D{<V>; f,x.'T['f;'x]} -->
	D{<V>; f,x.'c['f;'x]} -->
	D{<V>; f,x.(sequent [D_ForAll] { <F['f;'x]> >- it}) } -->
	D{<V>; f,x.case{'T['f;'x];'c['f;'x];'Pred['f;'x]; sequent [cases] { <F['f;'x]> >- it} }}

prim D_applH_on_fixpoint :
	D{(<V1>; z: 'T; <V2>); f,x.sequent [D_ForAll] { <Hp['f;'x]>; applH{'z; <Q>} >- it} } -->
	D{(<V1>; z: 'T; <V2>); f,x.applH{'f; (<Hp['f;'x]>; (applH{'z; <Q>}))} }

prim D_applH :
	D{<V>; f,x.'t['f;'x] } -->
	D{<V>; f,x.sequent [D_ForAll] { <Hp['f;'x]> >- it} } -->
	D{<V>; f,x.applH{'t['f;'x]; <Hp['f;'x]>} }

prim D_app :
	D{<V>; f,x.'t['f;'x] } -->
	D{<V>; f,x.'s['f;'x] } -->
	D{<V>; f,x.('t['f;'x] 's['f;'x]) }
*)