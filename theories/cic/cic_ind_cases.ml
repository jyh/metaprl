extends Cic_ind_type
open Basic_tactics
open Dtactic
open Cic_lambda
open Cic_ind_type

declare case{'t;'P;'F}
declare cases
declare brackets{'I;'B}
declare brackets{'I;'A;'B}

declare branchCases
declare branchConstrs

declare emptyDef{'I}
declare singletonDef{'I}

(* definition of a relation [I:A|B] *)

(* derivation rule [(I x) : A'|B']
                   ---------------  denotation (--->)
					 [I : (x:A)A'|(x:A)B']   *)
prim bracketsProd {| intro [] |} :
	sequent { <H>; x:'C >- brackets{'I 'x; 'A['x]; 'B['x]} } -->
	sequent { <H> >- brackets{'I;(x:'C -> 'A['x]); (x:'C -> 'B['x])} } = it

(* [I:Set | I -> Prop] *)
prim bracketsSetProp {| intro [] |} :
	sequent { <H> >- brackets{'I;Set;'I -> Prop} } = it

(* [I:Set | I -> Prop] *)
prim bracketsSetSet {| intro [] |} :
	sequent { <H> >- brackets{'I;Set;'I -> Set} } = it

(*! I is a small inductive definition s belongs to {Type(i)} --->
   [I : Set | I- > s]*)
prim bracketsSetType {| intro [] |} :
	sequent { <H> >- brackets{'I;Set;'I -> "type"[i:l]} } = it

prim bracketsTypeProp {| intro [] |} :
	sequent { <H> >- brackets{'I;"type"[j:l];'I -> Prop} } = it

prim bracketsTypeSet {| intro [] |} :
	sequent { <H> >- brackets{'I;"type"[j:l];'I -> Set} } = it

prim bracketsTypeType {| intro [] |} :
	sequent { <H> >- brackets{'I;"type"[j:l];'I -> "type"[i:l]} } = it

prim bracketsProp {| intro [] |} :
	sequent { <H> >- brackets{'I;Prop;'I -> Prop} } = it


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


declare branchType
declare branchType{'P;'c;'C}

prim_rw branchTypeApp {| reduce |} :
	sequent [branchType] { <Hp> >-
		branchType{ 'P<||>; 'c<||>; sequent[applH] { <Hp>;<T<| |> > >- 'I} } } <-->
	sequent [applH] { <T>; 'c >- 'P }

prim_rw branchTypeFun {| reduce |} :
	sequent [branchType] { <Hp> >-
		branchType{ 'P<||>; 'c<||>; (x:'T<||> -> 'C['x]) } } <-->
	(x: 'T -> sequent [branchType] { <Hp> >- branchType{'P; 'c 'x; 'C['x]}} )

let branchType_term = << branchType{'P; 'c; 'C} >>
let branchType_opname = opname_of_term branchType_term
let is_branchType_term = is_dep0_dep0_dep0_term branchType_opname
let dest_branchType = dest_dep0_dep0_dep0_term branchType_opname
let mk_branchType_term = mk_dep0_dep0_dep0_term branchType_opname

let mk_branchType_sequent args p c c_type =
	let br = mk_branchType_term p c c_type in
	let goal = SeqGoal.singleton br in
	let label = <<sequent_arg{branchType}>> in
	TermMan.mk_sequent_term {sequent_args=label; sequent_hyps=args; sequent_goals=goal}

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
		  sequent_goals=goals} = TermMan.explode_sequent def in
	let goal = SeqGoal.get goals 0 in
	let {sequent_args=arg;
	     sequent_hyps=types;
		  sequent_goals=goals} = TermMan.explode_sequent goal in
	let {sequent_args=arg;
	     sequent_hyps=constrs} = TermMan.explode_sequent (SeqGoal.get goals 0) in
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
		  sequent_goals=goals} = TermMan.explode_sequent def in
	let goal = SeqGoal.get goals 0 in
	let {sequent_args=arg;
	     sequent_hyps=types;
		  sequent_goals=goals} = TermMan.explode_sequent goal in
	let {sequent_args=arg;
	     sequent_hyps=constrs} = TermMan.explode_sequent (SeqGoal.get goals 0) in
	let goal = SeqGoal.singleton concl in
	let params_label' = mk_sequent_arg_term params_label in
	let types_label' = mk_sequent_arg_term types_label in
	let constrs_label' = mk_sequent_arg_term constrs_label in
	let constrs_seq = TermMan.mk_sequent_term
			{sequent_args=constrs_label'; sequent_hyps=constrs; sequent_goals=goal} in
	let types_seq = TermMan.mk_sequent_term
			{sequent_args=types_label'; sequent_hyps=types; sequent_goals=(SeqGoal.singleton constrs_seq)} in
	let params_seq = TermMan.mk_sequent_term
			{sequent_args=params_label'; sequent_hyps=params; sequent_goals=(SeqGoal.singleton types_seq)} in
	params_seq

(* extracts conclusion from any inductive sequent (we need it to extract the conclusion
	from an inductive definition (def))*)
let extract_ind_concl ind_seq =
	let {sequent_goals=goals} = TermMan.explode_sequent ind_seq in
	let goal = SeqGoal.get goals 0 in
	let {sequent_goals=goals} = TermMan.explode_sequent goal in
	let {sequent_goals=concl} = TermMan.explode_sequent (SeqGoal.get goals 0) in
	SeqGoal.get concl 0

let apply_rewrite conv t =
	let es={sequent_args= <<sequent_arg>>; sequent_hyps=(SeqHyp.of_list []); sequent_goals=(SeqGoal.of_list [t])} in
	let s=mk_sequent_term es in
	let b=Mp_resource.theory_bookmark "cic_ind_cases" in
	let r=Mp_resource.find b in
	let s'=Tactic_type.Conversionals.apply_rewrite r (higherC conv) s in
	SeqGoal.get (TermMan.explode_sequent s').sequent_goals 0

(* extracts conclusion "c in C'" from ind. definition *)
let get_c_in_C' def c_type c =
	let concl = mk_member_term c c_type in
	let subst = morph_type_def def <<IndParamsSubst>> <<IndTypesSubst>>
			<<IndConstrsSubst>> concl in
	let s'=apply_rewrite substC subst in
	let result = extract_ind_concl s' in
	result

(* *)
declare AppMember

prim_rw app_member_rw :
  sequent [AppMember] { 'q; <Hp> >- 'c in (p:'P -> 'C['p]) } <-->
  sequent [AppMember] { <Hp> >- ('c 'q) in 'C['q] }

let apply_context t params =
   let app_seq = TermMan.mk_sequent_term
			{ sequent_args= <<sequent_arg{AppMember}>>;
			 sequent_hyps=params;
			 sequent_goals=SeqGoal.singleton t} in
	let length = SeqHyp.length params in
	let s = apply_rewrite (repeatForC length app_member_rw) app_seq in
	let {sequent_goals=g} = TermMan.explode_sequent s in
	SeqGoal.get g 0



(***********************************************************
 * generates type of f_i, which is {(c_pi q_1 ... q_r)}^P,
 *	r is number of elements in parameters Hp,
 *	constr is the i-th constructor of indName
 ***********************************************************)

let gen_f_type def args indName i constr =
	let v, t = explode_hyp constr in
	let xxx = apply_context (get_c_in_C' def t (mk_var_term v)) args in
	let t', t_type = dest_member xxx in
	let fi = new_symbol_string_term (sprintf "f%i" i) in
	let p = new_symbol_string_term "P" in
	let br = mk_branchType_sequent args p t' t_type in
	let member = mk_member_term fi br in
	printf "%s@." (SimplePrint.string_of_term member)
	(*printf "'f%i in branchType{'P; %s; %s}@." i (SimplePrint.string_of_term t')
	   (SimplePrint.string_of_term t_type)*)


(* ----  *)

let rec iteri_aux f i = function
	[] -> ()
 | hd::tl ->
		f i hd;
		iteri_aux f (succ i) tl

let iteri f = iteri_aux f 0

(********************************************************
 *  generates case-analysis's fourth assumption for the
 *  given inductive type with index i
 ********************************************************)

let gen def args i =
	let params, ti_name, ti_type, constr_list = extract_type_def def i in
	let {sequent_hyps=args'} = TermMan.explode_sequent args in
	iteri (gen_f_type def args' ti_name) constr_list;
	failT
(*
module Shell = Shell.Shell(Shell_p4.ShellP4)

let _ =
   let goal = TermMan.mk_sequent_term
			{ sequent_args= <<sequent_arg>>;
			 sequent_hyps=SeqHyp.empty;
			 sequent_goals=SeqGoal.singleton <<it>>} in
	Shell.create_thm "cic_list" "foo2";
	Shell.set_goal "cic_list" "foo2" goal
*)
(* iota - reduction *)

declare caseAux{'S1;'P;'S2}

declare IndParamsIota


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
