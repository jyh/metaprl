(*
 * Declare base caml syntax, plus read macro.
 *)

open Filter_ocaml

(*
 * Arrange an array of subterms as a list.
 *)
let nil_term = mk_simple_term nil_op []
let mk_cons_term car cdr = mk_simple_term cons_op [car; cdr]
let rec mk_list_term = function
   h::t ->
      mk_cons_term h (mk_list_term t)
 | [] ->
      nil_term

(*
 * A "with" term is a term that evaluates only if the
 * with clause is true (else the next clause in the
 * match should be selected.
 *)
let with_op = mk_ocaml_op "with"

let mk_with_term w e =
   mk_simple_term with_op [w; e]

(*
 * A bound term is a recursive binding.
 *)
let bind_op = mk_ocaml_op "bind"

let mk_bound_term vars expr =
   let rec bind = function
      v::t ->
         mk_dep1_term bind_op v (bind t)
    | [] ->
         expr
   in
      bind vars

let fun_term = mk_simple_term (mk_ocaml_op "fun") []

(*
 * Get the opname and subterms of a term.
 *)
let dest_op_subterms t =
   let { term_operator = op } = dest_term t in
   let { op_name = opname } = dest_op op in
      opname, subterms_of_term t

(*
 * For looking up destructors in a hashtable.
 *)
let dest_tbl code table t =
   try (Hashtbl.find table (opname_of_term t)) t with
      Not_found ->
         raise (FormatError ("Caml_syntax.dest_" ^ code ^ " : unrecognized opname", t))
    | TermMatch (_, t, s) ->
         raise (FormatError ("Caml_syntax.dest_" ^ code ^ " : " ^ s, t))


let add_tbl table name f =
   let opname = mk_ocaml_op name in
      Hashtbl.add table opname f;
      opname

(*
 * Hashtables for destructing terms.
 *)
let expr_table = Hashtbl.create 17
let patt_table = Hashtbl.create 17
let type_table = Hashtbl.create 17
let sig_table  = Hashtbl.create 17
let str_table  = Hashtbl.create 17
let mt_able    = Hashtbl.create 17
let me_table   = Hashtbl.create 17
let wc_table   = Hashtbl.create 5
let ctf_table  = Hashtbl.create 17
let cf_table   = Hashtbl.create 17

(*
 * Simple conversion strips off the location,
 * which is the first two parameters.
 *)
let dest_simple t =
   let { term_operator = op; term_terms = bterms } = dest_term t in
   let { op_name = opname; op_params = params } = dest_op op in
   let params =
      match params with
         Number _ :: Number _ :: params' ->
            params'
       | _ ->
            params
   in
   let op' = mk_op opname params in
      mk_term op' bterms

(*
 * Array construction is expressed as a list.
 *)
let dest_array_expr t =
   let op, terms = dest_op_subterms t in
      mk_simple_term op [mk_list_term terms]

and dest_for_expr t =
   let op = opname_of_term t in
   let e1, e2, v, e3 = dest_dep0_dep0_dep1_any_term t in
   let el = subterms_of_term e3 in
      mk_dep0_dep0_dep1_term op e1 e2 v (mk_list_term el)

(*
 * For a function, we have to do pattern matching.
 * The patterns are handled by having a spread,
 * then beind the with and expression clauses over
 * all the variables in the pattern.  The slots
 * in the pattern are replaced by variable numbers.
 *)
and dest_pwel = function
   pwe :: t ->
      begin
         match subterms_of_term pwe with
            [p; w; e] ->
               let vars, spread = spread_of_patt p in
                  mk_simple_term fun_op [spread; mk_bound_term vars (mk_with_term w e); dest_pwel t]
          | _ ->
               raise (Failure "Function is malformed")
      end
 | [] ->
      fun_term

and dest_fun_expr t =
   let pwel = subterms_of_term t in
      dest_pwel pwel

(*
 * A "match" is a function with its argument.
 *)
and dest_match_expr t =
   let op = opname_of_term t in
      match subterms_of_term t with
         e :: pwel ->
            mk_simple_term op [dest_expr e; dest_pwel pwel]
       | [] ->
            raise (Failure "match is malformed")

(*
 * The "let" is a primitive construct.
 * Most of the reduction rules are defined on "let"
 * blocks.  For the simple let, we just make a binding,
 * collecting the patterns.
 *)
and dest_pe expr = function
   pe :: t ->
      begin
         match subterms_of_term pe with
            [p; e] ->
               let vars, spread = spread_patt p in
                  mk_simple_term let_op [dest_expr e; spread; mk_bound_term vars (dest_pe expr t)]
          | _ ->
               raise (Failure "Let is malformed")
      end
 | [] ->
      dest_expr expr

and dest_let_expr t =
   let sub = subterms_of_term t in
   let pe, e = List_util.split_last sub in
      dest_pe e pe

(*
 * The recursive "let" is somewhat different, because
 * the variables are bound over the entire term.  We collect
 * all the variables out of all the patterns, making sure there
 * are no duplicates.
 *)
and dest_letrec_expr t =
   let sub = subterms_of_term t in
   let pe, e = List_util.split_last sub in
      <:expr< let $rec:true$ $list: List.map dest_pe pe$ in $dest_expr e$ >>

and dest_lid_expr t =
   let loc = dest_loc t in
      <:expr< $lid:dest_var t$ >>

and dest_new_expr t =
   let loc = dest_loc t in
      <:expr< new $dest_expr (one_subterm t)$ >>

and dest_stream_expr t =
   let loc = dest_loc t in
   let sel = subterms_of_term t in
      <:expr< {< $list: List.map dest_se sel$ >} >>

and dest_record_expr t =
   let loc = dest_loc t in
   let eel = subterms_of_term t in
      <:expr< { $list: List.map dest_ee eel$ } >>

and dest_seq_expr t =
   let loc = dest_loc t in
   let el = subterms_of_term t in
   let el', e = List_util.split_last el in
      <:expr< do $list:List.map dest_expr el'$ return $dest_expr e$ >>

and dest_select_expr t =
   let loc = dest_loc t in
   let e, s = two_subterms t in
      <:expr< $dest_expr e$ # $dest_string s$ >>

and dest_string_subscript_expr t =
   let loc = dest_loc t in
   let e1, e2 = two_subterms t in
      <:expr< $dest_expr e1$ .[ $dest_expr e2$ ] >>

and dest_string_expr t =
   let loc, s = dest_loc_string t in
      <:expr< $str:s$ >>

and dest_try_expr t =
   let loc = dest_loc t in
      match subterms_of_term t with
         e :: pwel ->
   	    <:expr< try $dest_expr e$ with [ $list: List.map dest_pwe pwel$ ] >>
       | [] ->
            raise (FormatError ("try needs an argument", t))

and dest_tuple_expr t =
   let loc = dest_loc t in
   let el = subterms_of_term t in
      <:expr< ( $list: List.map dest_expr el$ ) >>

and dest_cast_expr t =
   let loc = dest_loc t in
   let e, t = two_subterms t in
      <:expr< ( $dest_expr e$ : $dest_type t$ ) >>

and dest_uid_expr t =
   let loc = dest_loc t in
      <:expr< $uid:dest_var t$ >>

and dest_while_expr t =
   let loc = dest_loc t in
   let e, el = two_subterms t in
      <:expr< while $dest_expr e$ do $list: List.map dest_expr (subterms_of_term el)$ done >>

(*
 * Patterns.
 * Patterns are handled by constructing a match clause,
 * and then binding over all the variables in the pattern.
 * The slots in the match clause are replaced by the
 * variable number.
 *)
and dest_proj_patt t =
   let loc = dest_loc t in
   let p1, p2 = two_subterms t in
      <:patt< $dest_patt p1$ . $dest_patt p2$ >>

and dest_as_patt t =
   let loc = dest_loc t in
   let p1, p2 = two_subterms t in
      <:patt< ( $dest_patt p1$ as $dest_patt p2$ ) >>

and dest_wildcard_patt t =
   let loc = dest_loc t in
      <:patt< _ >>

and dest_apply_patt t =
   let loc = dest_loc t in
   let p1, p2 = two_subterms t in
      <:patt< $dest_patt p1$ $dest_patt p2$ >>

and dest_char_patt t =
   let loc, s = dest_loc_string t in
      if String.length s = 0 then
         raise (FormatError ("dest_char_patt: string needs at least one char", t));
      <:patt< $chr:s.[0]$ >>

and dest_int_patt t =
   let loc, i = dest_loc_int t in
      <:patt< $int:i$ >>

and dest_lid_patt t =
   let loc = dest_loc t in
      <:patt< $lid:dest_var t$ >>

and dest_choice_patt t =
   let loc = dest_loc t in
   let p1, p2 = two_subterms t in
      <:patt< $dest_patt p1$ | $dest_patt p2$ >>

and dest_range_patt t =
   let loc = dest_loc t in
   let p1, p2 = two_subterms t in
      <:patt< $dest_patt p1$ .. $dest_patt p2$ >>

and dest_record_patt t =
   let loc = dest_loc t in
   let ppl = subterms_of_term t in
      <:patt< { $list: List.map dest_pp ppl$ } >>

and dest_string_patt t =
   let loc, s = dest_loc_string t in
      <:patt< $str:s$ >>

and dest_tuple_patt t =
   let loc = dest_loc t in
   let pl = subterms_of_term t in
      <:patt< ( $list: List.map dest_patt pl$ ) >>

and dest_cast_patt t =
   let loc = dest_loc t in
   let p, t = two_subterms t in
      <:patt< ( $dest_patt p$ : $dest_type t$ ) >>

and dest_uid_patt t =
   let loc = dest_loc t in
      <:patt< $uid:dest_var t$ >>

(*
 * Types.
 *)
and dest_proj_type t =
   let loc = dest_loc t in
   let t1, t2 = two_subterms t in
      <:ctyp< $dest_type t1$ . $dest_type t2$ >>

and dest_as_type t =
   let loc = dest_loc t in
   let t1, t2 = two_subterms t in
      <:ctyp< $dest_type t1$ as $dest_type t2$ >>

and dest_wildcard_type t =
   let loc = dest_loc t in
      <:ctyp< _ >>

and dest_apply_type t =
   let loc = dest_loc t in
   let t1, t2 = two_subterms t in
      <:ctyp< $dest_type t1$ $dest_type t2$ >>

and dest_fun_type t =
   let loc = dest_loc t in
   let t1, t2 = two_subterms t in
      <:ctyp< $dest_type t1$ -> $dest_type t2$ >>

and dest_class_id_type t =
   let loc = dest_loc t in
      <:ctyp< # $dest_type t$ >>

and dest_lid_type t =
   let loc = dest_loc t in
      <:ctyp< $lid:dest_var t$ >>

and dest_param_type t =
   let loc, s = dest_loc_string t in
      <:ctyp< '$s$ >>

and dest_equal_type t =
   let loc = dest_loc t in
   let t1, t2 = two_subterms t in
      <:ctyp< $dest_type t1$ == $dest_type t2$ >>

and dest_object_tt_type t =
   let loc = dest_loc t in
   let stl = subterms_of_term t in
      <:ctyp< < $list: List.map dest_st stl$ $dd:true$ > >>

and dest_object_ff_type t =
   let loc = dest_loc t in
   let stl = subterms_of_term t in
      <:ctyp< < $list: List.map dest_st stl$ $dd:false$ > >>

and dest_record_type t =
   let loc = dest_loc t in
   let sbtl = subterms_of_term t in
      <:ctyp< { $list: List.map dest_sbt sbtl$ } >>

and dest_list_type t =
   let loc = dest_loc t in
   let stll = subterms_of_term t in
      <:ctyp< [ $list: List.map dest_stl stll$ ] >>

and dest_prod_type t =
   let loc = dest_loc t in
   let tl = subterms_of_term t in
      <:ctyp< ( $list: List.map dest_type tl$ ) >>

and dest_uid_type t =
   let loc = dest_loc t in
      <:ctyp< $uid:dest_var t$ >>

(*
 * Signatures.
 *)
and dest_class_sig t =
   let loc = dest_loc t in
   let ctl = subterms_of_term t in
      <:sig_item< class $list: List.map dest_class_type ctl$ >>

and dest_subsig_sig t =
   let loc = dest_loc t in
   let sl = subterms_of_term t in
      <:sig_item< declare $list: List.map dest_sig sl$ end >>

and dest_exception_sig t =
   let loc, s = dest_loc_string t in
   let tl = subterms_of_term t in
      <:sig_item< exception $s$ of $list: List.map dest_type tl$ >>

and dest_external_sig t =
   let loc, s = dest_loc_string t in
      match subterms_of_term t with
         t :: sl ->
            <:sig_item< external $s$ : $dest_type t$ = $list: List.map dest_string sl$ >>
       | _ ->
           raise (FormatError ("external requires a name and a type", t))

and dest_module_sig t =
   let loc, s = dest_loc_string t in
   let mt = one_subterm t in
      <:sig_item< module $s$ : $dest_mt mt$ >>

and dest_module_type_sig t =
   let loc, s = dest_loc_string t in
   let mt = one_subterm t in
      <:sig_item< module type $s$ = $dest_mt mt$ >>

and dest_open_sig t =
   let loc = dest_loc t in
   let sl = subterms_of_term t in
      <:sig_item< open $List.map dest_string sl$ >>

and dest_type_sig t =
   let loc = dest_loc t in
   let ssltl = subterms_of_term t in
      <:sig_item< type $list: List.map dest_sslt ssltl$ >>

and dest_value_sig t =
   let loc, s = dest_loc_string t in
   let t = one_subterm t in
      <:sig_item< value $s$ : $dest_type t$ >>

(*
 * Structure items.
 *)
and dest_class_str t =
   let loc = dest_loc t in
   let cdl = subterms_of_term t in
      <:str_item< class $list: List.map dest_class cdl$ >>

and dest_substruct_str t =
   let loc = dest_loc t in
   let stl = subterms_of_term t in
      <:str_item< declare $list: List.map dest_str stl$ end >>

and dest_exception_str t =
   let loc, s = dest_loc_string t in
   let tl = subterms_of_term t in
      <:str_item< exception $s$ of $list: List.map dest_type tl$ >>

and dest_expr_str t =
   let loc = dest_loc t in
      <:str_item< $exp: dest_expr (one_subterm t)$ >>

and dest_external_str t =
   let loc, s = dest_loc_string t in
      match subterms_of_term t with
         t :: sl ->
            <:str_item< external $s$ : $dest_type t$ = $list: List.map dest_string sl$ >>
       | _ ->
            raise (FormatError ("external requires a name and type", t))

and dest_module_str t =
   let loc, s = dest_loc_string t in
   let me = one_subterm t in
      <:str_item< module $s$ = $dest_me me$ >>

and dest_module_type_str t =
   let loc, s = dest_loc_string t in
   let mt = one_subterm t in
      <:str_item< module type $s$ = $dest_mt mt$ >>

and dest_open_str t =
   let loc = dest_loc t in
   let sl = subterms_of_term t in
      <:str_item< open $List.map dest_string sl$ >>

and dest_type_str t =
   let loc = dest_loc t in
   let ssltl = subterms_of_term t in
      <:str_item< type $list: List.map dest_sslt ssltl$ >>

and dest_letrec_str t =
   let loc = dest_loc t in
   let pel = subterms_of_term t in
      <:str_item< value $rec:true$ $list: List.map dest_pe pel$ >>

and dest_let_str t =
   let loc = dest_loc t in
   let pel = subterms_of_term t in
      <:str_item< value $rec:false$ $list: List.map dest_pe pel$ >>

(*
 * Module types.
 *)
and dest_proj_mt t =
   let loc = dest_loc t in
   let mt1, mt2 = two_subterms t in
      <:module_type< $dest_mt mt1$ . $dest_mt mt2$ >>

and dest_apply_mt t =
   let loc = dest_loc t in
   let mt1, mt2 = two_subterms t in
      <:module_type< $dest_mt mt1$ $dest_mt mt2$ >>

and dest_functor_mt t =
   let loc = dest_loc t in
   let v, mt1, mt2 = dest_dep0_dep1_any_term t in
      <:module_type< functor ($v$ : $dest_mt mt1$) -> $dest_mt mt2$ >>

and dest_lid_mt t =
   let loc = dest_loc t in
      <:module_type< $lid:dest_var t$ >>

and dest_sig_mt t =
   let loc = dest_loc t in
   let sil = subterms_of_term t in
      <:module_type< sig $list: List.map dest_sig sil$ end >>

and dest_uid_mt t =
   let loc = dest_loc t in
      <:module_type< $uid:dest_var t$ >>

and dest_with_mt t =
   let loc = dest_loc t in
      match subterms_of_term t with
         mt :: wcl ->
            <:module_type< $dest_mt mt$ with $list: List.map dest_wc wcl$ >>
       | [] ->
           raise (FormatError ("module \"with\" clause must have type", t))

and dest_type_wc t =
   let loc = dest_loc t in
   let sl1, sl2, t = three_subterms t in
   let sl1' = List.map dest_string (subterms_of_term sl1) in
   let sl2' = List.map dest_string (subterms_of_term sl2) in
      WcTyp (loc, sl1', sl2', dest_type t)

and dest_module_wc t =
   let loc = dest_loc t in
   let sl1, mt = two_subterms t in
      WcMod (loc, List.map dest_string (subterms_of_term sl1), dest_mt mt)

(*
 * Module expressions.
 *)
and dest_proj_me t =
   let loc = dest_loc t in
   let me1, me2 = two_subterms t in
      <:module_expr< $dest_me me1$ . $dest_me me2$ >>

and dest_apply_me t =
   let loc = dest_loc t in
   let me1, me2 = two_subterms t in
      <:module_expr< $dest_me me1$ $dest_me me2$ >>

and dest_functor_me t =
   let loc = dest_loc t in
   let v, mt, me = dest_dep0_dep1_any_term t in
      <:module_expr< functor ($v$ : $dest_mt mt$ ) -> $dest_me me$ >>

(*
and dest_lid_me t =
   let loc = dest_loc t in
      <:module_expr< $lid:dest_var t$ >>
*)

and dest_struct_me t =
   let loc = dest_loc t in
   let stl = subterms_of_term t in
      <:module_expr< struct $list: List.map dest_str stl$ end >>

and dest_cast_me t =
   let loc = dest_loc t in
   let me, mt = two_subterms t in
      <:module_expr< ( $dest_me me$ : $dest_mt mt$) >>

and dest_uid_me t =
   let loc = dest_loc t in
      <:module_expr< $uid:dest_var t$ >>

(*
 * Class type.
 *)
and dest_class_type t =
   let loc = dest_loc t in
      match subterms_of_term t with
         [s; sl; tl1; so; ctfl; b1; b2] ->
             { ctLoc = loc;
               ctNam = dest_string s;
               ctPrm = List.map dest_string (subterms_of_term sl);
               ctArg = List.map dest_type (subterms_of_term tl1);
               ctTyc = dest_string_opt so;
               ctFld = List.map dest_ctf (subterms_of_term ctfl);
               ctVir = dest_bool b1;
               ctCls = dest_bool b2
             }
       | _ ->
             raise (FormatError ("class type format not recognized", t))

and dest_ctr_ctf t =
   let loc = dest_loc t in
   let s, t = two_subterms t in
      CtCtr (loc, dest_string s, dest_type t)

and dest_inh_ctf t =
   let loc = dest_loc t in
   let t = one_subterm t in
      CtInh (loc, dest_type t)

and dest_mth_ctf t =
   let loc = dest_loc t in
   let s, t = two_subterms t in
      CtMth (loc, dest_string s, dest_type t)

and dest_val_ctf t =
   let loc = dest_loc t in
   let s, b1, b2, ot = four_subterms t in
      CtVal (loc, dest_string s, dest_bool b1, dest_bool b2, dest_type_opt ot)

and dest_vir_ctf t =
   let loc = dest_loc t in
   let s, t = two_subterms t in
      CtVir (loc, dest_string s, dest_type t)

(*
 * Classes.
 *)
and dest_class t =
   let loc = dest_loc t in
      match subterms_of_term t with
         [s; sl1; pl1; so1; so2; cfl; b1; b2] ->
             { cdLoc = loc;
               cdNam = dest_string s;
               cdPrm = List.map dest_string (subterms_of_term sl1);
               cdArg = List.map dest_patt (subterms_of_term pl1);
               cdSlf = dest_string_opt so1;
               cdTyc = dest_string_opt so2;
               cdFld = List.map dest_cf (subterms_of_term cfl);
               cdVir = dest_bool b1;
               cdCls = dest_bool b2
             }
       | _ ->
             raise (FormatError ("class format not recognized", t))

and dest_ctr_cf t =
   let loc = dest_loc t in
   let s, t = two_subterms t in
      CfCtr (loc, dest_string s, dest_type t)

and dest_inh_cf t =
   let loc = dest_loc t in
   let t, e, so = three_subterms t in
      CfInh (loc, dest_type t, dest_expr e, dest_string_opt so)

and dest_mth_cf t =
   let loc = dest_loc t in
   let s, e = two_subterms t in
      CfMth (loc, dest_string s, dest_expr e)

and dest_val_cf t =
   let loc = dest_loc t in
   let s, b1, b2, eo = four_subterms t in
      CfVal (loc, dest_string s, dest_bool b1, dest_bool b2, dest_expr_opt eo)

and dest_vir_cf t =
   let loc = dest_loc t in
   let s, t = two_subterms t in
      CfVir (loc, dest_string s, dest_type t)

(*
 * Utilities.
 *)
and dest_pwe t =
   let p, wo, e = three_subterms t in
      dest_patt p, dest_expr_opt wo, dest_expr e

and dest_pe t =
   let p, e = two_subterms t in
      dest_patt p, dest_expr e

and dest_se t =
   let s, e = two_subterms t in
      dest_string s, dest_expr e

and dest_ee t =
   let e1, e2 = two_subterms t in
      dest_expr e1, dest_expr e2

and dest_pp t =
   let p1, p2 = two_subterms t in
      dest_patt p1, dest_patt p2

and dest_st t =
   let s, t = two_subterms t in
      dest_string s, dest_type t

and dest_sbt t =
   let s, b, t = three_subterms t in
      dest_string s, dest_bool b, dest_type t

and dest_stl t =
   match subterms_of_term t with
      s :: tl ->
         dest_string s, List.map dest_type tl
    | [] ->
         raise (FormatError ("Caml_syntax.dest_stl: requires a subterm", t))

and dest_sslt t =
   match subterms_of_term t with
      s :: slt ->
         let sl, t = List_util.split_last slt in
            dest_string s, List.map dest_string sl, dest_type t
   | [] ->
      raise (FormatError ("Caml_syntax.dest_sslt: requires a subterm", t))

and dest_expr_opt t = dest_opt dest_expr t

and dest_type_opt t = dest_opt dest_type t

and dest_bool t =
   let op = opname_of_term t in
      not (op == false_op)

(*
 * Destruction uses hashtables.
 *)
and dest_expr t = dest_tbl "expr" expr_table t
and dest_patt t = dest_tbl "patt" patt_table t
and dest_type t = dest_tbl "type" type_table t
and dest_sig  t = dest_tbl "sig"  sig_table  t
and dest_str  t = dest_tbl "str"  str_table  t
and dest_mt   t = dest_tbl "mt"   mt_able    t
and dest_me   t = dest_tbl "me"   me_table   t
and dest_wc   t = dest_tbl "wc"   wc_table   t
and dest_ctf  t = dest_tbl "ctf"  ctf_table  t
and dest_cf   t = dest_tbl "cf"   cf_table   t

and add_expr name f = add_tbl expr_table name f
and add_patt name f = add_tbl patt_table name f
and add_type name f = add_tbl type_table name f
and add_sig  name f = add_tbl sig_table  name f
and add_str  name f = add_tbl str_table  name f
and add_mt   name f = add_tbl mt_able    name f
and add_me   name f = add_tbl me_table   name f
and add_wc   name f = add_tbl wc_table   name f
and add_ctf  name f = add_tbl ctf_table  name f
and add_cf   name f = add_tbl cf_table   name f

(************************************************************************
 * OPERATOR NAMES							*
 ************************************************************************)

let expr_char_op		= add_expr "char" 		dest_char_expr
let expr_float_op		= add_expr "float"		dest_float_expr
let expr_int_op			= add_expr "int"		dest_int_expr
let expr_string_op              = add_expr "string"             dest_string_expr
let expr_lid_op			= add_expr "lid"		dest_lid_expr
let expr_uid_op			= add_expr "uid"		dest_uid_expr

let expr_proj_op 		= add_expr "proj"		dest_proj_expr
let expr_apply_op 		= add_expr "apply"		dest_apply_expr
let expr_array_subscript_op 	= add_expr "array_subscript"	dest_array_subscript_expr
let expr_array_op 		= add_expr "array"		dest_array_expr
let expr_assign_op		= add_expr "assign"		dest_assign_expr
let expr_coerce_class_op	= add_expr "coerce_class"	dest_coerce_class_expr
let expr_upto_op		= add_expr "for_upto"		dest_upto_expr
let expr_downto_op		= add_expr "for_downto"		dest_downto_expr
let expr_fun_op			= add_expr "fun"      	        dest_fun_expr
let expr_if_op			= add_expr "if"			dest_if_expr
let expr_letrec_op		= add_expr "letrec"		dest_letrec_expr
let expr_let_op			= add_expr "let"		dest_let_expr
let expr_match_op		= add_expr "match"		dest_match_expr
let expr_new_op			= add_expr "new"		dest_new_expr
let expr_stream_op		= add_expr "stream"		dest_stream_expr
let expr_record_op		= add_expr "record"		dest_record_expr
let expr_seq_op			= add_expr "sequence"		dest_seq_expr
let expr_select_op		= add_expr "select"		dest_select_expr
let expr_string_subscript_op	= add_expr "string_subscript"	dest_string_subscript_expr
let expr_try_op			= add_expr "try"		dest_try_expr
let expr_tuple_op		= add_expr "tuple"		dest_tuple_expr
let expr_cast_op		= add_expr "cast"		dest_cast_expr
let expr_while_op		= add_expr "while"		dest_while_expr

let patt_int_op			= add_patt "patt_int"           dest_int_patt
let patt_string_op		= add_patt "patt_string"        dest_string_patt
let patt_char_op		= add_patt "patt_char"          dest_char_patt
let patt_lid_op			= add_patt "patt_lid"           dest_lid_patt
let patt_uid_op			= add_patt "patt_uid"           dest_uid_patt
let patt_proj_op		= add_patt "patt_proj"          dest_proj_patt
let patt_as_op			= add_patt "patt_as"            dest_as_patt
let patt_wildcard_op		= add_patt "patt_wildcard"      dest_wildcard_patt
let patt_apply_op		= add_patt "patt_apply"         dest_apply_patt
let patt_choice_op		= add_patt "patt_choice"        dest_choice_patt
let patt_range_op		= add_patt "patt_range"         dest_range_patt
let patt_record_op		= add_patt "patt_record"        dest_record_patt
let patt_tuple_op		= add_patt "patt_tuple"         dest_tuple_patt
let patt_cast_op		= add_patt "patt_cast"          dest_cast_patt

let type_lid_op                 = add_type "type_lid"           dest_lid_type
let type_uid_op                 = add_type "type_uid"           dest_uid_type
let type_proj_op		= add_type "type_proj"          dest_proj_type
let type_as_op			= add_type "type_as"            dest_as_type
let type_wildcard_op		= add_type "type_wildcard"      dest_wildcard_type
let type_apply_op		= add_type "type_apply_op"      dest_apply_type
let type_fun_op                 = add_type "type_fun_op"        dest_fun_type
let type_class_id_op		= add_type "type_class_id"      dest_class_id_type
let type_param_op		= add_type "type_param"         dest_param_type
let type_equal_op		= add_type "type_equal"         dest_equal_type
let type_object_tt_op		= add_type "type_object_tt"     dest_object_tt_type
let type_object_ff_op		= add_type "type_object_ff"     dest_object_ff_type
let type_record_op		= add_type "type_record"        dest_record_type
let type_list_op		= add_type "type_list"          dest_list_type
let type_prod_op		= add_type "type_prod"          dest_prod_type

let sig_class_op		= add_sig "sig_class"           dest_class_sig
let sig_subsig_op		= add_sig "sig_subsig"          dest_subsig_sig
let sig_exception_op		= add_sig "sig_exception"       dest_exception_sig
let sig_external_op		= add_sig "sig_external"        dest_external_sig
let sig_module_op		= add_sig "sig_module"          dest_module_sig
let sig_module_type_op		= add_sig "sig_module_type"     dest_module_type_sig
let sig_open_op			= add_sig "sig_open"            dest_open_sig
let sig_type_op			= add_sig "sig_type"            dest_type_sig
let sig_value_op		= add_sig "sig_value"           dest_value_sig

let str_class_op		= add_str "str_class"           dest_class_str
let str_substruct_op		= add_str "str_substruct"       dest_substruct_str
let str_exception_op		= add_str "str_exception"       dest_exception_str
let str_expr_op			= add_str "str_expr"            dest_expr_str
let str_external_op		= add_str "str_external"        dest_external_str
let str_module_op		= add_str "str_module"          dest_module_str
let str_module_type_op		= add_str "str_module_type"     dest_module_type_str
let str_open_op			= add_str "str_open"            dest_open_str
let str_type_op			= add_str "str_type"            dest_type_str
let str_letrec_op		= add_str "str_letrec"          dest_letrec_str
let str_let_op			= add_str "str_let"             dest_let_str

let mt_lid_op			= add_mt "mt_lid"               dest_lid_mt
let mt_uid_op			= add_mt "mt_uid"               dest_uid_mt
let mt_proj_op			= add_mt "mt_proj"              dest_proj_mt
let mt_apply_op                 = add_mt "mt_apply"             dest_apply_mt
let mt_functor_op		= add_mt "mt_functor"           dest_functor_mt
let mt_sig_op			= add_mt "mt_sig"               dest_sig_mt
let mt_type_with_op		= add_mt "mt_type_with"         dest_with_mt

let wc_type_op     		= add_wc "wc_type"              dest_type_wc
let wc_module_op   		= add_wc "wc_module"            dest_module_wc

(* let me_lid_op			= add_me "me_lid"               dest_lid_me *)
let me_uid_op			= add_me "me_uid"               dest_uid_me
let me_proj_op			= add_me "me_proj"              dest_proj_me
let me_apply_op			= add_me "me_apply"             dest_apply_me
let me_functor_op		= add_me "me_functor"           dest_functor_me
let me_struct_op		= add_me "me_struct"            dest_struct_me
let me_cast_op			= add_me "me_cast"              dest_cast_me

let class_type_op		= mk_ocaml_op "class_type"

let ctf_ctr_op                  = add_ctf "class_type_ctr"      dest_ctr_ctf
let ctf_inh_op                  = add_ctf "class_type_inh"      dest_inh_ctf
let ctf_mth_op                  = add_ctf "class_type_mth"      dest_mth_ctf
let ctf_val_op                  = add_ctf "class_type_val"      dest_val_ctf
let ctf_vir_op                  = add_ctf "class_type_vir"      dest_vir_ctf

let class_op			= mk_ocaml_op "class"

let cf_ctr_op                   = add_cf "class_ctr"            dest_ctr_cf
let cf_inh_op                   = add_cf "class_inh"            dest_inh_cf
let cf_mth_op                   = add_cf "class_mth"            dest_mth_cf
let cf_val_op                   = add_cf "class_val"            dest_val_cf
let cf_vir_op                   = add_cf "class_vir"            dest_vir_cf

let pwe_op                      = mk_ocaml_op "pwe"
let pe_op                       = mk_ocaml_op "pe"
let se_op                       = mk_ocaml_op "se"
let ee_op                       = mk_ocaml_op "ee"
let pp_op                       = mk_ocaml_op "pp"
let st_op                       = mk_ocaml_op "st"
let sbt_op                      = mk_ocaml_op "sbt"
let stl_op                      = mk_ocaml_op "stl"
let sslt_op                     = mk_ocaml_op "sslt"

(*
 * $Log$
 * Revision 1.1  1998/01/27 23:04:30  jyh
 * Adding OCaml1.07 syntax.
 *
 *)