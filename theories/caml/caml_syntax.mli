(*
 * OCaml expressions.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
 *
 * Copyright (C) 1998 Jason Hickey, Cornell University
 * 
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 * 
 * Author: Jason Hickey
 * jyh@cs.cornell.edu
 *)
declare proj{'e1; 'e2}
declare apply{'e1; 'e2}
declare array_subscript{'e1; 'e2}
declare "array"{'a}
declare assign{'e1; 'e2}
declare "char"[$c:s]
declare coerce{'e; 't}
declare "float"[$f:s]
declare for_upto{'s; 't; v. 'body]
declare for_downto{'s; 't; v. 'body]
declare lambda_pattern{'a}
declare "if"{'e1; 'e2; 'e3}
declare "int"[$i:n]
declare letrec{'e; 'body}
declare "let"{'e; 'body}
declare "match"{'e; 'body}
declare "new"{'e}
declare stream{'sel}
declare record{'el}
declare sequence{'el}
declare select{'e; 'i}
declare string_subscript{'e; 'i}
declare "try"{'e; 'pwel}
declare tuple{'el}
declare cast{'e; 't}
declare "while"{'e; 'body}

(*
 * Patterns.
 *)
declare patt_proj{'p1; 'p2}
declare patt_as{'p1; 'p2}
declare patt_wildcard{}
declare patt_apply{'p1; 'p2}
declare patt_char[$s:n]
declare patt_int[$i:n]
declare patt_lid[$i:n]
declare patt_uid[$i:n]
declare patt_choice{'p1; 'p2}
declare patt_range{'p1; 'p2}
declare patt_record{'pl}
declare patt_string[$s:s]
declare patt_tuple{'pl}
declare patt_cast{'p; 't}

(*
 * Types.
 *)
declare type_proj{'t1; 't2}
declare type_as{'t1; 't2}
declare type_wildcard
declare type_apply{'t1; 't2}
declare type_fun{'t1; 't2}
declare type_class_id{'t}
declare type_lid[$v:v]
declare type_param[$s:s]
declare type_equal{'t1; 't2}
declare type_object_tt{'stl}
declare type_object_ff{'stl}
declare type_record{'tl}
declare type_list{'t}
declare type_prod{'t1; 't2}
declare type_uid[$v:v]

(*
 * Signature items.
 *)
declare sig_class{'ctl}
declare sig_exception{'tl}
declare sig_external{'t; 'sl}
declare sig_module{'mt}
declare sig_module_type{'mt}
declare sig_open{'path}
declare sig_type{'ssltl}
declare sig_value{'t}

(*
 * Structure items.
 *)
declare str_class{'cdl}
declare str_exception{'stl}
declare str_expr{'e}
declare str_external{'t; 'sl}
declare str_module{'me}
declare str_module_type{'mt}
declare str_open{'sl}
declare str_type{'ssltl}
declare str_let{'pel}
declare str_letrec{'pel}

(*
 * Module type.
 *)
declare mt_proj{'mt1;'mt2}
declare mt_apply{'mt1; 'mt2}
declare mt_functor{'mt1; v. 'mt2}
declare mt_lid[$v:v]
declare mt_sig{'sil}
declare mt_uid[$v:v]
declare mt_type_with{'mt; 'wcl}

(*
 * With clause.
 *)
declare wc_type{'sl1; 'sl2; 't}
declare wc_module{'sl1; 'mt}

(*
 * Module expression.
 *)
declare me_proj{'me1; 'me2}
declare me_apply{'me1; 'me2}
declare me_functor{'mt; v. 'me}
declare me_lid[$v:v]
declare me_struct{'sil}
declare me_cast{'me; 'mt}
declare me_uid[$v:v]

(*
 * Class type.
 *)
declare class_type{'sl; 't; 'so; 'ctfl; 'b1; 'b2}

(*
 * Class type field.
 *)
declare class_type_ctr{'s; 't}
declare class_type_inh{'t}
declare class_type_mth{'s; 't}
declare class_type_val{'s; 'b1; 'b2; 'to}
declare class_type_vir{'s; 't}

(*
 * Class.
 *)
declare class{'sl1; 'pl1; 'so1; 'so2; 'cfl; 'b1; 'b2}

(*
 * Class field.
 *)
declare class_ctr{'s; 't}
declare class_inh{'t; 'e; 'so}
declare class_mth{'s; 'e}
declare class_val{'s; 'b1; 'b2; 'eo}
declare class_vir{'s; 't}

(*
 * -*-
 * Local Variables:
 * Caml-master: "refiner"
 * End:
 * -*-
 *)
