(*
 * Interval sets for integers, rawints, and floats.
 * For us, and interval-set is a list of intervals.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2002 Jason Hickey, Caltech
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
 * @email{jyh@cs.caltech.edu}
 * @end[license]
 *)
extends M_prec
extends M_int
extends M_rawint

open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.RefineError

open Lm_interval_set

open Fir
open Fir_set

open M_int
open M_rawint

(*
 * An interval has two bounds, and a set is just
 * a list of intervals.
 *)
declare Infinity
declare Closed{'i}
declare Open{'i}
declare interval{'lower; 'upper}

(*
 * The intervals are in a list.
 *)
declare IntSet{'intervals}
declare RawIntSet[precision:n, signed:t]{'intervals}

(*
 * Display.
 *)
declare left{'i}
declare right{'i}

dform left_infinity_df : left{Infinity} =
   `"(inf"

dform left_closed_df : left{Closed{'i}} =
   `"[" slot{'i}

dform left_open_df : left{Open{'i}} =
   `"(" slot{'i}

dform right_infinity_df : right{Infinity} =
   `"inf)"

dform right_closed_df : right{Closed{'i}} =
   slot{'i} `"]"

dform right_open_df : right{Open{'i}} =
   slot{'i} `")"

dform interval_df : interval{'lower; 'upper} =
   left{'lower} `".." right{'upper}

(*
 * Interval sets.
 *)
declare interval_list{'intervals}

dform int_set_df : IntSet{'intervals} =
   szone pushm[0] pushm[3] bf["IntSet"] `"{ " interval_list{'intervals} popm hspace `"}" popm ezone

dform raw_int_set_df : RawIntSet[p:n, s:t]{'intervals} =
   szone pushm[0] pushm[3] bf["RawIntSet"] M_rawint!precision[p:n, s:t] `"{ " interval_list{'intervals} popm hspace `"}" popm ezone

dform interval_list_cons_df1 : interval_list{cons{'a; cons{'b; 'c}}} =
   slot{'a} `"," hspace interval_list{cons{'b; 'c}}

dform interval_list_cons_df2 : interval_list{cons{'a; nil}} =
   slot{'a}

dform interval_list_nil_df : interval_list{nil} =
   `""

(************************************************************************
 * Term conversions.
 *)

(*
 * Sets.
 *)
let term_Infinity = << Infinity >>
let opname_Infinity = opname_of_term term_Infinity
let term_Closed = << Closed{'i} >>
let opname_Closed = opname_of_term term_Closed
let term_Open = << Open{'i} >>
let opname_Open = opname_of_term term_Open

let dest_bound dest_int t =
   let { term_op = op; term_terms = bterms } = dest_term t in
   let { op_name = op; op_params = params } = dest_op op in
   let params = dest_params params in
   let bterms = List.map dest_bterm bterms in
      match params, bterms with
         [], []
         when Opname.eq op opname_Infinity ->
            Infinity
       | [], [{ bvars = []; bterm = i }] ->
            let i = dest_int i in
               if Opname.eq op opname_Closed then
                  Closed i
               else if Opname.eq op opname_Open then
                  Open i
               else
                  raise (RefineError ("dest_bound", StringTermError ("not a bound", t)))
       | _ ->
            raise (RefineError ("dest_bound", StringTermError ("not a bound", t)))

let make_bound make_int i =
   match i with
      Infinity ->
         term_Infinity
    | Closed i ->
         mk_simple_term opname_Closed [make_int i]
    | Open i ->
         mk_simple_term opname_Open [make_int i]

(*
 * Intervals.
 *)
let term_interval = << interval{'lower; 'upper} >>
let opname_interval = opname_of_term term_interval

let dest_interval dest_int t =
   if Opname.eq (opname_of_term t) opname_interval then
      let lower, upper = two_subterms t in
      let lower = dest_bound dest_int lower in
      let upper = dest_bound dest_int upper in
         (lower, upper)
   else
      raise (RefineError ("dest_interval", StringTermError ("not an interval", t)))

let make_interval make_int lower upper =
   mk_simple_term opname_interval [make_bound make_int lower; make_bound make_int upper]

(*
 * The intervals are in a list.
 *)
let term_IntSet = << IntSet{'intervals} >>
let opname_IntSet = opname_of_term term_IntSet
let term_RawIntSet = << RawIntSet[p:n, s:t]{'intervals} >>
let opname_RawIntSet = opname_of_term term_RawIntSet

(*
 * Integer-only sets.
 *)
let dest_int_set t =
   let { term_op = op; term_terms = bterms } = dest_term t in
   let { op_name = op; op_params = params } = dest_op op in
   let params = dest_params params in
   let bterms = List.map dest_bterm bterms in
      match params, bterms with
         [], [{ bvars = []; bterm = intervals }]
         when Opname.eq op opname_IntSet ->
            let intervals = dest_xlist intervals in
               List.fold_left (fun set t ->
                     let lower, upper = dest_interval dest_int t in
                     let set' = IntSet.of_interval lower upper in
                        IntSet.union set set') IntSet.empty intervals
       | _ ->
            raise (RefineError ("dest_int_set", StringTermError ("not a set", t)))

let make_int_set set =
   let intervals =
      IntSet.fold (fun l lower upper ->
            make_interval make_int lower upper :: l) [] set
   in
      mk_simple_term opname_IntSet [mk_xlist_term intervals]


(*
 * Any set.
 *)
let dest_set t =
   let { term_op = op; term_terms = bterms } = dest_term t in
   let { op_name = op; op_params = params } = dest_op op in
   let params = dest_params params in
   let bterms = List.map dest_bterm bterms in
      match params, bterms with
         [], [{ bvars = []; bterm = intervals }]
         when Opname.eq op opname_IntSet ->
            let intervals = dest_xlist intervals in
            let set =
               List.fold_left (fun set t ->
                     let lower, upper = dest_interval dest_int t in
                     let set' = IntSet.of_interval lower upper in
                        IntSet.union set set') IntSet.empty intervals
            in
               IntSet set

       | [Number p; Token s], [{ bvars = []; bterm = intervals }]
         when Opname.eq op opname_RawIntSet ->
            let p = rawint_precision_of_num p in
            let s = boolean_of_string s in
            let intervals = dest_xlist intervals in
            let set =
               List.fold_left (fun set t ->
                     let lower, upper = dest_interval dest_rawint t in
                     let set' = RawIntSet.of_interval p s lower upper in
                        RawIntSet.union set set') (RawIntSet.empty p s) intervals
            in
               RawIntSet set

       | _ ->
            raise (RefineError ("dest_interval_set", StringTermError ("not a set", t)))

let make_set set =
   match set with
      IntSet set ->
         let intervals =
            IntSet.fold (fun l lower upper ->
                  make_interval make_int lower upper :: l) [] set
         in
            mk_simple_term opname_IntSet [mk_xlist_term intervals]
    | RawIntSet set ->
         let p = RawIntSet.precision set in
         let s = RawIntSet.signed set in
         let intervals =
            RawIntSet.fold (fun l lower upper ->
                  make_interval make_rawint lower upper :: l) [] set
         in
         let params =
            [make_param (Number (num_of_rawint_precision p));
             make_param (Token (string_of_boolean s))]
         in
         let op = mk_op opname_RawIntSet params in
         let intervals = mk_xlist_term intervals in
         let bterm = mk_bterm [] intervals in
            mk_term op [bterm]

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
