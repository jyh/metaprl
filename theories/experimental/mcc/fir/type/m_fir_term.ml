(*
 * term<->FIR conversions.
 *
 * ----------------------------------------------------------------
 *
 * @begin[license]
 * Copyright (C) 2003 Jason Hickey, Caltech
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
 * @docoff
 *)
extends M_fir

open Refiner.Refiner.TermType
open Refiner.Refiner.Term
open Refiner.Refiner.TermOp
open Refiner.Refiner.TermMan
open Refiner.Refiner.RefineError

open Lm_symbol

open Fir

open M_int
open M_rawint
open M_rawfloat
open M_set

(*
 * Term forms.
 *)
type term_ty   = term poly_ty
type term_atom = (term, term) poly_atom
type term_exp  = (term, term, term) poly_exp

(* No delayed substitutions *)
type exp       = (ty, atom, exp) poly_exp

(*
 * Basic utilities.
 *)
let dest_symbol t =
   Symbol.add (dest_var t)

let make_symbol v =
   mk_var_term (Symbol.to_string v)

(*
 * We frequently have terms with rawint precision/signed parameters.
 *)
let make_rawint_term opname p s =
   let params =
      [make_param (Number (num_of_rawint_precision p));
       make_param (Token (string_of_boolean s))]
   in
   let op = mk_op opname params in
      mk_term op []

let make_rawfloat_term opname p =
   let params = [make_param (Number (num_of_rawfloat_precision p))] in
   let op = mk_op opname params in
      mk_term op []

(*
 * Options.
 *)
let term_None = << None >>
let opname_None = opname_of_term term_None
let term_Some = << Some{'t} >>
let opname_Some = opname_of_term term_Some

let dest_option dest_val t =
   let { term_op = op; term_terms = bterms } = dest_term t in
   let { op_name = op; op_params = params } = dest_op op in
   let params = dest_params params in
   let bterms = List.map dest_bterm bterms in
      match params, bterms with
         [], []
         when Opname.eq op opname_None ->
            None

       | [], [{ bvars = []; bterm = t }] ->
            Some (dest_val t)

       | _ ->
            raise (RefineError ("dest_option", StringTermError ("not an option", t)))

let make_option make_val t =
   match t with
      None ->
         term_None
    | Some t ->
         mk_simple_term opname_Some [make_val t]

(*
 * Types of tuples:
 *
 *    NormalTuple
 *       Each element in the tuple must be a ``smalltype'' -- is, elements
 *       can be polymorphic values or other word- size data, but cannot be
 *       raw data (RawInt or Float).
 *
 *    RawTuple
 *       Can contain pointers and other rawdata.  Requires a slightly
 *       different runtime representation, where the first field in the
 *       tuple contains run-time type information.  Used by Java, where we
 *       have type safety but also raw data within tuples.
 *
 *    BoxTuple
 *       Must be a 1-tuple, but the element can be a value of any type.
 *       Used to box raw data (RawInt and Floats)
 *)
let term_NormalTuple = << NormalTuple >>
let opname_NormalTuple = opname_of_term term_NormalTuple
let term_RawTuple = << RawTuple >>
let opname_RawTuple = opname_of_term term_RawTuple
let term_BoxTuple = << BoxTuple >>
let opname_BoxTuple = opname_of_term term_BoxTuple

let dest_tuple_class t =
   let op = opname_of_term t in
      if Opname.eq op opname_NormalTuple then
         NormalTuple
      else if Opname.eq op opname_RawTuple then
         RawTuple
      else if Opname.eq op opname_BoxTuple then
         BoxTuple
      else
         raise (RefineError ("dest_tuple_class", StringError "not a tuple_class"))

let make_tuple_class tc =
   match tc with
      NormalTuple -> term_NormalTuple
    | RawTuple -> term_RawTuple
    | BoxTuple -> term_BoxTuple

(*
 * The fields in tuples, unions, and dtuples are allowed to
 * be mutable (array fields are always mutable).  The following
 * flags determine mutablility:
 *
 *    Mutable: the field is mutable
 *    Immutable: the field is not mutable
 *
 *    MutableDelayed:
 *       The mutability is not known.  This is eliminated
 *       by type inference, and it will not pass the type
 *       checker.
 *
 *    MutableVar v:
 *       This is used only during type inference, where
 *       the mutability is associated with a variable
 *       in a substitution table.
 *)
let term_Mutable = << Mutable >>
let opname_Mutable = opname_of_term term_Mutable
let term_Immutable = << Immutable >>
let opname_Immutable = opname_of_term term_Immutable
let term_MutableDelayed = << MutableDelayed >>
let opname_MutableDelayed = opname_of_term term_MutableDelayed
let term_MutableVar = << MutableVar{'v} >>
let opname_MutableVar = opname_of_term term_MutableVar

let dest_mutable_flag t =
   let op = opname_of_term t in
      if Opname.eq op opname_Mutable then
         Mutable
      else if Opname.eq op opname_Immutable then
         Immutable
      else if Opname.eq op opname_MutableDelayed then
         MutableDelayed
      else if Opname.eq op opname_MutableVar then
         let v = dest_symbol (one_subterm t) in
            MutableVar v
      else
         raise (RefineError ("dest_mutable_flag", StringTermError ("not a mutable_flag", t)))

let make_mutable_flag flag =
   match flag with
      Mutable ->
         term_Mutable
    | Immutable ->
         term_Immutable
    | MutableDelayed ->
         term_MutableDelayed
    | MutableVar v ->
         mk_dep0_term opname_MutableVar (make_symbol v)

(*
 * Subscript operations.  The subop is a hint to the backend on how to
 * interpret the data being read/written, and how to interpret the index
 * value used in subscripting.  A subscript operation has four parts:
 *
 *    1. the kind of block being subscripted:
 *          BlockSub:    a ML block: TyUnion, TyTuple, TyArray
 *          RawDataSub:  a TyRawData block
 *          TupleSub:    a ML block containing only pointers
 *          RawTupleSub: a mixed rawdata/pointer block
 *
 *    2. the kind of element being read/written:
 *          PolySub:          a TyInt or a ML block
 *          RawIntSub:        a TyRawInt with indicated precision/signed
 *          RawFloatSub:      a TyRawFloat with indicated precision
 *          PointerInfixSub:  a infix pointer (pair of base and offset ptr)
 *          BlockPointerSub:  a data pointer
 *          RawPointerSub:    a data pointer
 *          FunctionSub:      a function pointer
 *
 *       (note that the actual memory format for these values is not
 *        specified until the MIR)
 *
 *    3. the element width (used to determine how to read the index):
 *          ByteSub: byte width
 *          WordSub: word width
 *
 *    4. the kind of subscript index:
 *          IntIndex: ML-style int subscript
 *          RawIntIndex (pre, signed): rawint subscript
 *)
let term_BlockSub = << BlockSub >>
let opname_BlockSub = opname_of_term term_BlockSub
let term_RawDataSub = << RawDataSub >>
let opname_RawDataSub = opname_of_term term_RawDataSub
let term_TupleSub = << TupleSub >>
let opname_TupleSub = opname_of_term term_TupleSub
let term_RawTupleSub = << RawTupleSub >>
let opname_RawTupleSub = opname_of_term term_RawTupleSub

let dest_sub_block t =
   let op = opname_of_term t in
      if Opname.eq op opname_BlockSub then
         BlockSub
      else if Opname.eq op opname_RawDataSub then
         RawDataSub
      else if Opname.eq op opname_TupleSub then
         TupleSub
      else if Opname.eq op opname_RawTupleSub then
         RawTupleSub
      else
         raise (RefineError ("dest_mutable_flag", StringTermError ("not a sub_block", t)))

let make_sub_block flag =
   match flag with
      BlockSub ->
         term_BlockSub
    | RawDataSub ->
         term_RawDataSub
    | TupleSub ->
         term_TupleSub
    | RawTupleSub ->
         term_RawTupleSub

(*
 * sub_index.
 *)
let term_ByteIndex = << ByteIndex >>
let opname_ByteIndex = opname_of_term term_ByteIndex
let term_WordIndex = << WordIndex >>
let opname_WordIndex = opname_of_term term_WordIndex

let dest_sub_index t =
   let op = opname_of_term t in
      if Opname.eq op opname_ByteIndex then
         ByteIndex
      else if Opname.eq op opname_WordIndex then
         WordIndex
      else
         raise (RefineError ("dest_mutable_flag", StringTermError ("not a sub_index", t)))

let make_sub_index flag =
   match flag with
      ByteIndex ->
         term_ByteIndex
    | WordIndex ->
         term_WordIndex

(*
 * sub_script.
 *)
let term_IntIndex = << IntIndex >>
let opname_IntIndex = opname_of_term term_IntIndex
let term_RawIntIndex = << RawIntIndex[precision:n, signed:t] >>
let opname_RawIntIndex = opname_of_term term_RawIntIndex

let dest_sub_script t =
   let { term_op = op; term_terms = bterms } = dest_term t in
   let { op_name = op; op_params = params } = dest_op op in
   let params = dest_params params in
   let bterms = List.map dest_bterm bterms in
      match params, bterms with
         [], []
         when Opname.eq op opname_IntIndex ->
            IntIndex

       | [Number p; Token s], []
         when Opname.eq op opname_RawIntIndex ->
            let p = rawint_precision_of_num p in
            let s = boolean_of_string s in
               RawIntIndex (p, s)

       | _ ->
         raise (RefineError ("dest_mutable_flag", StringTermError ("not a sub_script", t)))

let make_sub_script flag =
   match flag with
      IntIndex ->
         term_IntIndex
    | RawIntIndex (p, s) ->
         let params =
            [make_param (Number (num_of_rawint_precision p));
             make_param (Token (string_of_boolean s))]
         in
         let op = mk_op opname_RawIntIndex params in
            mk_term op []

(*
 * Mutable types.
 *)
let term_TyMutable = << TyMutable{'ty; 'mutable_flag} >>
let opname_TyMutable = opname_of_term term_TyMutable

(*
 * Mutable type.
 *)
let dest_poly_mutable dest_ty t =
   let { term_op = op; term_terms = bterms } = dest_term t in
   let { op_name = op; op_params = params } = dest_op op in
   let params = dest_params params in
   let bterms = List.map dest_bterm bterms in
      match params, bterms with
         [], [{ bvars = []; bterm = ty };
              { bvars = []; bterm = mutable_flag }]
         when Opname.eq op opname_TyMutable ->
            let ty = dest_ty ty in
            let mutable_flag = dest_mutable_flag mutable_flag in
               ty, mutable_flag

       | _ ->
            raise (RefineError ("dest_poly_mutable", StringTermError ("not a ty_mutable", t)))

let make_poly_mutable make_ty (ty, mutable_flag) =
   let ty = make_ty ty in
   let mutable_flag = make_mutable_flag mutable_flag in
      mk_simple_term opname_TyMutable [ty; mutable_flag]

(*
 * sub_value.
 *)
let term_EnumSub = << EnumSub[i:n] >>
let opname_EnumSub = opname_of_term term_EnumSub
let term_IntSub = << IntSub >>
let opname_IntSub = opname_of_term term_IntSub
let term_TagSub = << TagSub{'ty_var; 'ty_list} >>
let opname_TagSub = opname_of_term term_TagSub
let term_PolySub = << PolySub >>
let opname_PolySub = opname_of_term term_PolySub
let term_RawIntSub = << RawIntSub[precision:n, signed:t] >>
let opname_RawIntSub = opname_of_term term_RawIntSub
let term_RawFloatSub = << RawFloatSub[precision:n] >>
let opname_RawFloatSub = opname_of_term term_RawFloatSub
let term_PointerInfixSub = << PointerInfixSub >>
let opname_PointerInfixSub = opname_of_term term_PointerInfixSub
let term_BlockPointerSub = << BlockPointerSub >>
let opname_BlockPointerSub = opname_of_term term_BlockPointerSub
let term_RawPointerSub = << RawPointerSub >>
let opname_RawPointerSub = opname_of_term term_RawPointerSub
let term_FunctionSub = << FunctionSub >>
let opname_FunctionSub = opname_of_term term_FunctionSub

(*
 * Recursive definitions.
 *
 * 'ty poly_sub_value
 *)
let dest_poly_sub_value dest_ty t =
   let { term_op = op; term_terms = bterms } = dest_term t in
   let { op_name = op; op_params = params } = dest_op op in
   let params = dest_params params in
   let bterms = List.map dest_bterm bterms in
      match params, bterms with
         [], [] ->
            if Opname.eq op opname_IntSub then
               IntSub
            else if Opname.eq op opname_PolySub then
               PolySub
            else if Opname.eq op opname_PointerInfixSub then
               PointerInfixSub
            else if Opname.eq op opname_BlockPointerSub then
               BlockPointerSub
            else if Opname.eq op opname_RawPointerSub then
               RawPointerSub
            else if Opname.eq op opname_FunctionSub then
               FunctionSub
            else
               raise (RefineError ("dest_sub_value", StringTermError ("not a sub_value", t)))

         (* EnumSub *)
       | [Number i], []
         when Opname.eq op opname_EnumSub ->
            EnumSub (Lm_num.int_of_num i)

         (* TagSub *)
       | [], [{ bvars = []; bterm = ty_var };
              { bvars = []; bterm = ty_mutable_list }]
         when Opname.eq op opname_TagSub ->
            let ty_var = dest_symbol ty_var in
            let ty_list = dest_xlist ty_mutable_list in
            let ty_list = List.map (dest_poly_mutable dest_ty) ty_list in
               TagSub (ty_var, ty_list)

         (* RawIntSub *)
       | [Number p; Token s], []
         when Opname.eq op opname_RawIntSub ->
            let p = rawint_precision_of_num p in
            let s = bool_of_string s in
               RawIntSub (p, s)

         (* RawFloatSub *)
       | [Number p], []
         when Opname.eq op opname_RawFloatSub ->
            let p = rawfloat_precision_of_num p in
               RawFloatSub p

       | _ ->
            raise (RefineError ("dest_poly_sub_value", StringTermError ("not a sub_value", t)))

let make_poly_sub_value make_ty v =
   match v with
      EnumSub i ->
         let params = [make_param (Number (Lm_num.num_of_int i))] in
         let op = mk_op opname_EnumSub params in
            mk_term op []
    | IntSub ->
         term_IntSub
    | TagSub (ty_var, ty_mutable_list) ->
         let l = mk_xlist_term (List.map (make_poly_mutable make_ty) ty_mutable_list) in
         let ty_var = make_symbol ty_var in
            mk_simple_term opname_TagSub [ty_var; l]
    | PolySub ->
         term_PolySub
    | RawIntSub (p, s) ->
         let params =
            [make_param (Number (num_of_rawint_precision p));
             make_param (Token (string_of_boolean s))]
         in
         let op = mk_op opname_RawIntSub params in
            mk_term op []
    | RawFloatSub p ->
         let params = [make_param (Number (num_of_rawfloat_precision p))] in
         let op = mk_op opname_RawFloatSub params in
            mk_term op []
    | PointerInfixSub ->
         term_PointerInfixSub
    | BlockPointerSub ->
         term_BlockPointerSub
    | RawPointerSub ->
         term_RawPointerSub
    | FunctionSub ->
         term_FunctionSub

(*
 * subop.
 *)
let term_subop = << subop{'block; 'value; 'index; 'script} >>
let opname_subop = opname_of_term term_subop

(*
 * 'ty poly_subop.
 *)
let dest_poly_subop dest_ty t =
   let { term_op = op; term_terms = bterms } = dest_term t in
   let { op_name = op; op_params = params } = dest_op op in
   let params = dest_params params in
   let bterms = List.map dest_bterm bterms in
      match params, bterms with
         [], [{ bvars = []; bterm = sub_block };
              { bvars = []; bterm = sub_value };
              { bvars = []; bterm = sub_index };
              { bvars = []; bterm = sub_script }]
         when Opname.eq op opname_subop ->
            let sub_block = dest_sub_block sub_block in
            let sub_value = dest_poly_sub_value dest_ty sub_value in
            let sub_index = dest_sub_index sub_index in
            let sub_script = dest_sub_script sub_script in
               { sub_block = sub_block;
                 sub_value = sub_value;
                 sub_index = sub_index;
                 sub_script = sub_script
               }
       | _ ->
            raise (RefineError ("dest_poly_subop", StringTermError ("not a subop", t)))

let make_poly_subop make_ty subop =
   let { sub_block = sub_block;
         sub_value = sub_value;
         sub_index = sub_index;
         sub_script = sub_script
       } = subop
   in
   let sub_block = make_sub_block sub_block in
   let sub_value = make_poly_sub_value make_ty sub_value in
   let sub_index = make_sub_index sub_index in
   let sub_script = make_sub_script sub_script in
      mk_simple_term opname_subop [sub_block; sub_value; sub_index; sub_script]

(*
 * Types.  A few types are marked as ``not a smalltype''; the types marked
 * this way cannot be used in certain types of tuples or unions, and cannot
 * be used as a type argument in a TyApply or AtomTyApply.
 *
 * Unfortunately, types are polymorphic with respect to a 'mutable_flag,
 * which describes whether tuple and union fields are mutable.  The only
 * time when we use something other than the type mutable_flag here
 * is during type inference.
 *
 *    TyInt
 *       Normal 31-bit ML-style integer
 *
 *    TyEnum size
 *       Enumeration in the interval [0, size) (unsigned).  The
 *       size must be less than max_enum (defined in sizeof_const.ml).
 *
 *    TyRawInt (pre, signed)
 *       Raw integer, with indicated precision and signedness
 *       (not a smalltype).
 *
 *    TyFloat fpre
 *       Raw floating-point value, with indicated precision
 *       (not a smalltype).
 *
 *    TyFun (args, return)
 *       Function with indicated argument and return types.
 *
 *    TyUnion (union_name, type_args, int_set)
 *       Value of union_name case (union_name is bound in the type defs).
 *       The type_args are a list of types used to instantiate the union;
 *       they are NOT the types of the elements!  THe type_args must be
 *       smalltypes.
 *
 *       If the union has N cases, then the int_set is a subset of [0..N),
 *       and indicates which cases this union may be.  If int_set is a
 *       singleton set, then we know exactly which union case we are in,
 *       and can dereference the union pointer.
 *
 *       Union elements must be smalltypes.
 *
 *    TyTuple (tuple_class, flags_types)
 *       Tuple with indicated element types.  The flags indicate mutability
 *       of the field.  See tuple_class comments above for more information.
 *
 *    TyDTuple (ty_var, tyl_opt)
 *       A dependent-tuple type.  This represents the following type:
 *          Sigma (t1, ..., tn) : Type. t1 * ... * tn
 *       An element of this type is tagged with a TyTag (described below)
 *       that defines the element types.  The ty_var must refer to a
 *       TyDefDTuple.  If tyl_opt is (Some tyl), then tyl are the types
 *       of the elements; otherwise the element types are not known.
 *
 *    TyTag (ty_var, tyl)
 *       A tag used for constructing TyDTuple values (see AllocDTuple
 *       below).  The tyl are the types of the elements in the tuple.
 *
 *    TyArray t
 *       Array of elements, all of type t.
 *
 *    TyRawData
 *       Byte array of arbitrary data.  Used for most C data structures,
 *       where we don't know the types of the elements within.  Requires
 *       safety checks.
 *
 *    TyPointer sub_block
 *       Infix pointers; a pointer into rawdata that contains an offset
 *       from the base of a rawdata block.
 *
 *    TyFrame (frame_name, type_args)
 *       Pointer to frame data (frame_name is bound in the frame defs).
 *       The type_args are a list of types used to instantiate the frame;
 *       they must be smalltypes.
 *
 *       Frames are intended to be used for frames generated during closure
 *       conversion.  The assumption is that frames are not directly access-
 *       able to the programmer, so they do not escape.  As a result, we are
 *       free to store extra fields in the frame before a CPS call, and are
 *       guaranteed that the values will be correct when the continuation
 *       is called.  If this assumption is violated, the program will still
 *       be type-safe, but the Fir_closure module will change the semantics
 *       of the program.
 *
 *    TyVar ty_var
 *       Polymorphic type variable.
 *
 *    TyApply (ty_var, type_args)
 *       Apply polymorphic type_args to the type function indicated by
 *       ty_var (which is bound in the type defs).  type_args must all be
 *       smalltypes.
 *
 *    TyExists (poly_vars, t)
 *       Existential type, binding the named poly_vars.
 *
 *    TyAll (poly_vars, t)
 *       Universal type, binding the named poly_vars.
 *
 *    TyProject (v, i)
 *       If v is a variable with type TyExists (alpha_1, ..., alpha_n . t),
 *       then the projection v.i refers to alpha_i.
 *
 *    TyCase t
 *       Used for object system.
 *
 *    TyObject (ty_var, t)
 *       Used for object system.
 *
 *    TyDelayed
 *       Used by frontends and some optimizations to request that the
 *       FIR type inference infer this type automatically.  No TyDelayed's
 *       should exist in the program after type inference phase.
 *)
let term_TyInt = << TyInt >>
let opname_TyInt = opname_of_term term_TyInt
let term_TyEnum = << TyEnum[i:n] >>
let opname_TyEnum = opname_of_term term_TyEnum
let term_TyRawInt = << TyRawInt[precision:n, signed:t] >>
let opname_TyRawInt = opname_of_term term_TyRawInt
let term_TyFloat = << TyFloat[precision:n] >>
let opname_TyFloat = opname_of_term term_TyFloat
let term_TyFun = << TyFun{'ty_args; 'ty_res} >>
let opname_TyFun = opname_of_term term_TyFun
let term_TyUnion = << TyUnion{'ty_var; 'ty_list; 'int_set} >>
let opname_TyUnion = opname_of_term term_TyUnion
let term_TyTuple = << TyTuple{'tuple_class; 'mutable_ty_list} >>
let opname_TyTuple = opname_of_term term_TyTuple
let term_TyDTuple = << TyDTuple{'ty_var; 'mutable_ty_list} >>
let opname_TyDTuple = opname_of_term term_TyDTuple
let term_TyTag = << TyTag{'ty_var; 'mutable_ty_list} >>
let opname_TyTag = opname_of_term term_TyTag
let term_TyArray = << TyArray{'ty} >>
let opname_TyArray = opname_of_term term_TyArray
let term_TyRawData = << TyRawData >>
let opname_TyRawData = opname_of_term term_TyRawData
let term_TyPointer = << TyPointer{'sub_block} >>
let opname_TyPointer = opname_of_term term_TyPointer
let term_TyFrame = << TyFrame{'ty_var; 'ty_list} >>
let opname_TyFrame = opname_of_term term_TyFrame
let term_TyVar = << TyVar{'ty_var} >>
let opname_TyVar = opname_of_term term_TyVar
let term_TyApply = << TyApply{'ty_var; 'ty_list} >>
let opname_TyApply = opname_of_term term_TyApply
let term_TyExists = << TyExists{v. 'ty['v]} >>
let opname_TyExists = opname_of_term term_TyExists
let term_TyAll = << TyAll{v. 'ty['v]} >>
let opname_TyAll = opname_of_term term_TyAll
let term_TyProject = << TyProject[i:n]{'v} >>
let opname_TyProject = opname_of_term term_TyProject
let term_TyDelayed = << TyDelayed >>
let opname_TyDelayed = opname_of_term term_TyDelayed

(*
 * Type.
 *)
let dest_poly_type (dest_ty : term -> 'ty) (t : term) : 'ty poly_ty =
   let { term_op = op; term_terms = bterms } = dest_term t in
   let { op_name = op; op_params = params } = dest_op op in
   let params = dest_params params in
   let bterms = List.map dest_bterm bterms in
      match params, bterms with
         [], [] ->
            if Opname.eq op opname_TyInt then
               TyInt
            else if Opname.eq op opname_TyRawData then
               TyRawData
            else if Opname.eq op opname_TyDelayed then
               TyDelayed
            else
               raise (RefineError ("dest_ty", StringTermError ("not a type", t)))

         (* TyEnum *)
       | [Number i], []
         when Opname.eq op opname_TyEnum ->
            TyEnum (Lm_num.int_of_num i)

         (* TyRawInt *)
       | [Number p; Token s], []
         when Opname.eq op opname_TyRawInt ->
            let p = rawint_precision_of_num p in
            let s = boolean_of_string s in
               TyRawInt (p, s)

         (* TyFloat *)
       | [Number p], []
         when Opname.eq op opname_TyFloat ->
            let p = rawfloat_precision_of_num p in
               TyFloat p

         (* TyFun *)
       | [], [{ bvars = []; bterm = ty_args };
              { bvars = []; bterm = ty_res }]
         when Opname.eq op opname_TyFun ->
            let ty_args = dest_xlist ty_args in
            let ty_args = List.map dest_ty ty_args in
            let ty_res  = dest_ty ty_res in
               TyFun (ty_args, ty_res)

         (* TyUnion *)
       | [], [{ bvars = []; bterm = ty_var };
              { bvars = []; bterm = ty_list };
              { bvars = []; bterm = int_set }]
         when Opname.eq op opname_TyUnion ->
            let ty_var = dest_symbol ty_var in
            let ty_list = List.map dest_ty (dest_xlist ty_list) in
            let int_set = dest_int_set int_set in
               TyUnion (ty_var, ty_list, int_set)

         (* TyTuple *)
       | [], [{ bvars = []; bterm = tuple_class };
              { bvars = []; bterm = ty_mutable_list }]
         when Opname.eq op opname_TyTuple ->
            let tuple_class = dest_tuple_class tuple_class in
            let ty_mutable_list = List.map (dest_poly_mutable dest_ty) (dest_xlist ty_mutable_list) in
               TyTuple (tuple_class, ty_mutable_list)

         (* TyDTuple *)
       | [], [{ bvars = []; bterm = ty_var };
              { bvars = []; bterm = ty_mutable_list_option }]
         when Opname.eq op opname_TyDTuple ->
            let ty_var = dest_symbol ty_var in
            let ty_mutable_list_option = dest_option (fun t -> List.map (dest_poly_mutable dest_ty) (dest_xlist t)) ty_mutable_list_option in
               TyDTuple (ty_var, ty_mutable_list_option)

         (* TyTag *)
       | [], [{ bvars = []; bterm = ty_var };
              { bvars = []; bterm = ty_mutable_list }]
         when Opname.eq op opname_TyTag ->
            let ty_var = dest_symbol ty_var in
            let ty_mutable_list = List.map (dest_poly_mutable dest_ty) (dest_xlist ty_mutable_list) in
               TyTag (ty_var, ty_mutable_list)

         (* TyArray *)
       | [], [{ bvars = []; bterm = ty }]
         when Opname.eq op opname_TyArray ->
            TyArray (dest_ty ty)

         (* TyPointer *)
       | [], [{ bvars = []; bterm = sub_block }]
         when Opname.eq op opname_TyPointer ->
            TyPointer (dest_sub_block sub_block)

         (* TyFrame *)
       | [], [{ bvars = []; bterm = ty_var };
              { bvars = []; bterm = ty_list }]
         when Opname.eq op opname_TyFrame ->
            let ty_var = dest_symbol ty_var in
            let tyl = List.map dest_ty (dest_xlist ty_list) in
               TyFrame (ty_var, tyl)

         (* TyVar *)
       | [], [{ bvars = []; bterm = ty_var }]
         when Opname.eq op opname_TyVar ->
            TyVar (dest_symbol ty_var)

         (* TyApply *)
       | [], [{ bvars = []; bterm = ty_var };
              { bvars = []; bterm = ty_list }]
         when Opname.eq op opname_TyApply ->
            let ty_var = dest_symbol ty_var in
            let tyl = List.map dest_ty (dest_xlist ty_list) in
               TyApply (ty_var, tyl)

         (* TyExists *)
       | [], [{ bvars = [v]; bterm = ty }]
         when Opname.eq op opname_TyExists ->
            let v = Symbol.add v in
            let ty = dest_ty ty in
               TyExists ([v], ty)

         (* TyAll *)
       | [], [{ bvars = [v]; bterm = ty }]
         when Opname.eq op opname_TyAll ->
            let v = Symbol.add v in
            let ty = dest_ty ty in
               TyAll ([v], ty)

         (* TyProject *)
       | [Number i], [{ bvars = []; bterm = ty_var }]
         when Opname.eq op opname_TyProject ->
            let i = Lm_num.int_of_num i in
            let ty_var = dest_symbol ty_var in
               TyProject (ty_var, i)

       | _ ->
            raise (RefineError ("dest_poly_ty", StringTermError ("not a type", t)))

let make_poly_type make_ty ty =
   match ty with
      TyInt ->
         term_TyInt
    | TyEnum i ->
         let params = [make_param (Number (Lm_num.num_of_int i))] in
         let op = mk_op opname_TyEnum params in
            mk_term op []
    | TyRawInt (p, s) ->
         let params =
            [make_param (Number (num_of_rawint_precision p));
             make_param (Token (string_of_boolean s))]
         in
         let op = mk_op opname_TyRawInt params in
            mk_term op []
    | TyFloat p ->
         let params = [make_param (Number (num_of_rawfloat_precision p))] in
         let op = mk_op opname_TyFloat params in
            mk_term op []
    | TyFun (ty_args, ty_res) ->
         let ty_args = mk_xlist_term (List.map make_ty ty_args) in
         let ty_res = make_ty ty_res in
            mk_simple_term opname_TyFun [ty_args; ty_res]
    | TyUnion (ty_var, ty_list, int_set) ->
         let ty_var = make_symbol ty_var in
         let ty_list = mk_xlist_term (List.map make_ty ty_list) in
         let int_set = make_int_set int_set in
            mk_simple_term opname_TyUnion [ty_var; ty_list; int_set]
    | TyTuple (tuple_class, ty_mutable_list) ->
         let tuple_class = make_tuple_class tuple_class in
         let ty_mutable_list = mk_xlist_term (List.map (make_poly_mutable make_ty) ty_mutable_list) in
            mk_simple_term opname_TyTuple [tuple_class; ty_mutable_list]
    | TyDTuple (ty_var, ty_mutable_list_option) ->
         let ty_var = make_symbol ty_var in
         let ty_mutable_list_option = make_option (fun l -> mk_xlist_term (List.map (make_poly_mutable make_ty) l)) ty_mutable_list_option in
            mk_simple_term opname_TyDTuple [ty_var; ty_mutable_list_option]
    | TyTag (ty_var, ty_mutable_list) ->
         let ty_var = make_symbol ty_var in
         let ty_mutable_list = mk_xlist_term (List.map (make_poly_mutable make_ty) ty_mutable_list) in
            mk_simple_term opname_TyTag [ty_var; ty_mutable_list]
    | TyArray ty ->
         let ty = make_ty ty in
            mk_simple_term opname_TyArray [ty]
    | TyRawData ->
         term_TyRawData
    | TyPointer sub_block ->
         let sub_block = make_sub_block sub_block in
            mk_simple_term opname_TyPointer [sub_block]
    | TyFrame (ty_var, ty_list) ->
         let ty_var = make_symbol ty_var in
         let ty_list = mk_xlist_term (List.map make_ty ty_list) in
            mk_simple_term opname_TyFrame [ty_var; ty_list]
    | TyVar v ->
         let v = make_symbol v in
            mk_simple_term opname_TyVar [v]
    | TyApply (ty_var, ty_list) ->
         let ty_var = make_symbol ty_var in
         let ty_list = mk_xlist_term (List.map make_ty ty_list) in
            mk_simple_term opname_TyApply [ty_var; ty_list]
    | TyExists (vars, ty) ->
         let ty = make_ty ty in
         let op = mk_op opname_TyExists [] in
            List.fold_right (fun v ty ->
                  mk_term op [mk_bterm [Symbol.to_string v] ty]) vars ty
    | TyAll (vars, ty) ->
         let ty = make_ty ty in
         let op = mk_op opname_TyAll [] in
            List.fold_right (fun v ty ->
                  mk_term op [mk_bterm [Symbol.to_string v] ty]) vars ty
    | TyProject (v, i) ->
         let params = [make_param (Number (Lm_num.num_of_int i))] in
         let op = mk_op opname_TyProject params in
         let v = mk_bterm [] (make_symbol v) in
            mk_term op [v]
    | TyDelayed ->
         term_TyDelayed
    | TyCase _
    | TyObject _ ->
         raise (RefineError ("make_ty", StringError "object types not supported"))


(*
 * Generic abstraction for types.
 *)

let term_TyLambda = << TyLambda{v. 'ty['v]} >>
let opname_TyLambda = opname_of_term term_TyLambda

let rec dest_ty_lambda t =
   let { term_op = op; term_terms = bterms } = dest_term t in
   let { op_name = op; op_params = params } = dest_op op in
   let params = dest_params params in
   let bterms = List.map dest_bterm bterms in
      match params, bterms with
         [], [{ bvars = [v]; bterm = t }]
         when Opname.eq op opname_TyLambda ->
            let vars, t = dest_ty_lambda t in
               Symbol.add v :: vars, t
       | _ ->
            [], t

let make_ty_lambda vars ty =
   let op = mk_op opname_TyLambda [] in
      List.fold_right (fun v ty ->
            mk_term op [mk_bterm [Symbol.to_string v] ty]) vars ty

(*
 * A frame has a list of fields, each of which has a list of subfields.
 * The var list is a universal quantifier.
 *
 * The outer symbol table is indexed on the field names.  The list is
 * a list of subfields for that field --- certain fields (e.g. pointers)
 * must be broken into multiple subfields, such as pointers which become
 * a base/offset pair. The subfield tuple is (sf_name, sf_type, sf_size)
 *)
let term_FrameSubfield = << FrameSubfield[size:n]{'v; 'ty} >>
let opname_FrameSubfield = opname_of_term term_FrameSubfield
let term_FrameField = << FrameField{'v; 'subfields} >>
let opname_FrameField = opname_of_term term_FrameField
let term_FrameType = << FrameType{'fields} >>
let opname_FrameType = opname_of_term term_FrameType

let dest_poly_frame dest_ty t =
   let vars, t = dest_ty_lambda t in
      if Opname.eq (opname_of_term t) opname_FrameType then
         let fields = dest_xlist (one_subterm t) in
         let table =
            List.fold_left (fun table field ->
                  if Opname.eq (opname_of_term field) opname_FrameField then
                     let v, subfields = two_subterms field in
                     let v = dest_symbol v in
                     let subfields = dest_xlist subfields in
                     let subfields =
                        List.map (fun subfield ->
                              let { term_op = op; term_terms = bterms } = dest_term subfield in
                              let { op_name = op; op_params = params } = dest_op op in
                              let params = dest_params params in
                              let bterms = List.map dest_bterm bterms in
                                 match params, bterms with
                                    [Number size], [{ bvars = []; bterm = v };
                                                    { bvars = []; bterm = ty }]
                                    when Opname.eq op opname_FrameSubfield ->
                                       let size = Lm_num.int_of_num size in
                                       let v = dest_symbol v in
                                       let ty = dest_ty ty in
                                          size, v, ty

                                  | _ ->
                                       raise (RefineError ("dest_poly_frame", StringTermError ("not a subfield", subfield)))) subfields
                     in
                        SymbolTable.add table v subfields

                  else
                     raise (RefineError ("dest_poly_frame", StringTermError ("not a field", field)))) SymbolTable.empty fields
         in
            vars, table

      else
         raise (RefineError ("dest_poly_frame", StringTermError ("not a frame", t)))

let make_poly_frame make_ty vars table =
   let fields =
      SymbolTable.fold (fun fields v_field subfields ->
            let v_field = make_symbol v_field in
            let subfields =
               List.map (fun (v, ty, i) ->
                     let v = make_symbol v in
                     let ty = make_ty ty in
                     let params = [make_param (Number (Lm_num.num_of_int i))] in
                     let op = mk_op opname_FrameSubfield params in
                        mk_term op [mk_bterm [] v; mk_bterm [] ty]) subfields
            in
            let subfields = mk_xlist_term subfields in
            let field = mk_simple_term opname_FrameField [v_field; subfields] in
               field :: fields) [] table
   in
   let ty = mk_simple_term opname_FrameType [mk_xlist_term fields] in
      make_ty_lambda vars ty

(*
 * Type definitions are the toplevel constructions.
 *)
let term_TyDefUnionList = << TyDefUnionList{'ty_list_list} >>
let opname_TyDefUnionList = opname_of_term term_TyDefUnionList
let term_TyDefUnion = << TyDefUnion{'ty} >>
let opname_TyDefUnion = opname_of_term term_TyDefUnion
let term_TyDefLambda = << TyDefLambda{'ty} >>
let opname_TyDefLambda = opname_of_term term_TyDefLambda
let term_TyDefDTuple = << TyDefDTuple{'ty_var} >>
let opname_TyDefDTuple = opname_of_term term_TyDefDTuple

let dest_tydef dest_ty t =
   let vars, t = dest_ty_lambda t in
   let op = opname_of_term t in
   let ty = one_subterm t in
      if Opname.eq op opname_TyDefUnion then
         let tyll =
            List.map (fun tyl ->
                  if Opname.eq (opname_of_term tyl) opname_TyDefUnionList then
                     List.map (dest_poly_mutable dest_ty) (dest_xlist (one_subterm tyl))
                  else
                     raise (RefineError ("dest_tydef", StringTermError ("not a union list", tyl)))) (dest_xlist ty)
         in
            TyDefUnion (vars, tyll)

      else if Opname.eq op opname_TyDefLambda then
         let ty = dest_ty ty in
            TyDefLambda (vars, ty)

      else if Opname.eq op opname_TyDefDTuple then
         let ty_var = dest_symbol ty in
            TyDefDTuple ty_var

      else
         raise (RefineError ("dest_tydef", StringTermError ("not a tydef", t)))

let make_tydef make_ty tydef =
   match tydef with
      TyDefUnion (vars, tyll) ->
         let tyll =
            List.map (fun tyl ->
                  let tyl = mk_xlist_term (List.map make_ty tyl) in
                     mk_simple_term opname_TyDefUnionList [tyl]) tyll
         in
         let ty = mk_simple_term opname_TyDefUnion [mk_xlist_term tyll] in
            make_ty_lambda vars ty

    | TyDefLambda (vars, ty) ->
         let ty = mk_simple_term opname_TyDefLambda [make_ty ty] in
            make_ty_lambda vars ty

    | TyDefDTuple ty_var ->
         mk_simple_term opname_TyDefDTuple [make_symbol ty_var]

(************************************************************************
 * EXPRESSIONS                                                          *
 ************************************************************************)

(*
 * Unary operators.
 *)
let term_NotEnumOp = << NotEnumOp[i:n] >>
let opname_NotEnumOp = opname_of_term term_NotEnumOp
let term_UMinusIntOp = << UMinusIntOp >>
let opname_UMinusIntOp = opname_of_term term_UMinusIntOp
let term_NotIntOp = << NotIntOp >>
let opname_NotIntOp = opname_of_term term_NotIntOp
let term_AbsIntOp = << AbsIntOp >>
let opname_AbsIntOp = opname_of_term term_AbsIntOp

let term_UMinusRawIntOp = << UMinusRawIntOp[p:n, s:t] >>
let opname_UMinusRawIntOp = opname_of_term term_UMinusRawIntOp
let term_NotRawIntOp = << NotRawIntOp[p:n, s:t] >>
let opname_NotRawIntOp = opname_of_term term_NotRawIntOp
let term_RawBitFieldOp = << RawBitFieldOp[p:n, s:t, off:n, len:n] >>
let opname_RawBitFieldOp = opname_of_term term_RawBitFieldOp

let term_UMinusFloatOp = << UMinusFloatOp[p:n] >>
let opname_UMinusFloatOp = opname_of_term term_UMinusFloatOp
let term_AbsFloatOp = << AbsFloatOp[p:n] >>
let opname_AbsFloatOp = opname_of_term term_AbsFloatOp
let term_SinFloatOp = << SinFloatOp[p:n] >>
let opname_SinFloatOp = opname_of_term term_SinFloatOp
let term_CosFloatOp = << CosFloatOp[p:n] >>
let opname_CosFloatOp = opname_of_term term_CosFloatOp
let term_TanFloatOp = << TanFloatOp[p:n] >>
let opname_TanFloatOp = opname_of_term term_TanFloatOp
let term_ASinFloatOp = << ASinFloatOp[p:n] >>
let opname_ASinFloatOp = opname_of_term term_ASinFloatOp
let term_ACosFloatOp = << ACosFloatOp[p:n] >>
let opname_ACosFloatOp = opname_of_term term_ACosFloatOp
let term_ATanFloatOp = << ATanFloatOp[p:n] >>
let opname_ATanFloatOp = opname_of_term term_ATanFloatOp
let term_SinHFloatOp = << SinHFloatOp[p:n] >>
let opname_SinHFloatOp = opname_of_term term_SinHFloatOp
let term_CosHFloatOp = << CosHFloatOp[p:n] >>
let opname_CosHFloatOp = opname_of_term term_CosHFloatOp
let term_TanHFloatOp = << TanHFloatOp[p:n] >>
let opname_TanHFloatOp = opname_of_term term_TanHFloatOp
let term_ExpFloatOp = << ExpFloatOp[p:n] >>
let opname_ExpFloatOp = opname_of_term term_ExpFloatOp
let term_LogFloatOp = << LogFloatOp[p:n] >>
let opname_LogFloatOp = opname_of_term term_LogFloatOp
let term_Log10FloatOp = << Log10FloatOp[p:n] >>
let opname_Log10FloatOp = opname_of_term term_Log10FloatOp
let term_SqrtFloatOp = << SqrtFloatOp[p:n] >>
let opname_SqrtFloatOp = opname_of_term term_SqrtFloatOp
let term_CeilFloatOp = << CeilFloatOp[p:n] >>
let opname_CeilFloatOp = opname_of_term term_CeilFloatOp
let term_FloorFloatOp = << FloorFloatOp[p:n] >>
let opname_FloorFloatOp = opname_of_term term_FloorFloatOp

let term_IntOfFloatOp = << IntOfFloatOp[p:n] >>
let opname_IntOfFloatOp = opname_of_term term_IntOfFloatOp
let term_IntOfRawIntOp = << IntOfRawIntOp[p:n, s:t] >>
let opname_IntOfRawIntOp = opname_of_term term_IntOfRawIntOp
let term_FloatOfIntOp = << FloatOfIntOp[p:n] >>
let opname_FloatOfIntOp = opname_of_term term_FloatOfIntOp
let term_FloatOfFloatOp = << FloatOfFloatOp[p1:n, p2:n] >>
let opname_FloatOfFloatOp = opname_of_term term_FloatOfFloatOp
let term_FloatOfRawIntOp = << FloatOfRawIntOp[fp:n, ip:n, s:t] >>
let opname_FloatOfRawIntOp = opname_of_term term_FloatOfRawIntOp
let term_RawIntOfIntOp = << RawIntOfIntOp[p:n, s:t] >>
let opname_RawIntOfIntOp = opname_of_term term_RawIntOfIntOp
let term_RawIntOfEnumOp = << RawIntOfEnumOp[p:n, s:t, i:n] >>
let opname_RawIntOfEnumOp = opname_of_term term_RawIntOfEnumOp
let term_RawIntOfFloatOp = << RawIntOfFloatOp[ip:n, s:t, fp:n] >>
let opname_RawIntOfFloatOp = opname_of_term term_RawIntOfFloatOp
let term_RawIntOfRawIntOp = << RawIntOfRawIntOp[p1:n, s1:t, p2:n, s2:t] >>
let opname_RawIntOfRawIntOp = opname_of_term term_RawIntOfRawIntOp
let term_RawIntOfPointerOp = << RawIntOfPointerOp[p:n, s:t] >>
let opname_RawIntOfPointerOp = opname_of_term term_RawIntOfPointerOp
let term_PointerOfRawIntOp = << PointerOfRawIntOp[p:n, s:t] >>
let opname_PointerOfRawIntOp = opname_of_term term_PointerOfRawIntOp
let term_PointerOfBlockOp = << PointerOfBlockOp{'sub_block} >>
let opname_PointerOfBlockOp = opname_of_term term_PointerOfBlockOp
let term_LengthOfBlockOp = << LengthOfBlockOp{'subop; 'ty} >>
let opname_LengthOfBlockOp = opname_of_term term_LengthOfBlockOp
let term_DTupleOfDTupleOp = << DTupleOfDTupleOp{'ty_var; 'mutable_ty_list} >>
let opname_DTupleOfDTupleOp = opname_of_term term_DTupleOfDTupleOp
let term_UnionOfUnionOp = << UnionOfUnionOp{'ty_var; 'ty_list; 'int_set1; 'int_set2} >>
let opname_UnionOfUnionOp = opname_of_term term_UnionOfUnionOp
let term_RawDataOfFrameOp = << RawDataOfFrameOp{'ty_var; 'ty_list} >>
let opname_RawDataOfFrameOp = opname_of_term term_RawDataOfFrameOp

let dest_unop dest_ty t =
   let { term_op = op; term_terms = bterms } = dest_term t in
   let { op_name = op; op_params = params } = dest_op op in
   let params = dest_params params in
   let bterms = List.map dest_bterm bterms in
      match params, bterms with
         [], [] ->
            if Opname.eq op opname_UMinusIntOp then
               UMinusIntOp
            else if Opname.eq op opname_NotIntOp then
               NotIntOp
            else if Opname.eq op opname_AbsIntOp then
               AbsIntOp
            else
               raise (RefineError ("dest_unop", StringTermError ("not a unop", t)))

       | [Number i], [] ->
            if Opname.eq op opname_NotEnumOp then
               NotEnumOp (Lm_num.int_of_num i)
            else if Opname.eq op opname_UMinusFloatOp then
               UMinusFloatOp (rawfloat_precision_of_num i)
            else if Opname.eq op opname_AbsFloatOp then
               AbsFloatOp (rawfloat_precision_of_num i)
            else if Opname.eq op opname_SinFloatOp then
               SinFloatOp (rawfloat_precision_of_num i)
            else if Opname.eq op opname_CosFloatOp then
               CosFloatOp (rawfloat_precision_of_num i)
            else if Opname.eq op opname_TanFloatOp then
               TanFloatOp (rawfloat_precision_of_num i)
            else if Opname.eq op opname_ASinFloatOp then
               ASinFloatOp (rawfloat_precision_of_num i)
            else if Opname.eq op opname_ACosFloatOp then
               ACosFloatOp (rawfloat_precision_of_num i)
            else if Opname.eq op opname_ATanFloatOp then
               ATanFloatOp (rawfloat_precision_of_num i)
            else if Opname.eq op opname_SinHFloatOp then
               SinHFloatOp (rawfloat_precision_of_num i)
            else if Opname.eq op opname_CosHFloatOp then
               CosHFloatOp (rawfloat_precision_of_num i)
            else if Opname.eq op opname_TanHFloatOp then
               TanHFloatOp (rawfloat_precision_of_num i)
            else if Opname.eq op opname_ExpFloatOp then
               ExpFloatOp (rawfloat_precision_of_num i)
            else if Opname.eq op opname_LogFloatOp then
               LogFloatOp (rawfloat_precision_of_num i)
            else if Opname.eq op opname_Log10FloatOp then
               Log10FloatOp (rawfloat_precision_of_num i)
            else if Opname.eq op opname_SqrtFloatOp then
               SqrtFloatOp (rawfloat_precision_of_num i)
            else if Opname.eq op opname_CeilFloatOp then
               CeilFloatOp (rawfloat_precision_of_num i)
            else if Opname.eq op opname_FloorFloatOp then
               FloorFloatOp (rawfloat_precision_of_num i)
            else if Opname.eq op opname_IntOfFloatOp then
               IntOfFloatOp (rawfloat_precision_of_num i)
            else if Opname.eq op opname_FloatOfIntOp then
               FloatOfIntOp (rawfloat_precision_of_num i)
            else
               raise (RefineError ("dest_unop", StringTermError ("not a unop", t)))

       | [Number p; Token s], [] ->
            let p = rawint_precision_of_num p in
            let s = boolean_of_string s in
               if Opname.eq op opname_UMinusRawIntOp then
                  UMinusRawIntOp (p, s)
               else if Opname.eq op opname_NotRawIntOp then
                  NotRawIntOp (p, s)
               else if Opname.eq op opname_IntOfRawIntOp then
                  IntOfRawIntOp (p, s)
               else if Opname.eq op opname_RawIntOfIntOp then
                  RawIntOfIntOp (p, s)
               else if Opname.eq op opname_RawIntOfPointerOp then
                  RawIntOfPointerOp (p, s)
               else if Opname.eq op opname_PointerOfRawIntOp then
                  PointerOfRawIntOp (p, s)
               else
                  raise (RefineError ("dest_unop", StringTermError ("not a unop", t)))

       | [Number p; Token s; Number off; Number len], []
         when Opname.eq op opname_RawBitFieldOp ->
            let p = rawint_precision_of_num p in
            let s = boolean_of_string s in
            let off = Lm_num.int_of_num off in
            let len = Lm_num.int_of_num len in
               RawBitFieldOp (p, s, off, len)

       | [Number p1; Number p2], []
         when Opname.eq op opname_FloatOfFloatOp ->
            let p1 = rawfloat_precision_of_num p1 in
            let p2 = rawfloat_precision_of_num p2 in
               FloatOfFloatOp (p1, p2)

       | [Number fp; Number ip; Token s], []
         when Opname.eq op opname_FloatOfRawIntOp ->
            let fp = rawfloat_precision_of_num fp in
            let ip = rawint_precision_of_num ip in
            let s = boolean_of_string s in
               FloatOfRawIntOp (fp, ip, s)

       | [Number p; Token s; Number i], [] ->
            if Opname.eq op opname_RawIntOfFloatOp then
               let fp = rawfloat_precision_of_num i in
               let ip = rawint_precision_of_num p in
               let s = boolean_of_string s in
                  RawIntOfFloatOp (ip, s, fp)
            else if Opname.eq op opname_RawIntOfEnumOp then
               let p = rawint_precision_of_num p in
               let s = boolean_of_string s in
               let i = Lm_num.int_of_num i in
                  RawIntOfEnumOp (p, s, i)
            else
               raise (RefineError ("dest_unop", StringTermError ("not a unop", t)))

       | [Number p1; Token s1; Number p2; Token s2], []
         when Opname.eq op opname_RawIntOfRawIntOp ->
            let p1 = rawint_precision_of_num p1 in
            let s1 = boolean_of_string s1 in
            let p2 = rawint_precision_of_num p2 in
            let s2 = boolean_of_string s2 in
               RawIntOfRawIntOp (p1, s1, p2, s2)

       | [], [{ bvars = []; bterm = sub_block }]
         when Opname.eq op opname_PointerOfBlockOp ->
            let sub_block = dest_sub_block sub_block in
               PointerOfBlockOp sub_block

       | [], [{ bvars = []; bterm = subop };
              { bvars = []; bterm = ty }]
         when Opname.eq op opname_LengthOfBlockOp ->
            let subop = dest_poly_subop dest_ty subop in
            let ty = dest_ty ty in
               LengthOfBlockOp (subop, ty)

       | [], [{ bvars = []; bterm = ty_var };
              { bvars = []; bterm = ty_mutable_list }]
         when Opname.eq op opname_DTupleOfDTupleOp ->
            let ty_var = dest_symbol ty_var in
            let ty_mutable_list = List.map (dest_poly_mutable dest_ty) (dest_xlist ty_mutable_list) in
               DTupleOfDTupleOp (ty_var, ty_mutable_list)

       | [], [{ bvars = []; bterm = ty_var };
              { bvars = []; bterm = ty_list };
              { bvars = []; bterm = int_set1 };
              { bvars = []; bterm = int_set2 }]
         when Opname.eq op opname_UnionOfUnionOp ->
            let ty_var = dest_symbol ty_var in
            let ty_list = List.map dest_ty (dest_xlist ty_list) in
            let int_set1 = dest_int_set int_set1 in
            let int_set2 = dest_int_set int_set2 in
               UnionOfUnionOp (ty_var, ty_list, int_set1, int_set2)

       | [], [{ bvars = []; bterm = ty_var };
              { bvars = []; bterm = ty_list }]
         when Opname.eq op opname_RawDataOfFrameOp ->
            let ty_var = dest_symbol ty_var in
            let ty_list = List.map dest_ty (dest_xlist ty_list) in
               RawDataOfFrameOp (ty_var, ty_list)

       | _ ->
            raise (RefineError ("dest_unop", StringTermError ("not a unop", t)))

let make_unop make_ty op =
   match op with
      NotEnumOp i ->
         let params = [make_param (Number (Lm_num.num_of_int i))] in
         let op = mk_op opname_NotEnumOp params in
            mk_term op []
    | UMinusIntOp ->
         term_UMinusIntOp
    | NotIntOp ->
         term_NotIntOp
    | AbsIntOp ->
         term_AbsIntOp
    | UMinusRawIntOp (p, s) ->
         make_rawint_term opname_UMinusRawIntOp p s
    | NotRawIntOp (p, s) ->
         make_rawint_term opname_NotRawIntOp p s
    | RawBitFieldOp (p, s, off, len) ->
         let params =
            [make_param (Number (num_of_rawint_precision p));
             make_param (Token (string_of_boolean s));
             make_param (Number (Lm_num.num_of_int off));
             make_param (Number (Lm_num.num_of_int len))]
         in
         let op = mk_op opname_RawBitFieldOp params in
            mk_term op []
    | UMinusFloatOp p ->
         make_rawfloat_term opname_UMinusFloatOp p
    | AbsFloatOp p ->
         make_rawfloat_term opname_AbsFloatOp p
    | SinFloatOp p ->
         make_rawfloat_term opname_SinFloatOp p
    | CosFloatOp p ->
         make_rawfloat_term opname_CosFloatOp p
    | TanFloatOp p ->
         make_rawfloat_term opname_TanFloatOp p
    | ASinFloatOp p ->
         make_rawfloat_term opname_ASinFloatOp p
    | ACosFloatOp p ->
         make_rawfloat_term opname_ACosFloatOp p
    | ATanFloatOp p ->
         make_rawfloat_term opname_ATanFloatOp p
    | SinHFloatOp p ->
         make_rawfloat_term opname_SinHFloatOp p
    | CosHFloatOp p ->
         make_rawfloat_term opname_CosHFloatOp p
    | TanHFloatOp p ->
         make_rawfloat_term opname_TanHFloatOp p
    | ExpFloatOp p ->
         make_rawfloat_term opname_ExpFloatOp p
    | LogFloatOp p ->
         make_rawfloat_term opname_LogFloatOp p
    | Log10FloatOp p ->
         make_rawfloat_term opname_Log10FloatOp p
    | SqrtFloatOp p ->
         make_rawfloat_term opname_SqrtFloatOp p
    | CeilFloatOp p ->
         make_rawfloat_term opname_CeilFloatOp p
    | FloorFloatOp p ->
         make_rawfloat_term opname_FloorFloatOp p
    | FloatOfIntOp p ->
         make_rawfloat_term opname_FloatOfIntOp p
    | IntOfFloatOp p ->
         make_rawfloat_term opname_IntOfFloatOp p
    | IntOfRawIntOp (p, s) ->
         make_rawint_term opname_IntOfRawIntOp p s
    | FloatOfFloatOp (p1, p2) ->
         let params =
            [make_param (Number (num_of_rawfloat_precision p1));
             make_param (Number (num_of_rawfloat_precision p2))]
         in
         let op = mk_op opname_FloatOfFloatOp params in
            mk_term op []
    | FloatOfRawIntOp (fp, ip, s) ->
         let params =
            [make_param (Number (num_of_rawfloat_precision fp));
             make_param (Number (num_of_rawint_precision ip));
             make_param (Token (string_of_boolean s))]
         in
         let op = mk_op opname_FloatOfRawIntOp params in
            mk_term op []
    | RawIntOfIntOp (p, s) ->
         make_rawint_term opname_RawIntOfIntOp p s
    | RawIntOfEnumOp (p, s, n) ->
         let params =
            [make_param (Number (num_of_rawint_precision p));
             make_param (Token (string_of_boolean s));
             make_param (Number (Lm_num.num_of_int n))]
         in
         let op = mk_op opname_RawIntOfEnumOp params in
            mk_term op []
    | RawIntOfFloatOp (ip, s, fp) ->
         let params =
            [make_param (Number (num_of_rawint_precision ip));
             make_param (Token (string_of_boolean s));
             make_param (Number (num_of_rawfloat_precision fp))]
         in
         let op = mk_op opname_RawIntOfFloatOp params in
            mk_term op []
    | RawIntOfRawIntOp (p1, s1, p2, s2) ->
         let params =
            [make_param (Number (num_of_rawint_precision p1));
             make_param (Token (string_of_boolean s1));
             make_param (Number (num_of_rawint_precision p2));
             make_param (Token (string_of_boolean s2))]
         in
         let op = mk_op opname_RawIntOfRawIntOp params in
            mk_term op []
    | RawIntOfPointerOp (p, s) ->
         make_rawint_term opname_RawIntOfPointerOp p s
    | PointerOfRawIntOp (p, s) ->
         make_rawint_term opname_PointerOfRawIntOp p s
    | PointerOfBlockOp sub_block ->
         mk_simple_term opname_PointerOfBlockOp [make_sub_block sub_block]
    | LengthOfBlockOp (subop, ty) ->
         let subop = make_poly_subop make_ty subop in
         let ty = make_ty ty in
            mk_simple_term opname_LengthOfBlockOp [subop; ty]
    | DTupleOfDTupleOp (ty_var, ty_mutable_list) ->
         let ty_var = make_symbol ty_var in
         let ty_mutable_list = mk_xlist_term (List.map (make_poly_mutable make_ty) ty_mutable_list) in
            mk_simple_term opname_DTupleOfDTupleOp [ty_var; ty_mutable_list]
    | UnionOfUnionOp (ty_var, ty_list, int_set1, int_set2) ->
         let ty_var = make_symbol ty_var in
         let ty_list = mk_xlist_term (List.map make_ty ty_list) in
         let int_set1 = make_int_set int_set1 in
         let int_set2 = make_int_set int_set2 in
            mk_simple_term opname_UnionOfUnionOp [ty_var; ty_list; int_set1; int_set2]
    | RawDataOfFrameOp (ty_var, ty_list) ->
         let ty_var = make_symbol ty_var in
         let ty_list = mk_xlist_term (List.map make_ty ty_list) in
            mk_simple_term opname_RawDataOfFrameOp [ty_var; ty_list]



(*
 * Binary operators.
 *)
let term_AndEnumOp = << AndEnumOp[i:n] >>
let opname_AndEnumOp = opname_of_term term_AndEnumOp
let term_OrEnumOp = << OrEnumOp[i:n] >>
let opname_OrEnumOp = opname_of_term term_OrEnumOp
let term_XorEnumOp = << XorEnumOp[i:n] >>
let opname_XorEnumOp = opname_of_term term_XorEnumOp

(* Standard binary operations on NAML ints *)
let term_PlusIntOp = << PlusIntOp >>
let opname_PlusIntOp = opname_of_term term_PlusIntOp
let term_MinusIntOp = << MinusIntOp >>
let opname_MinusIntOp = opname_of_term term_MinusIntOp
let term_MulIntOp = << MulIntOp >>
let opname_MulIntOp = opname_of_term term_MulIntOp
let term_DivIntOp = << DivIntOp >>
let opname_DivIntOp = opname_of_term term_DivIntOp
let term_RemIntOp = << RemIntOp >>
let opname_RemIntOp = opname_of_term term_RemIntOp
let term_LslIntOp = << LslIntOp >>
let opname_LslIntOp = opname_of_term term_LslIntOp
let term_LsrIntOp = << LsrIntOp >>
let opname_LsrIntOp = opname_of_term term_LsrIntOp
let term_AsrIntOp = << AsrIntOp >>
let opname_AsrIntOp = opname_of_term term_AsrIntOp
let term_AndIntOp = << AndIntOp >>
let opname_AndIntOp = opname_of_term term_AndIntOp
let term_OrIntOp = << OrIntOp >>
let opname_OrIntOp = opname_of_term term_OrIntOp
let term_XorIntOp = << XorIntOp >>
let opname_XorIntOp = opname_of_term term_XorIntOp
let term_MaxIntOp = << MaxIntOp >>
let opname_MaxIntOp = opname_of_term term_MaxIntOp
let term_MinIntOp = << MinIntOp >>
let opname_MinIntOp = opname_of_term term_MinIntOp

(*
 * Equality and comparison.
 *)
let term_EqIntOp = << EqIntOp >>
let opname_EqIntOp = opname_of_term term_EqIntOp
let term_NeqIntOp = << NeqIntOp >>
let opname_NeqIntOp = opname_of_term term_NeqIntOp
let term_LtIntOp = << LtIntOp >>
let opname_LtIntOp = opname_of_term term_LtIntOp
let term_LeIntOp = << LeIntOp >>
let opname_LeIntOp = opname_of_term term_LeIntOp
let term_GtIntOp = << GtIntOp >>
let opname_GtIntOp = opname_of_term term_GtIntOp
let term_GeIntOp = << GeIntOp >>
let opname_GeIntOp = opname_of_term term_GeIntOp
let term_CmpIntOp = << CmpIntOp >>
let opname_CmpIntOp = opname_of_term term_CmpIntOp

(*
 * Standard binary operations on native ints.  The precision is
 * the result precision; the inputs should match this precision.
 *)
let term_PlusRawIntOp = << PlusRawIntOp[p:n, s:t] >>
let opname_PlusRawIntOp = opname_of_term term_PlusRawIntOp
let term_MinusRawIntOp = << MinusRawIntOp[p:n, s:t] >>
let opname_MinusRawIntOp = opname_of_term term_MinusRawIntOp
let term_MulRawIntOp = << MulRawIntOp[p:n, s:t] >>
let opname_MulRawIntOp = opname_of_term term_MulRawIntOp
let term_DivRawIntOp = << DivRawIntOp[p:n, s:t] >>
let opname_DivRawIntOp = opname_of_term term_DivRawIntOp
let term_RemRawIntOp = << RemRawIntOp[p:n, s:t] >>
let opname_RemRawIntOp = opname_of_term term_RemRawIntOp
let term_SlRawIntOp = << SlRawIntOp[p:n, s:t] >>
let opname_SlRawIntOp = opname_of_term term_SlRawIntOp
let term_SrRawIntOp = << SrRawIntOp[p:n, s:t] >>
let opname_SrRawIntOp = opname_of_term term_SrRawIntOp
let term_AndRawIntOp = << AndRawIntOp[p:n, s:t] >>
let opname_AndRawIntOp = opname_of_term term_AndRawIntOp
let term_OrRawIntOp = << OrRawIntOp[p:n, s:t] >>
let opname_OrRawIntOp = opname_of_term term_OrRawIntOp
let term_XorRawIntOp = << XorRawIntOp[p:n, s:t] >>
let opname_XorRawIntOp = opname_of_term term_XorRawIntOp
let term_MaxRawIntOp = << MaxRawIntOp[p:n, s:t] >>
let opname_MaxRawIntOp = opname_of_term term_MaxRawIntOp
let term_MinRawIntOp = << MinRawIntOp[p:n, s:t] >>
let opname_MinRawIntOp = opname_of_term term_MinRawIntOp

(*
 * RawSetBitFieldOp (pre, signed, offset, length)
 *    See comments for RawBitFieldOp. This modifies the bitfield starting
 *    at bit <offset> and extending <length> bits.  There are two atoms:
 *       First atom is the integer containing the field.
 *       Second atom is the value to be set in the field.
 *    The resulting integer contains the revised field, with type
 *    ACRawInt (pre, signed)
 *)
let term_RawSetBitFieldOp = << RawSetBitFieldOp[p:n, s:t, off:n, len:n] >>
let opname_RawSetBitFieldOp = opname_of_term term_RawSetBitFieldOp

(* Comparisons on native ints *)
let term_EqRawIntOp = << EqRawIntOp[p:n, s:t] >>
let opname_EqRawIntOp = opname_of_term term_EqRawIntOp
let term_NeqRawIntOp = << NeqRawIntOp[p:n, s:t] >>
let opname_NeqRawIntOp = opname_of_term term_NeqRawIntOp
let term_LtRawIntOp = << LtRawIntOp[p:n, s:t] >>
let opname_LtRawIntOp = opname_of_term term_LtRawIntOp
let term_LeRawIntOp = << LeRawIntOp[p:n, s:t] >>
let opname_LeRawIntOp = opname_of_term term_LeRawIntOp
let term_GtRawIntOp = << GtRawIntOp[p:n, s:t] >>
let opname_GtRawIntOp = opname_of_term term_GtRawIntOp
let term_GeRawIntOp = << GeRawIntOp[p:n, s:t] >>
let opname_GeRawIntOp = opname_of_term term_GeRawIntOp
let term_CmpRawIntOp = << CmpRawIntOp[p:n, s:t] >>
let opname_CmpRawIntOp = opname_of_term term_CmpRawIntOp

(* Standard binary operations on floats *)
let term_PlusFloatOp = << PlusFloatOp[p:n] >>
let opname_PlusFloatOp = opname_of_term term_PlusFloatOp
let term_MinusFloatOp = << MinusFloatOp[p:n] >>
let opname_MinusFloatOp = opname_of_term term_MinusFloatOp
let term_MulFloatOp = << MulFloatOp[p:n] >>
let opname_MulFloatOp = opname_of_term term_MulFloatOp
let term_DivFloatOp = << DivFloatOp[p:n] >>
let opname_DivFloatOp = opname_of_term term_DivFloatOp
let term_RemFloatOp = << RemFloatOp[p:n] >>
let opname_RemFloatOp = opname_of_term term_RemFloatOp
let term_MaxFloatOp = << MaxFloatOp[p:n] >>
let opname_MaxFloatOp = opname_of_term term_MaxFloatOp
let term_MinFloatOp = << MinFloatOp[p:n] >>
let opname_MinFloatOp = opname_of_term term_MinFloatOp

(* Comparisons on floats *)
let term_EqFloatOp = << EqFloatOp[p:n] >>
let opname_EqFloatOp = opname_of_term term_EqFloatOp
let term_NeqFloatOp = << NeqFloatOp[p:n] >>
let opname_NeqFloatOp = opname_of_term term_NeqFloatOp
let term_LtFloatOp = << LtFloatOp[p:n] >>
let opname_LtFloatOp = opname_of_term term_LtFloatOp
let term_LeFloatOp = << LeFloatOp[p:n] >>
let opname_LeFloatOp = opname_of_term term_LeFloatOp
let term_GtFloatOp = << GtFloatOp[p:n] >>
let opname_GtFloatOp = opname_of_term term_GtFloatOp
let term_GeFloatOp = << GeFloatOp[p:n] >>
let opname_GeFloatOp = opname_of_term term_GeFloatOp
let term_CmpFloatOp = << CmpFloatOp[p:n] >>
let opname_CmpFloatOp = opname_of_term term_CmpFloatOp

(*
 * Arctangent.  This computes arctan(y/x), where y is the first atom
 * and x is the second atom given.  Handles case when x = 0 correctly.
 *)
let term_ATan2FloatOp = << ATan2FloatOp[p:n] >>
let opname_ATan2FloatOp = opname_of_term term_ATan2FloatOp

(*
 * Power.  This computes x^y.
 *)
let term_PowerFloatOp = << PowerFloatOp[p:n] >>
let opname_PowerFloatOp = opname_of_term term_PowerFloatOp

(*
 * Float hacking.
 * This sets the exponent field of the float.
 *)
let term_LdExpFloatIntOp = << LdExpFloatIntOp[p:n] >>
let opname_LdExpFloatIntOp = opname_of_term term_LdExpFloatIntOp

(* Pointer (in)equality.  Arguments must have the given type *)
let term_EqEqOp = << EqEqOp{'ty} >>
let opname_EqEqOp = opname_of_term term_EqEqOp
let term_NeqEqOp = << NeqEqOp{'ty} >>
let opname_NeqEqOp = opname_of_term term_NeqEqOp

(*
 * Pointer arithmetic. The pointer in the first argument, and the
 * returned pointer should be infix pointers (which keep the base
 * pointer as well as a pointer to anywhere within the block).
 *)
let term_PlusPointerOp = << PlusPointerOp[p:n, s:t]{'sub_block} >>
let opname_PlusPointerOp = opname_of_term term_PlusPointerOp

let dest_binop dest_ty t =
   let { term_op = op; term_terms = bterms } = dest_term t in
   let { op_name = op; op_params = params } = dest_op op in
   let params = dest_params params in
   let bterms = List.map dest_bterm bterms in
      match params, bterms with
         [], [] ->
            if Opname.eq op opname_PlusIntOp then
               PlusIntOp
            else if Opname.eq op opname_MinusIntOp then
               MinusIntOp
            else if Opname.eq op opname_MulIntOp then
               MulIntOp
            else if Opname.eq op opname_DivIntOp then
               DivIntOp
            else if Opname.eq op opname_RemIntOp then
               RemIntOp
            else if Opname.eq op opname_LslIntOp then
               LslIntOp
            else if Opname.eq op opname_LsrIntOp then
               LsrIntOp
            else if Opname.eq op opname_AsrIntOp then
               AsrIntOp
            else if Opname.eq op opname_AndIntOp then
               AndIntOp
            else if Opname.eq op opname_OrIntOp then
               OrIntOp
            else if Opname.eq op opname_XorIntOp then
               XorIntOp
            else if Opname.eq op opname_MaxIntOp then
               MaxIntOp
            else if Opname.eq op opname_MinIntOp then
               MinIntOp
            else if Opname.eq op opname_EqIntOp then
               EqIntOp
            else if Opname.eq op opname_NeqIntOp then
               NeqIntOp
            else if Opname.eq op opname_LtIntOp then
               LtIntOp
            else if Opname.eq op opname_LeIntOp then
               LeIntOp
            else if Opname.eq op opname_GtIntOp then
               GtIntOp
            else if Opname.eq op opname_GeIntOp then
               GeIntOp
            else if Opname.eq op opname_CmpIntOp then
               CmpIntOp
            else
               raise (RefineError ("dest_binop", StringTermError ("not a binop", t)))

       | [Number n], [] ->
            if Opname.eq op opname_AndEnumOp then
               AndEnumOp (Lm_num.int_of_num n)
            else if Opname.eq op opname_OrEnumOp then
               OrEnumOp (Lm_num.int_of_num n)
            else if Opname.eq op opname_XorEnumOp then
               XorEnumOp (Lm_num.int_of_num n)
            else if Opname.eq op opname_PlusFloatOp then
               PlusFloatOp (rawfloat_precision_of_num n)
            else if Opname.eq op opname_MinusFloatOp then
               MinusFloatOp (rawfloat_precision_of_num n)
            else if Opname.eq op opname_MulFloatOp then
               MulFloatOp (rawfloat_precision_of_num n)
            else if Opname.eq op opname_DivFloatOp then
               DivFloatOp (rawfloat_precision_of_num n)
            else if Opname.eq op opname_RemFloatOp then
               RemFloatOp (rawfloat_precision_of_num n)
            else if Opname.eq op opname_MaxFloatOp then
               MaxFloatOp (rawfloat_precision_of_num n)
            else if Opname.eq op opname_MinFloatOp then
               MinFloatOp (rawfloat_precision_of_num n)
            else if Opname.eq op opname_EqFloatOp then
               EqFloatOp (rawfloat_precision_of_num n)
            else if Opname.eq op opname_NeqFloatOp then
               NeqFloatOp (rawfloat_precision_of_num n)
            else if Opname.eq op opname_LtFloatOp then
               LtFloatOp (rawfloat_precision_of_num n)
            else if Opname.eq op opname_LeFloatOp then
               LeFloatOp (rawfloat_precision_of_num n)
            else if Opname.eq op opname_GtFloatOp then
               GtFloatOp (rawfloat_precision_of_num n)
            else if Opname.eq op opname_GeFloatOp then
               GeFloatOp (rawfloat_precision_of_num n)
            else if Opname.eq op opname_CmpFloatOp then
               CmpFloatOp (rawfloat_precision_of_num n)
            else if Opname.eq op opname_ATan2FloatOp then
               ATan2FloatOp (rawfloat_precision_of_num n)
            else if Opname.eq op opname_PowerFloatOp then
               PowerFloatOp (rawfloat_precision_of_num n)
            else if Opname.eq op opname_LdExpFloatIntOp then
               LdExpFloatIntOp (rawfloat_precision_of_num n)
            else
               raise (RefineError ("dest_binop", StringTermError ("not a binop", t)))

       | [Number p; Token s], [] ->
            let p = rawint_precision_of_num p in
            let s = boolean_of_string s in
               if Opname.eq op opname_PlusRawIntOp then
                  PlusRawIntOp (p, s)
               else if Opname.eq op opname_MinusRawIntOp then
                  MinusRawIntOp (p, s)
               else if Opname.eq op opname_MulRawIntOp then
                  MulRawIntOp (p, s)
               else if Opname.eq op opname_DivRawIntOp then
                  DivRawIntOp (p, s)
               else if Opname.eq op opname_RemRawIntOp then
                  RemRawIntOp (p, s)
               else if Opname.eq op opname_SlRawIntOp then
                  SlRawIntOp (p, s)
               else if Opname.eq op opname_SrRawIntOp then
                  SrRawIntOp (p, s)
               else if Opname.eq op opname_AndRawIntOp then
                  AndRawIntOp (p, s)
               else if Opname.eq op opname_OrRawIntOp then
                  OrRawIntOp (p, s)
               else if Opname.eq op opname_XorRawIntOp then
                  XorRawIntOp (p, s)
               else if Opname.eq op opname_MaxRawIntOp then
                  MinRawIntOp (p, s)
               else if Opname.eq op opname_EqRawIntOp then
                  EqRawIntOp (p, s)
               else if Opname.eq op opname_NeqRawIntOp then
                  NeqRawIntOp (p, s)
               else if Opname.eq op opname_LtRawIntOp then
                  LtRawIntOp (p, s)
               else if Opname.eq op opname_LeRawIntOp then
                  LeRawIntOp (p, s)
               else if Opname.eq op opname_GtRawIntOp then
                  GtRawIntOp (p, s)
               else if Opname.eq op opname_GeRawIntOp then
                  GeRawIntOp (p, s)
               else if Opname.eq op opname_CmpRawIntOp then
                  CmpRawIntOp (p, s)
               else
                  raise (RefineError ("dest_binop", StringTermError ("not a binop", t)))

       | [Number p; Token s; Number off; Number len], []
         when Opname.eq op opname_RawSetBitFieldOp ->
            let p = rawint_precision_of_num p in
            let s = boolean_of_string s in
            let off = Lm_num.int_of_num off in
            let len = Lm_num.int_of_num len in
               RawSetBitFieldOp (p, s, off, len)

       | [], [{ bvars = []; bterm = ty }] ->
            if Opname.eq op opname_EqEqOp then
               EqEqOp (dest_ty ty)
            else if Opname.eq op opname_NeqEqOp then
               NeqEqOp (dest_ty ty)
            else
               raise (RefineError ("dest_binop", StringTermError ("not a binop", t)))

       | [Number p; String s], [{ bvars = []; bterm = sub_block }]
         when Opname.eq op opname_PlusPointerOp ->
            let p = rawint_precision_of_num p in
            let s = boolean_of_string s in
            let sub_block = dest_sub_block sub_block in
               PlusPointerOp (sub_block, p, s)

       | _ ->
            raise (RefineError ("dest_binop", StringTermError ("not a binop", t)))

let make_binop make_ty op =
   match op with
      AndEnumOp i ->
         let params = [make_param (Number (Lm_num.num_of_int i))] in
         let op = mk_op opname_AndEnumOp params in
            mk_term op []
    | OrEnumOp i ->
         let params = [make_param (Number (Lm_num.num_of_int i))] in
         let op = mk_op opname_OrEnumOp params in
            mk_term op []
    | XorEnumOp i ->
         let params = [make_param (Number (Lm_num.num_of_int i))] in
         let op = mk_op opname_XorEnumOp params in
            mk_term op []
    | PlusIntOp ->
         term_PlusIntOp
    | MinusIntOp ->
         term_MinusIntOp
    | MulIntOp ->
         term_MulIntOp
    | DivIntOp ->
         term_DivIntOp
    | RemIntOp ->
         term_RemIntOp
    | LslIntOp ->
         term_LslIntOp
    | LsrIntOp ->
         term_LsrIntOp
    | AsrIntOp ->
         term_AsrIntOp
    | AndIntOp ->
         term_AndIntOp
    | OrIntOp ->
         term_OrIntOp
    | XorIntOp ->
         term_XorIntOp
    | MaxIntOp ->
         term_MaxIntOp
    | MinIntOp ->
         term_MinIntOp
    | EqIntOp ->
         term_EqIntOp
    | NeqIntOp ->
         term_NeqIntOp
    | LtIntOp ->
         term_LtIntOp
    | LeIntOp ->
         term_LeIntOp
    | GtIntOp ->
         term_GtIntOp
    | GeIntOp ->
         term_GeIntOp
    | CmpIntOp ->
         term_CmpIntOp
    | PlusRawIntOp (p, s) ->
         make_rawint_term opname_PlusRawIntOp p s
    | MinusRawIntOp (p, s) ->
         make_rawint_term opname_MinusRawIntOp p s
    | MulRawIntOp (p, s) ->
         make_rawint_term opname_MulRawIntOp p s
    | DivRawIntOp (p, s) ->
         make_rawint_term opname_DivRawIntOp p s
    | RemRawIntOp (p, s) ->
         make_rawint_term opname_RemRawIntOp p s
    | SlRawIntOp (p, s) ->
         make_rawint_term opname_SlRawIntOp p s
    | SrRawIntOp (p, s) ->
         make_rawint_term opname_SrRawIntOp p s
    | AndRawIntOp (p, s) ->
         make_rawint_term opname_AndRawIntOp p s
    | OrRawIntOp (p, s) ->
         make_rawint_term opname_OrRawIntOp p s
    | XorRawIntOp (p, s) ->
         make_rawint_term opname_XorRawIntOp p s
    | MaxRawIntOp (p, s) ->
         make_rawint_term opname_MaxRawIntOp p s
    | MinRawIntOp (p, s) ->
         make_rawint_term opname_MinRawIntOp p s
    | RawSetBitFieldOp (p, s, off, len) ->
         let params =
            [make_param (Number (num_of_rawint_precision p));
             make_param (Token (string_of_boolean s));
             make_param (Number (Lm_num.num_of_int off));
             make_param (Number (Lm_num.num_of_int len))]
         in
         let op = mk_op opname_RawSetBitFieldOp params in
            mk_term op []
    | EqRawIntOp (p, s) ->
         make_rawint_term opname_EqRawIntOp p s
    | NeqRawIntOp (p, s) ->
         make_rawint_term opname_NeqRawIntOp p s
    | LtRawIntOp (p, s) ->
         make_rawint_term opname_LtRawIntOp p s
    | LeRawIntOp (p, s) ->
         make_rawint_term opname_LeRawIntOp p s
    | GtRawIntOp (p, s) ->
         make_rawint_term opname_GtRawIntOp p s
    | GeRawIntOp (p, s) ->
         make_rawint_term opname_GeRawIntOp p s
    | CmpRawIntOp (p, s) ->
         make_rawint_term opname_CmpRawIntOp p s
    | PlusFloatOp p ->
         make_rawfloat_term opname_PlusFloatOp p
    | MinusFloatOp p ->
         make_rawfloat_term opname_MinusFloatOp p
    | MulFloatOp p ->
         make_rawfloat_term opname_MulFloatOp p
    | DivFloatOp p ->
         make_rawfloat_term opname_DivFloatOp p
    | RemFloatOp p ->
         make_rawfloat_term opname_RemFloatOp p
    | MaxFloatOp p ->
         make_rawfloat_term opname_MaxFloatOp p
    | MinFloatOp p ->
         make_rawfloat_term opname_MinFloatOp p
    | EqFloatOp p ->
         make_rawfloat_term opname_EqFloatOp p
    | NeqFloatOp p ->
         make_rawfloat_term opname_NeqFloatOp p
    | LtFloatOp p ->
         make_rawfloat_term opname_LtFloatOp p
    | LeFloatOp p ->
         make_rawfloat_term opname_LeFloatOp p
    | GtFloatOp p ->
         make_rawfloat_term opname_GtFloatOp p
    | GeFloatOp p ->
         make_rawfloat_term opname_GeFloatOp p
    | CmpFloatOp p ->
         make_rawfloat_term opname_CmpFloatOp p
    | ATan2FloatOp p ->
         make_rawfloat_term opname_ATan2FloatOp p
    | PowerFloatOp p ->
         make_rawfloat_term opname_PowerFloatOp p
    | LdExpFloatIntOp p ->
         make_rawfloat_term opname_LdExpFloatIntOp p
    | EqEqOp ty ->
         mk_simple_term opname_EqEqOp [make_ty ty]
    | NeqEqOp ty ->
         mk_simple_term opname_NeqEqOp [make_ty ty]
    | PlusPointerOp (sub_block, p, s) ->
         let params =
            [make_param (Number (num_of_rawint_precision p));
             make_param (Token (string_of_boolean s))]
         in
         let op = mk_op opname_PlusPointerOp params in
         let sub_block = mk_bterm [] (make_sub_block sub_block) in
            mk_term op [sub_block]

(*
 * A field is identified by a triple (frame, field, subfield).
 *)
let term_FrameLabel = << FrameLabel[frame:t, field:t, subfield:t] >>
let opname_FrameLabel = opname_of_term term_FrameLabel

let dest_frame_label t =
   let { term_op = op; term_terms = bterms } = dest_term t in
   let { op_name = op; op_params = params } = dest_op op in
   let params = dest_params params in
   let bterms = List.map dest_bterm bterms in
      match params, bterms with
         [Token frame; Token field; Token subfield], []
         when Opname.eq op opname_FrameLabel ->
            Symbol.add frame, Symbol.add field, Symbol.add subfield

       | _ ->
            raise (RefineError ("dest_frame_label", StringTermError ("not a frame label", t)))

let make_frame_label (frame, field, subfield) =
   let params =
      [make_param (Token (Symbol.to_string frame));
       make_param (Token (Symbol.to_string field));
       make_param (Token (Symbol.to_string subfield))]
   in
   let op = mk_op opname_FrameLabel params in
      mk_term op []

(*
 * Normal values:
 *    AtomNil ty
 *       A nil pointer of indicated type.  This will be a zero-size block,
 *       therefore when dereferencing the pointer you can use a standard
 *       BoundsCheck to catch.
 *
 *    AtomInt i
 *       ML-style integer i (31 bit, LSB is 1)
 *
 *    AtomEnum (bound, value)
 *       Enumeration value.  Should satisfy 0 <= value < bound.
 *
 *    AtomRawInt i
 *       Native integer i (precision and signed are encoded in i)
 *
 *    AtomFloat f
 *       Floating-point value f (precision is encoded in f)
 *
 *    AtomLabel (label, off)
 *       Offset off to a value in a TyFrame (label) block.
 *
 *    AtomSizeof (frames, constant)
 *       Total size of the frames in the list, plus an arbitrary constant.
 *
 *    AtomConst (ty, ty_var, i)
 *       Constant constructor (used for constructor cases in unions which
 *       have no arguments).  Non-constant constructors are created with
 *       AllocUnion, below, which has a similar form.
 *
 *    AtomVar v
 *       Reference to a variable v.
 *
 *    AtomFun v
 *       Global function v.
 *
 *    AtomTyApply (v, t, [t_1; ...; t_n]):
 *       v should have type (TyAll x_1, ..., x_n). t
 *       The quantifier is instantiated to get an atom of type
 *          t[t_1, ..., t_n/x_1, ..., x_n]
 *
 *    AtomTyPack (v, s, [t_1, ..., t_n])
 *       Existential introduction; here's the informal rule.
 *
 *       v : s[t_1, ..., t_n/x_1, ..., x_n]
 *       s = TyExists (x_1, ..., x_n. s')
 *       ----------------------------------
 *       AtomTyPack (v, s, [t_1, ..., t_n]) : s
 *
 *    AtomTyUnpack v
 *       If v has type TyExists (x_0, ..., x_{n - 1}. t)
 *       then (AtomTyUnpack v) : t[v.0, ..., v_{n - 1}/x_0, ..., x_{n - 1}]
 *
 *    AtomRawDataOfFrame v:
 *       Convert v from some frame type to a TyRawData
 *
 *    AtomUnop (op, a):
 *       Unary arithmetic
 *
 *    AtomBinop (op, a1, a2):
 *       Binary arithmetic
 *
 * AtomLabel and AtomSizeof are used for frames; since the FIR may rearrange
 * and add new elements to the frames, we cannot use constant offsets/sizes
 * for these objects during the FIR.
 *)
let term_AtomNil = << AtomNil{'ty} >>
let opname_AtomNil = opname_of_term term_AtomNil
let term_AtomInt = << AtomInt{'i} >>
let opname_AtomInt = opname_of_term term_AtomInt
let term_AtomEnum = << AtomEnum[n:n, i:n] >>
let opname_AtomEnum = opname_of_term term_AtomEnum
let term_AtomRawInt = << AtomRawInt{'i} >>
let opname_AtomRawInt = opname_of_term term_AtomRawInt
let term_AtomFloat = << AtomFloat{'x} >>
let opname_AtomFloat = opname_of_term term_AtomFloat
let term_AtomLabel = << AtomLabel{'frame_label; 'rawint} >>
let opname_AtomLabel = opname_of_term term_AtomLabel
let term_AtomSizeof = << AtomSizeof{'ty_var_list; 'rawint} >>
let opname_AtomSizeof = opname_of_term term_AtomSizeof
let term_AtomConst = << AtomConst[i:n]{'ty; 'ty_var} >>
let opname_AtomConst = opname_of_term term_AtomConst
let term_AtomVar = << AtomVar{'v} >>
let opname_AtomVar = opname_of_term term_AtomVar
let term_AtomFun = << AtomFun{'v} >>
let opname_AtomFun = opname_of_term term_AtomFun

   (* Polymorphism *)
let term_AtomTyApply = << AtomTyApply{'a; 'ty; 'ty_list} >>
let opname_AtomTyApply = opname_of_term term_AtomTyApply
let term_AtomTyPack = << AtomTyPack{'v; 'ty; 'ty_list} >>
let opname_AtomTyPack = opname_of_term term_AtomTyPack
let term_AtomTyUnpack = << AtomTyUnpack{'v} >>
let opname_AtomTyUnpack = opname_of_term term_AtomTyUnpack

   (* Arithmetic *)
let term_AtomUnop = << AtomUnop{'op; 'a} >>
let opname_AtomUnop = opname_of_term term_AtomUnop
let term_AtomBinop = << AtomBinop{'op; 'a1; 'a2} >>
let opname_AtomBinop = opname_of_term term_AtomBinop

let dest_poly_atom (dest_ty : term -> 'ty) (dest_atom : term -> 'atom) (t : term) : ('ty, 'atom) poly_atom =
   let { term_op = op; term_terms = bterms } = dest_term t in
   let { op_name = op; op_params = params } = dest_op op in
   let params = dest_params params in
   let bterms = List.map dest_bterm bterms in
      match params, bterms with
         [], [{ bvars = []; bterm = ty }]
         when Opname.eq op opname_AtomNil ->
            AtomNil (dest_ty ty)

         (* AtomInt *)
       | [], [{ bvars = []; bterm = i }]
         when Opname.eq op opname_AtomInt ->
            AtomInt (dest_int i)

         (* AtomEnum *)
       | [Number n; Number i], []
         when Opname.eq op opname_AtomEnum ->
            AtomEnum (Lm_num.int_of_num n, Lm_num.int_of_num i)

         (* AtomRawInt *)
       | [], [{ bvars = []; bterm = i }]
         when Opname.eq op opname_AtomRawInt ->
            AtomRawInt (dest_rawint i)

         (* AtomFloat *)
       | [], [{ bvars = []; bterm = x }]
         when Opname.eq op opname_AtomFloat ->
            AtomFloat (dest_rawfloat x)

         (* AtomLabel *)
       | [], [{ bvars = []; bterm = label };
              { bvars = []; bterm = i }]
         when Opname.eq op opname_AtomLabel ->
            let label = dest_frame_label label in
            let i = dest_rawint i in
               AtomLabel (label, i)

         (* AtomSizeof *)
       | [], [{ bvars = []; bterm = ty_var_list };
              { bvars = []; bterm = i }]
         when Opname.eq op opname_AtomSizeof ->
            let ty_var_list = List.map dest_symbol (dest_xlist ty_var_list) in
            let i = dest_rawint i in
               AtomSizeof (ty_var_list, i)

         (* AtomConst *)
       | [], [{ bvars = []; bterm = ty };
              { bvars = []; bterm = ty_var };
              { bvars = []; bterm = i }]
         when Opname.eq op opname_AtomConst ->
            let ty = dest_ty ty in
            let ty_var = dest_symbol ty_var in
            let i = dest_int i in
               AtomConst (ty, ty_var, i)

         (* AtomVar *)
       | [], [{ bvars = []; bterm = v }]
         when Opname.eq op opname_AtomVar ->
            AtomVar (dest_symbol v)

         (* AtomFun *)
       | [], [{ bvars = []; bterm = v }]
         when Opname.eq op opname_AtomVar ->
            AtomFun (dest_symbol v)

         (* AtomTyApply *)
       | [], [{ bvars = []; bterm = a };
              { bvars = []; bterm = ty };
              { bvars = []; bterm = ty_list }]
         when Opname.eq op opname_AtomTyApply ->
            let a = dest_atom a in
            let ty = dest_ty ty in
            let ty_list = List.map dest_ty (dest_xlist ty_list) in
               AtomTyApply (a, ty, ty_list)

         (* AtomTyUnpack *)
       | [], [{ bvars = []; bterm = v }]
         when Opname.eq op opname_AtomTyUnpack ->
            AtomTyUnpack (dest_symbol v)

         (* AtomUnop *)
       | [], [{ bvars = []; bterm = unop };
              { bvars = []; bterm = a }]
         when Opname.eq op opname_AtomUnop ->
            let op = dest_unop dest_ty unop in
            let a = dest_atom a in
               AtomUnop (op, a)

         (* AtomBinop *)
       | [], [{ bvars = []; bterm = binop };
              { bvars = []; bterm = a1 };
              { bvars = []; bterm = a2 }]
         when Opname.eq op opname_AtomBinop ->
            let op = dest_binop dest_ty binop in
            let a1 = dest_atom a1 in
            let a2 = dest_atom a2 in
               AtomBinop (op, a1, a2)

       | _ ->
            raise (RefineError ("dest_poly_atom", StringTermError ("not an atom", t)))

let make_poly_atom make_ty make_atom a =
   match a with
      AtomNil ty ->
         mk_simple_term opname_AtomNil [make_ty ty]
    | AtomInt i ->
         mk_simple_term opname_AtomInt [make_int i]
    | AtomEnum (n, i) ->
         let params =
            [make_param (Number (Lm_num.num_of_int n));
             make_param (Number (Lm_num.num_of_int i))]
         in
         let op = mk_op opname_AtomEnum params in
            mk_term op []
    | AtomRawInt i ->
         mk_simple_term opname_AtomRawInt [make_rawint i]
    | AtomFloat x ->
         mk_simple_term opname_AtomFloat [make_rawfloat x]
    | AtomLabel (label, i) ->
         let label = make_frame_label label in
         let i = make_rawint i in
            mk_simple_term opname_AtomLabel [label; i]
    | AtomSizeof (ty_vars, i) ->
         let ty_vars = mk_xlist_term (List.map make_symbol ty_vars) in
         let i = make_rawint i in
            mk_simple_term opname_AtomSizeof [ty_vars; i]
    | AtomConst (ty, ty_var, i) ->
         let params = [make_param (Number (Lm_num.num_of_int i))] in
         let op = mk_op opname_AtomConst params in
         let ty = mk_bterm [] (make_ty ty) in
         let ty_var = mk_bterm [] (make_symbol ty_var) in
            mk_term op [ty; ty_var]
    | AtomVar v ->
         mk_simple_term opname_AtomVar [make_symbol v]
    | AtomFun v ->
         mk_simple_term opname_AtomFun [make_symbol v]
    | AtomTyApply (a, ty, ty_list) ->
         let a = make_atom a in
         let ty = make_ty ty in
         let ty_list = mk_xlist_term (List.map make_ty ty_list) in
            mk_simple_term opname_AtomTyApply [a; ty; ty_list]
    | AtomTyPack (v, ty, ty_list) ->
         let v = make_symbol v in
         let ty = make_ty ty in
         let ty_list = mk_xlist_term (List.map make_ty ty_list) in
            mk_simple_term opname_AtomTyPack [v; ty; ty_list]
    | AtomTyUnpack v ->
         mk_simple_term opname_AtomTyUnpack [make_symbol v]
    | AtomUnop (op, a) ->
         let op = make_unop make_ty op in
         let a = make_atom a in
            mk_simple_term opname_AtomUnop [op; a]
    | AtomBinop (op, a1, a2) ->
         let op = make_binop make_ty op in
         let a1 = make_atom a1 in
         let a2 = make_atom a2 in
            mk_simple_term opname_AtomBinop [op; a1; a2]

(*
 * Allocation operators:
 *    AllocTuple (class, ty_vars, ty, atoms)
 *       Allocate a tuple of indicated type ty, and using the indicated
 *       atoms as initializer values.  If ty_vars is not empty, then the
 *       tuple is embedded in a universal qualifier that binds the named
 *       symbols; the ty_vars may be used by the initializer atoms.
 *
 *    AllocDTuple (ty, ty_var, tag, atoms)
 *       Allocate a dependent tuple with the given tag and the indicated
 *       elements as initializer values.
 *
 *    AllocUnion (ty_vars, ty, ty_var, tag, atoms)
 *       Allocate a union with the integer tag given, and using the atoms
 *       as initialisers for that union case.  The name of the union is
 *       given in ty_var.  The type arguments to instantiate the union
 *       are in the result type, ty.  If ty_vars is not empty, then the
 *       tuple is embedded in a universal qualifier that binds the named
 *       symbols; the ty_vars may be used by the initializer atoms.
 *
 *    AllocArray (ty, atoms)
 *       Allocate an array with indicated atoms for initialization.  The
 *       type given is the type of the array, so if ty is (TyArray ty'),
 *       then the type of the atoms should be ty'.
 *
 *    AllocVArray (ty, indexty, size, init)
 *       Allocate a VArray with indicated size, and using the initialiser
 *       atom to initialise all entries.  The indexty is used to indicate
 *       whether size is in bytes or words.  The type given is the type
 *       of the array.
 *
 *    AllocMalloc (ty, size)
 *       Standard C allocation.  Allocate a TyRawData block with size bytes.
 *
 *    AllocFrame (v, type_args)
 *       Allocate a new frame with the name v.  The frame is instantiated
 *       with the type_args indicated (which must be smalltypes).
 *)
let term_AllocTuple = << AllocTuple{'tuple_class; 'ty; 'atom_list} >>
let opname_AllocTuple = opname_of_term term_AllocTuple
let term_AllocUnion = << AllocUnion[i:n]{'ty; 'ty_var; 'atom_list} >>
let opname_AllocUnion = opname_of_term term_AllocUnion
let term_AllocDTuple = << AllocDTuple{'ty; 'ty_var; 'atom; 'atom_list} >>
let opname_AllocDTuple = opname_of_term term_AllocDTuple
let term_AllocArray = << AllocArray{'ty; 'atom_list} >>
let opname_AllocArray = opname_of_term term_AllocArray
let term_AllocVArray = << AllocVArray{'ty; 'sub_index; 'atom1; 'atom2} >>
let opname_AllocVArray = opname_of_term term_AllocVArray
let term_AllocMalloc = << AllocMalloc{'ty; 'atom} >>
let opname_AllocMalloc = opname_of_term term_AllocMalloc
let term_AllocFrame = << AllocFrame{'ty_var; 'ty_list} >>
let opname_AllocFrame = opname_of_term term_AllocFrame

let dest_poly_alloc_op dest_ty dest_atom t =
   let vars, t = dest_ty_lambda t in
   let { term_op = op; term_terms = bterms } = dest_term t in
   let { op_name = op; op_params = params } = dest_op op in
   let params = dest_params params in
   let bterms = List.map dest_bterm bterms in
      match params, bterms with
         [], [{ bvars = []; bterm = tuple_class };
              { bvars = []; bterm = ty };
              { bvars = []; bterm = atom_list }]
         when Opname.eq op opname_AllocTuple ->
            let tuple_class = dest_tuple_class tuple_class in
            let ty = dest_ty ty in
            let atom_list = List.map dest_atom (dest_xlist atom_list) in
               AllocTuple (tuple_class, vars, ty, atom_list)

       | [Number i], [{ bvars = []; bterm = ty };
                      { bvars = []; bterm = ty_var };
                      { bvars = []; bterm = atom_list }]
         when Opname.eq op opname_AllocUnion ->
            let i = Lm_num.int_of_num i in
            let ty = dest_ty ty in
            let ty_var = dest_symbol ty_var in
            let atom_list = List.map dest_atom (dest_xlist atom_list) in
               AllocUnion (vars, ty, ty_var, i, atom_list)

       | [], [{ bvars = []; bterm = ty };
              { bvars = []; bterm = ty_var };
              { bvars = []; bterm = a };
              { bvars = []; bterm = atom_list }]
         when Opname.eq op opname_AllocDTuple ->
            let ty = dest_ty ty in
            let ty_var = dest_symbol ty_var in
            let a = dest_atom a in
            let atom_list = List.map dest_atom (dest_xlist atom_list) in
               AllocDTuple (ty, ty_var, a, atom_list)

       | [], [{ bvars = []; bterm = ty };
              { bvars = []; bterm = atom_list }]
         when Opname.eq op opname_AllocArray ->
            let ty = dest_ty ty in
            let atom_list = List.map dest_atom (dest_xlist atom_list) in
               AllocArray (ty, atom_list)

       | [], [{ bvars = []; bterm = ty };
              { bvars = []; bterm = sub_index };
              { bvars = []; bterm = a1 };
              { bvars = []; bterm = a2 }]
         when Opname.eq op opname_AllocVArray ->
            let ty = dest_ty ty in
            let sub_index = dest_sub_index sub_index in
            let a1 = dest_atom a1 in
            let a2 = dest_atom a2 in
               AllocVArray (ty, sub_index, a1, a2)

       | [], [{ bvars = []; bterm = ty };
              { bvars = []; bterm = a }]
         when Opname.eq op opname_AllocMalloc ->
            let ty = dest_ty ty in
            let a = dest_atom a in
               AllocMalloc (ty, a)

       | [], [{ bvars = []; bterm = ty_var };
              { bvars = []; bterm = ty_list }]
         when Opname.eq op opname_AllocFrame ->
            let ty_var = dest_symbol ty_var in
            let ty_list = List.map dest_ty (dest_xlist ty_list) in
               AllocFrame (ty_var, ty_list)

       | _ ->
            raise (RefineError ("dest_poly_alloc_op", StringTermError ("not an alloc op", t)))

let make_poly_alloc_op make_ty make_atom op =
   match op with
      AllocTuple (tuple_class, ty_vars, ty, atom_list) ->
         let tuple_class = make_tuple_class tuple_class in
         let ty = make_ty ty in
         let atom_list = mk_xlist_term (List.map make_atom atom_list) in
         let t = mk_simple_term opname_AllocTuple [tuple_class; ty; atom_list] in
            make_ty_lambda ty_vars t

    | AllocUnion (ty_vars, ty, ty_var, i, atom_list) ->
         let ty = mk_bterm [] (make_ty ty) in
         let ty_var = mk_bterm [] (make_symbol ty_var) in
         let atom_list = mk_bterm [] (mk_xlist_term (List.map make_atom atom_list)) in
         let params = [make_param (Number (Lm_num.num_of_int i))] in
         let op = mk_op opname_AllocUnion params in
         let t = mk_term op [ty; ty_var; atom_list] in
            make_ty_lambda ty_vars t

    | AllocDTuple (ty, ty_var, a, atom_list) ->
         let ty = make_ty ty in
         let ty_var = make_symbol ty_var in
         let a = make_atom a in
         let atom_list = mk_xlist_term (List.map make_atom atom_list) in
            mk_simple_term opname_AllocDTuple [ty; ty_var; a; atom_list]

    | AllocArray (ty, atom_list) ->
         let ty = make_ty ty in
         let atom_list = mk_xlist_term (List.map make_atom atom_list) in
            mk_simple_term opname_AllocArray [ty; atom_list]

    | AllocVArray (ty, sub_index, a1, a2) ->
         let ty = make_ty ty in
         let sub_index = make_sub_index sub_index in
         let a1 = make_atom a1 in
         let a2 = make_atom a2 in
            mk_simple_term opname_AllocVArray [ty; sub_index; a1; a2]

    | AllocMalloc (ty, a) ->
         let ty = make_ty ty in
         let a = make_atom a in
            mk_simple_term opname_AllocMalloc [ty; a]

    | AllocFrame (ty_var, ty_list) ->
         let ty_var = make_symbol ty_var in
         let ty_list = mk_xlist_term (List.map make_ty ty_list) in
            mk_simple_term opname_AllocFrame [ty_var; ty_list]

(*
 * Tail call operators for the SpecialCall construct.  The SpecialCall
 * is used by constructs which will eventually call some other local
 * function (say, f), and as such they resemble normal tailcalls. How-
 * ever, these constructs require some special processing first, such
 * as process migration or atomicity.  This construct identifies which
 * case is occurring.
 *
 * The special ops are briefly described below; check the MIR or runtime
 * docs for a more thorough description however.
 *
 *    TailSysMigrate (id, loc_ptr, loc_off, f, args)
 *       Perform a migration between systems.  id is a unique identifier for
 *       the call.  The destination is described by a null-terminated string
 *       at (loc_ptr, loc_off).  See migration documentation for details on
 *       the string's format.  After migration, the function f is called
 *       with args given; if args = (v1, v2, ..., vn) then we will call
 *       f(v1, v2, ..., vn).
 *
 * Note for atomic transactions:  the atomic levels are organized such that
 * level *0* is the outermost level, where no atomic entries have occurred.
 * Each entry creates a new level.  Suppose there are N levels; rollback and
 * commit can operate on the i'th level, where 0 < i <= N.  Commit/rollback
 * on the Nth level will take action on the most recently entry, and commit/
 * rollback on the 1st level will take action on the oldest entry.  Also, if
 * i = 0, then the backend will take i = N automatically.
 *
 *    TailAtomic (f, c, args)
 *       Enter a new atomic block, then call f.  c is (currently) an
 *       integer constant that is passed to f; args are the variables
 *       which are normally passed to f; note that on rollback, f will
 *       be called again; it will receive the same args but the value
 *       of c will change.  If args = (v1, v2, ..., vn) then we will
 *       call f(c, v1, v2, ..., vn).
 *
 *    TailAtomicRollback (level, c)
 *       Rollback the atomic level indicated, and call the function f
 *       again (where f was the function used by that atomic level).
 *       ALL levels more recent than <level> must be rolled back.  We
 *       will be in level <level> after this is called; in effect, we
 *       REENTER the transaction (this is not an abort).
 *
 *    TailAtomicCommit (level, g, args)
 *       Commits (exits) the atomic level indicated, then calls function
 *       g with the args given.  Note that g is not same as function f
 *       above; this can be an arbitrary function, and it receives only
 *       the args given here.  A commit on an older level will simply
 *       merge that level's data with the previous level --- it will NOT
 *       commit more recent levels.
 *)
let term_TailMigrate = << TailMigrate[i:n]{'a1; 'a2; 'a3; 'atom_list} >>
let opname_TailMigrate = opname_of_term term_TailMigrate
let term_TailSpeculate = << TailSpeculate{'a1; 'a2; 'atom_list} >>
let opname_TailSpeculate = opname_of_term term_TailSpeculate
let term_TailAbort = << TailAbort{'a1; 'a2} >>
let opname_TailAbort = opname_of_term term_TailAbort
let term_TailCommit = << TailCommit{'a1; 'a2; 'atom_list} >>
let opname_TailCommit = opname_of_term term_TailCommit

let dest_poly_tailop dest_atom t =
   let { term_op = op; term_terms = bterms } = dest_term t in
   let { op_name = op; op_params = params } = dest_op op in
   let params = dest_params params in
   let bterms = List.map dest_bterm bterms in
      match params, bterms with
         [Number i], [{ bvars = []; bterm = a1 };
                      { bvars = []; bterm = a2 };
                      { bvars = []; bterm = a3 };
                      { bvars = []; bterm = atom_list }]
         when Opname.eq op opname_TailMigrate ->
            let a1 = dest_atom a1 in
            let a2 = dest_atom a2 in
            let a3 = dest_atom a3 in
            let atom_list = List.map dest_atom (dest_xlist atom_list) in
            let i = Lm_num.int_of_num i in
               TailSysMigrate (i, a1, a2, a3, atom_list)

       | [], [{ bvars = []; bterm = a1 };
              { bvars = []; bterm = a2 };
              { bvars = []; bterm = atom_list }]
         when Opname.eq op opname_TailSpeculate ->
            let a1 = dest_atom a1 in
            let a2 = dest_atom a2 in
            let atom_list = List.map dest_atom (dest_xlist atom_list) in
               TailAtomic (a1, a2, atom_list)

       | [], [{ bvars = []; bterm = a1 };
              { bvars = []; bterm = a2 }]
         when Opname.eq op opname_TailAbort ->
            let a1 = dest_atom a1 in
            let a2 = dest_atom a2 in
               TailAtomicRollback (a1, a2)

       | [], [{ bvars = []; bterm = a1 };
              { bvars = []; bterm = a2 };
              { bvars = []; bterm = atom_list }]
         when Opname.eq op opname_TailCommit ->
            let a1 = dest_atom a1 in
            let a2 = dest_atom a2 in
            let atom_list = List.map dest_atom (dest_xlist atom_list) in
               TailAtomicCommit (a1, a2, atom_list)

       | _ ->
            raise (RefineError ("dest_poly_tailop", StringTermError ("not a tailop", t)))

let make_poly_tailop make_atom op =
   match op with
      TailSysMigrate (i, a1, a2, a3, atom_list) ->
         let a1 = mk_bterm [] (make_atom a1) in
         let a2 = mk_bterm [] (make_atom a2) in
         let a3 = mk_bterm [] (make_atom a3) in
         let atom_list = mk_bterm [] (mk_xlist_term (List.map make_atom atom_list)) in
         let params = [make_param (Number (Lm_num.num_of_int i))] in
         let op = mk_op opname_TailSpeculate params in
            mk_term op [a1; a2; a3; atom_list]

    | TailAtomic (a1, a2, atom_list) ->
         let a1 = make_atom a1 in
         let a2 = make_atom a2 in
         let atom_list = mk_xlist_term (List.map make_atom atom_list) in
            mk_simple_term opname_TailSpeculate [a1; a2; atom_list]

    | TailAtomicRollback (a1, a2) ->
         let a1 = make_atom a1 in
         let a2 = make_atom a2 in
            mk_simple_term opname_TailAbort [a1; a2]

    | TailAtomicCommit (a1, a2, atom_list) ->
         let a1 = make_atom a1 in
         let a2 = make_atom a2 in
         let atom_list = mk_xlist_term (List.map make_atom atom_list) in
            mk_simple_term opname_TailCommit [a1; a2; atom_list]

(*
 * Predicates and assertions.
 * Currently, these are used mainly for runtime safety checks.
 * However, it is likely that this set will grow to include
 * higher-level proofs, whenever we figure out what those are.
 *
 * For now we have these simple forms:
 *    IsMutable v
 *       Required between any Reserve and SetSubscript.  The argument is
 *       a block, and the assertion tells the runtime to make the block
 *       mutable so it can be modified.
 *
 *    Reserve (bytes, pointers)
 *       Reserve at least "a" bytes of storage from the runtime.  This
 *       number includes the size of the maximum allocation along any
 *       execution path, terminating at the next reserve.  The size
 *       includes the size of runtime block headers, which are defined
 *       in arch/conf/sizeof.ml.
 *
 *    BoundsCheck (subop, v, a1, a2)
 *       An array bounds check. Succeeds if a1 >= 0 && a2 <= array length.
 *       In general, a1 is the lower bound and a2 is the upper bound.
 *
 *    ElementCheck (subop, v, a)
 *       Succeeds if v[a] has the element specified by the subop.
 *)
let term_IsMutable = << IsMutable{'a} >>
let opname_IsMutable = opname_of_term term_IsMutable
let term_Reserve = << Reserve{'a1; 'a2} >>
let opname_Reserve = opname_of_term term_Reserve
let term_BoundsCheck = << BoundsCheck{'subop; 'a1; 'a2; 'a3} >>
let opname_BoundsCheck = opname_of_term term_BoundsCheck
let term_ElementCheck = << ElementCheck{'ty; 'subop; 'a1; 'a2} >>
let opname_ElementCheck = opname_of_term term_ElementCheck

let dest_poly_pred dest_ty dest_atom t =
   let { term_op = op; term_terms = bterms } = dest_term t in
   let { op_name = op; op_params = params } = dest_op op in
   let params = dest_params params in
   let bterms = List.map dest_bterm bterms in
      match params, bterms with
         [], [{ bvars = []; bterm = a }]
         when Opname.eq op opname_IsMutable ->
            let a = dest_atom a in
               IsMutable a

       | [], [{ bvars = []; bterm = a1 };
              { bvars = []; bterm = a2 }]
         when Opname.eq op opname_Reserve ->
            let a1 = dest_atom a1 in
            let a2 = dest_atom a2 in
               Reserve (a1, a2)

       | [], [{ bvars = []; bterm = subop };
              { bvars = []; bterm = a1 };
              { bvars = []; bterm = a2 };
              { bvars = []; bterm = a3 }]
         when Opname.eq op opname_BoundsCheck ->
            let subop = dest_poly_subop dest_ty subop in
            let a1 = dest_atom a1 in
            let a2 = dest_atom a2 in
            let a3 = dest_atom a3 in
               BoundsCheck (subop, a1, a2, a3)

       | [], [{ bvars = []; bterm = ty };
              { bvars = []; bterm = subop };
              { bvars = []; bterm = a1 };
              { bvars = []; bterm = a2 }]
         when Opname.eq op opname_ElementCheck ->
            let ty = dest_ty ty in
            let subop = dest_poly_subop dest_ty subop in
            let a1 = dest_atom a1 in
            let a2 = dest_atom a2 in
               ElementCheck (ty, subop, a1, a2)

       | _ ->
            raise (RefineError ("dest_poly_pred", StringTermError ("not a predicate", t)))

let make_poly_pred make_ty make_atom pred =
   match pred with
      IsMutable a ->
         let a = make_atom a in
            mk_simple_term opname_IsMutable [a]

    | Reserve (a1, a2) ->
         let a1 = make_atom a1 in
         let a2 = make_atom a2 in
            mk_simple_term opname_Reserve [a1; a2]

    | BoundsCheck (subop, a1, a2, a3) ->
         let subop = make_poly_subop make_ty subop in
         let a1 = make_atom a1 in
         let a2 = make_atom a2 in
         let a3 = make_atom a3 in
            mk_simple_term opname_BoundsCheck [subop; a1; a2; a3]

    | ElementCheck (ty, subop, a1, a2) ->
         let ty = make_ty ty in
         let subop = make_poly_subop make_ty subop in
         let a1 = make_atom a1 in
         let a2 = make_atom a2 in
            mk_simple_term opname_ElementCheck [ty; subop; a1; a2]

(*
 * Expressions.
 *)

(* Primitive operations *)
let term_LetAtom = << LetAtom{'ty; 'a; v. 'e['v]} >>
let opname_LetAtom = opname_of_term term_LetAtom

(* Function application *)
(*
 * LetExt (v, ty_v, gc_flag, f, ty_f, ty_args, args, e)
 *    Call an external function f, with function type ty_f, and give
 *    it the arguments listed in ty_args and args. The return value of f is stored
 *    in v, which should have type ty_v.
 *
 * TailCall (label, f, args)
 *    Call the function f with indicated arguments.  f may either be
 *    the name of a function directly, or it may be a variable holding
 *    a function pointer.  The label is only used for debugging, to
 *    identify this TailCall.
 *
 * SpecialCall (label, tailop)
 *    Execute a special call.  SpecialCalls resemble TailCalls in that
 *    control is transferred to another function; however, some action
 *    is usually performed before the new function is invoked (e.g.
 *    a system migration).  See comments for tailop (above) for details.
 *    The label is only used for debugging to identify this SpecialCall.
 *)
let term_LetExt = << LetExt[f:s, b:t]{'ty; 'ty_fun; 'ty_list; 'atom_list; v. 'e['v]} >>
let opname_LetExt = opname_of_term term_LetExt
let term_TailCall = << TailCall[label:t]{'a; 'atom_list} >>
let opname_TailCall = opname_of_term term_TailCall
let term_SpecialCall = << SpecialCall[label:t]{'tailop} >>
let opname_SpecialCall = opname_of_term term_SpecialCall

(*
 * Control.
 *
 * Match (a, [l1, s1, e1; ...; ln, sn, en])
 *    Choose the first set si where (a in si); the value is ei.
 *
 * MatchDTuple (a, [l1, a1, e1; ...; ln, an, en])
 *    The atom a should be a dependent tuple (of type TyDTuple).
 *    Choose the first case ei where a has tag ai.
 *    A tag of None matches any tag.
 *
 * TypeCase (a1, a2, v1, v2, e1, e2):
 *    This is like MatchDTuple, but jyh has completely
 *    forgotten what all the different fields are.
 *)
let term_MatchCase = << MatchCase[label:t]{'set; 'e} >>
let opname_MatchCase = opname_of_term term_MatchCase
let term_MatchDTupleCase = << MatchDTupleCase[label:t]{'atom_opt; 'e} >>
let opname_MatchDTupleCase = opname_of_term term_MatchDTupleCase

let term_Match = << Match{'a; 'cases} >>
let opname_Match = opname_of_term term_Match
let term_MatchDTuple = << MatchDTuple{'a; 'cases} >>
let opname_MatchDTuple = opname_of_term term_MatchDTuple

let dest_match_case dest_exp t =
   let { term_op = op; term_terms = bterms } = dest_term t in
   let { op_name = op; op_params = params } = dest_op op in
   let params = dest_params params in
   let bterms = List.map dest_bterm bterms in
      match params, bterms with
         [Token label],
         [{ bvars = []; bterm = set };
          { bvars = []; bterm = e }]
         when Opname.eq op opname_MatchCase ->
            let label = Symbol.add label in
            let set = dest_set set in
            let e = dest_exp e in
               label, set, e

       | _ ->
            raise (RefineError ("dest_match_case", StringTermError ("not a match case", t)))

let make_match_case make_exp (label, set, e) =
   let label = Symbol.to_string label in
   let set = make_set set in
   let e = make_exp e in
   let params = [make_param (Token label)] in
   let op = mk_op opname_MatchCase params in
      mk_term op [mk_bterm [] set; mk_bterm [] e]

let dest_match_dtuple_case dest_atom dest_exp t =
   let { term_op = op; term_terms = bterms } = dest_term t in
   let { op_name = op; op_params = params } = dest_op op in
   let params = dest_params params in
   let bterms = List.map dest_bterm bterms in
      match params, bterms with
         [Token label],
         [{ bvars = []; bterm = atom_opt };
          { bvars = []; bterm = e }]
         when Opname.eq op opname_MatchDTuple ->
            let label = Symbol.add label in
            let atom_opt = dest_option dest_atom atom_opt in
            let e = dest_exp e in
               label, atom_opt, e

       | _ ->
            raise (RefineError ("dest_match_dtuple_case", StringTermError ("not a match dtuple case", t)))

let make_match_dtuple_case make_atom make_exp (label, atom_opt, e) =
   let atom_opt = make_option make_atom atom_opt in
   let e = make_exp e in
   let params = [make_param (Token (Symbol.to_string label))] in
   let op = mk_op opname_MatchDTupleCase params in
      mk_term op [mk_bterm [] atom_opt; mk_bterm [] e]

(*
 * Allocation.
 *)
let term_LetAlloc = << LetAlloc{'alloc_op; v. 'e['v]} >>
let opname_LetAlloc = opname_of_term term_LetAlloc

(* Memory operations. *)
(*
 * Subscripting operations use various types of offsets, depending
 * on the type of the pointer being subscripted.  Requirements on the
 * offsets are listed below:
 *    TyTuple, TyUnion:
 *       Offset must be constant; AtomInt is interpreted as a word
 *       offset, and AtomRawInt is interpreted as a byte offset.
 *       For BoxTuple tuples, the constant must be zero.
 *    TyArray, TyRawData, TyPointer:
 *       Offset can be constant or variable.  For TyPointer, the
 *       offset is relative to the offset embedded in the infix ptr,
 *       and can be negative.
 *    TyFrame:
 *       Offset must be an AtomLabel, which indicates the frame,
 *       field, subfield, and offset into the subfield being accessed.
 *
 * LetSubscript (subop, v, ty, ptr, off, e)
 *    Read ptr[off] and store the result in v:ty, using subop to
 *    interpret the value in memory and the type of offset used.
 *
 * SetSubscript (subop, label, ptr, off, ty, a, e)
 *    Store a:ty into memory at ptr[off], using subop to interpret
 *    the value in a and the type of offset used.  The label is only
 *    used for debugging to identify this SetSubscript.
 *
 * LetGlobal (subvalue, v, ty, global, e)
 *    Read a global variable global:ty, using subvalue to interpret
 *    the value read out.
 *
 * SetGlobal (subvalue, label, global, ty, a, e)
 *    Store a into the global variable global:ty, using subvalue to
 *    interpret the value in a.  The label is used for debugging.
 *
 * Memcpy (subop, label, dstp, dsto, srcp, srco, size, e)
 *    Copies a block of memory from one block into another.  The
 *    data is read from srcp[srco], and is written to dstp[dsto].
 *    size bytes/words are copied (depending on subop). The subop
 *    indicates what types of blocks srcp and dstp are, and also
 *    how to interpret the offsets srco, dsto.  Currently both
 *    blocks must have the same subop type.
 *
 *    WARNING:  This implements a forward-copy; if dstp and srcp
 *    are the same block, and srco < dsto < srco + size, then the
 *    copy will overwrite data that it is supposed to copy, BEFORE
 *    it has copied the data. As a result, Memcpy is not recommended
 *    when srcp and dstp refer to the same block.
 *
 *    The label is used for debugging only, to identify this Memcpy.
 *)
let term_LetSubscript = << LetSubscript{'subop; 'ty; 'a1; 'a2; v. 'e['v]} >>
let opname_LetSubscript = opname_of_term term_LetSubscript
let term_SetSubscript = << SetSubscript[label:t]{'subop; 'a1; 'a2; 'ty; 'a3; 'e} >>
let opname_SetSubscript = opname_of_term term_SetSubscript
let term_LetGlobal = << LetGlobal[label:t]{'sub_value; 'ty; v. 'e['v]} >>
let opname_LetGlobal = opname_of_term term_LetGlobal
let term_SetGlobal = << SetGlobal[label:t, global:t]{'sub_value; 'ty; 'a; 'e} >>
let opname_SetGlobal = opname_of_term term_SetGlobal
let term_Memcpy = << Memcpy[label:t]{'subop; 'a1; 'a2; 'a3; 'a4; 'a5; 'e} >>
let opname_Memcpy = opname_of_term term_Memcpy

(* Assertions: label is a unique label identifying this assertion *)
let term_Call = << Call[label:t]{'a; 'atop_opt_list; 'e} >>
let opname_Call = opname_of_term term_Call
let term_Assert = << Assert[label:t]{'pred; 'e} >>
let opname_Assert = opname_of_term term_Assert

let dest_poly_exp (dest_ty : term -> 'ty) (dest_atom : term -> 'atom) (dest_exp : term -> 'exp) (t : term) : ('ty, 'atom, 'exp) poly_exp =
   let { term_op = op; term_terms = bterms } = dest_term t in
   let { op_name = op; op_params = params } = dest_op op in
   let params = dest_params params in
   let bterms = List.map dest_bterm bterms in
      match params, bterms with
         [], [{ bvars = []; bterm = ty };
              { bvars = []; bterm = a };
              { bvars = [v]; bterm = e }]
         when Opname.eq op opname_LetAtom ->
            let ty = dest_ty ty in
            let a = dest_atom a in
            let e = dest_exp e in
            let v = Symbol.add v in
               LetAtom (v, ty, a, e)

       | [String f; Token b],
         [{ bvars = []; bterm = ty };
          { bvars = []; bterm = ty_f };
          { bvars = []; bterm = ty_args };
          { bvars = []; bterm = args };
          { bvars = [v]; bterm = e }]
         when Opname.eq op opname_LetExt ->
            let b = boolean_of_string b in
            let ty = dest_ty ty in
            let ty_f = dest_ty ty_f in
            let ty_args = List.map dest_ty (dest_xlist ty_args) in
            let args = List.map dest_atom (dest_xlist args) in
            let v = Symbol.add v in
            let e = dest_exp e in
               LetExt (v, ty, f, b, ty_f, ty_args, args, e)

       | [Token label],
         [{ bvars = []; bterm = a };
          { bvars = []; bterm = args }]
         when Opname.eq op opname_TailCall ->
            let label = Symbol.add label in
            let a = dest_atom a in
            let args = List.map dest_atom (dest_xlist args) in
               TailCall (label, a, args)

       | [Token label],
         [{ bvars = []; bterm = tailop }]
         when Opname.eq op opname_SpecialCall ->
            let label = Symbol.add label in
            let tailop = dest_poly_tailop dest_atom tailop in
               SpecialCall (label, tailop)

       | [], [{ bvars = []; bterm = a };
              { bvars = []; bterm = cases }]
         when Opname.eq op opname_Match ->
            let a = dest_atom a in
            let cases = List.map (dest_match_case dest_exp) (dest_xlist cases) in
               Match (a, cases)

       | [], [{ bvars = []; bterm = a };
              { bvars = []; bterm = cases }]
         when Opname.eq op opname_MatchDTuple ->
            let a = dest_atom a in
            let cases = List.map (dest_match_dtuple_case dest_atom dest_exp) (dest_xlist cases) in
               MatchDTuple (a, cases)

       | [], [{ bvars = []; bterm = alloc_op };
              { bvars = [v]; bterm = e }]
         when Opname.eq op opname_LetAlloc ->
            let alloc_op = dest_poly_alloc_op dest_ty dest_atom alloc_op in
            let v = Symbol.add v in
            let e = dest_exp e in
               LetAlloc (v, alloc_op, e)

       | [], [{ bvars = []; bterm = subop };
              { bvars = []; bterm = ty };
              { bvars = []; bterm = a1 };
              { bvars = []; bterm = a2 };
              { bvars = [v]; bterm = e }]
         when Opname.eq op opname_LetSubscript ->
            let subop = dest_poly_subop dest_ty subop in
            let ty = dest_ty ty in
            let a1 = dest_atom a1 in
            let a2 = dest_atom a2 in
            let v = Symbol.add v in
            let e = dest_exp e in
               LetSubscript (subop, v, ty, a1, a2, e)

       | [Token label],
         [{ bvars = []; bterm = subop };
          { bvars = []; bterm = a1 };
          { bvars = []; bterm = a2 };
          { bvars = []; bterm = ty };
          { bvars = []; bterm = a3 };
          { bvars = []; bterm = e }]
         when Opname.eq op opname_SetSubscript ->
            let label = Symbol.add label in
            let subop = dest_poly_subop dest_ty subop in
            let a1 = dest_atom a1 in
            let a2 = dest_atom a2 in
            let ty = dest_ty ty in
            let a3 = dest_atom a3 in
            let e = dest_exp e in
               SetSubscript (subop, label, a1, a2, ty, a3, e)

       | [Token label],
         [{ bvars = []; bterm = sub_value };
          { bvars = []; bterm = ty };
          { bvars = [v]; bterm = e }]
         when Opname.eq op opname_LetGlobal ->
            let label = Symbol.add label in
            let sub_value = dest_poly_sub_value dest_ty sub_value in
            let ty = dest_ty ty in
            let v = Symbol.add v in
            let e = dest_exp e in
               LetGlobal (sub_value, v, ty, label, e)

       | [Token label; Token global],
         [{ bvars = []; bterm = sub_value };
          { bvars = []; bterm = ty };
          { bvars = []; bterm = a };
          { bvars = []; bterm = e }]
         when Opname.eq op opname_SetGlobal ->
            let label = Symbol.add label in
            let global = Symbol.add global in
            let sub_value = dest_poly_sub_value dest_ty sub_value in
            let ty = dest_ty ty in
            let a = dest_atom a in
            let e = dest_exp e in
               SetGlobal (sub_value, label, global, ty, a, e)

       | [Token label],
         [{ bvars = []; bterm = subop };
          { bvars = []; bterm = a1 };
          { bvars = []; bterm = a2 };
          { bvars = []; bterm = a3 };
          { bvars = []; bterm = a4 };
          { bvars = []; bterm = a5 };
          { bvars = []; bterm = e }]
         when Opname.eq op opname_Memcpy ->
            let label = Symbol.add label in
            let subop = dest_poly_subop dest_ty subop in
            let a1 = dest_atom a1 in
            let a2 = dest_atom a2 in
            let a3 = dest_atom a3 in
            let a4 = dest_atom a4 in
            let a5 = dest_atom a5 in
            let e = dest_exp e in
               Memcpy (subop, label, a1, a2, a3, a4, a5, e)

       | [Token label],
         [{ bvars = []; bterm = a };
          { bvars = []; bterm = atom_opt_list };
          { bvars = []; bterm = e }]
         when Opname.eq op opname_Call ->
            let label = Symbol.add label in
            let a = dest_atom a in
            let a_opt_list = List.map (dest_option dest_atom) (dest_xlist atom_opt_list) in
            let e = dest_exp e in
               Call (label, a, a_opt_list, e)

       | [Token label],
         [{ bvars = []; bterm = pred };
          { bvars = []; bterm = e }]
         when Opname.eq op opname_Assert ->
            let label = Symbol.add label in
            let pred = dest_poly_pred dest_ty dest_atom pred in
            let e = dest_exp e in
               Assert (label, pred, e)

       | _ ->
            raise (RefineError ("dest_poly_exp", StringTermError ("not an exp", t)))

let rec make_poly_exp (make_ty : 'ty -> term) (make_atom : 'atom -> term) (make_exp : 'exp -> term) (e : ('ty, 'atom, 'exp) poly_exp) : term =
   match e with
      LetAtom (v, ty, a, e) ->
         let v = Symbol.to_string v in
         let ty = make_ty ty in
         let a = make_atom a in
         let e = make_exp e in
         let op = mk_op opname_LetAtom [] in
            mk_term op [mk_bterm [] ty; mk_bterm [] a; mk_bterm [v] e]

    | LetExt (v, ty, f, b, ty_f, ty_args, args, e) ->
         let v = Symbol.to_string v in
         let ty = make_ty ty in
         let ty_f = make_ty ty_f in
         let ty_args = mk_xlist_term (List.map make_ty ty_args) in
         let args = mk_xlist_term (List.map make_atom args) in
         let e = make_exp e in
         let params = [make_param (String f); make_param (Token (string_of_boolean b))] in
         let op = mk_op opname_LetExt params in
            mk_term op [mk_bterm [] ty;
                        mk_bterm [] ty_f;
                        mk_bterm [] ty_args;
                        mk_bterm [] args;
                        mk_bterm [v] e]

    | TailCall (label, a, args) ->
         let a = make_atom a in
         let args = mk_xlist_term (List.map make_atom args) in
         let params = [make_param (Token (Symbol.to_string label))] in
         let op = mk_op opname_TailCall params in
            mk_term op [mk_bterm [] a; mk_bterm [] args]

    | SpecialCall (label, tailop) ->
         let tailop = make_poly_tailop make_atom tailop in
         let params = [make_param (Token (Symbol.to_string label))] in
         let op = mk_op opname_SpecialCall params in
            mk_term op [mk_bterm [] tailop]

    | Match (a, cases) ->
         let a = make_atom a in
         let cases = mk_xlist_term (List.map (make_match_case make_exp) cases) in
            mk_simple_term opname_Match [a; cases]

    | MatchDTuple (a, cases) ->
         let a = make_atom a in
         let cases = mk_xlist_term (List.map (make_match_dtuple_case make_atom make_exp) cases) in
            mk_simple_term opname_MatchDTuple [a; cases]

    | LetAlloc (v, alloc_op, e) ->
         let v = Symbol.to_string v in
         let alloc_op = make_poly_alloc_op make_ty make_atom alloc_op in
         let e = make_exp e in
         let op = mk_op opname_LetAlloc [] in
            mk_term op [mk_bterm [] alloc_op; mk_bterm [v] e]

    | LetSubscript (subop, v, ty, a1, a2, e) ->
         let subop = make_poly_subop make_ty subop in
         let v = Symbol.to_string v in
         let ty = make_ty ty in
         let a1 = make_atom a1 in
         let a2 = make_atom a2 in
         let e = make_exp e in
         let op = mk_op opname_LetSubscript [] in
            mk_term op [mk_bterm [] subop;
                        mk_bterm [] ty;
                        mk_bterm [] a1;
                        mk_bterm [] a2;
                        mk_bterm [v] e]

    | SetSubscript (subop, label, a1, a2, ty, a3, e) ->
         let subop = make_poly_subop make_ty subop in
         let label = Symbol.to_string label in
         let a1 = make_atom a1 in
         let a2 = make_atom a2 in
         let ty = make_ty ty in
         let a3 = make_atom a3 in
         let e = make_exp e in
         let params = [make_param (Token label)] in
         let op = mk_op opname_SetSubscript params in
            mk_term op [mk_bterm [] subop;
                        mk_bterm [] a1;
                        mk_bterm [] a2;
                        mk_bterm [] ty;
                        mk_bterm [] a3;
                        mk_bterm [] e]

    | LetGlobal (sub_value, v, ty, l, e) ->
         let sub_value = make_poly_sub_value make_ty sub_value in
         let v = Symbol.to_string v in
         let ty = make_ty ty in
         let l = Symbol.to_string l in
         let e = make_exp e in
         let params = [make_param (Token l)] in
         let op = mk_op opname_LetGlobal params in
            mk_term op [mk_bterm [] sub_value;
                        mk_bterm [] ty;
                        mk_bterm [v] e]

    | SetGlobal (sub_value, label, l, ty, a, e) ->
         let sub_value = make_poly_sub_value make_ty sub_value in
         let label = Symbol.to_string label in
         let l = Symbol.to_string l in
         let ty = make_ty ty in
         let a = make_atom a in
         let e = make_exp e in
         let params = [make_param (Token label); make_param (Token l)] in
         let op = mk_op opname_SetGlobal params in
            mk_term op [mk_bterm [] sub_value;
                        mk_bterm [] ty;
                        mk_bterm [] a;
                        mk_bterm [] e]

    | Memcpy (subop, label, a1, a2, a3, a4, a5, e) ->
         let subop = make_poly_subop make_ty subop in
         let label = Symbol.to_string label in
         let a1 = make_atom a1 in
         let a2 = make_atom a2 in
         let a3 = make_atom a3 in
         let a4 = make_atom a4 in
         let a5 = make_atom a5 in
         let e = make_exp e in
         let params = [make_param (Token label)] in
         let op = mk_op opname_Memcpy params in
            mk_term op [mk_bterm [] subop;
                        mk_bterm [] a1;
                        mk_bterm [] a2;
                        mk_bterm [] a3;
                        mk_bterm [] a4;
                        mk_bterm [] a5;
                        mk_bterm [] e]

    | Call (label, a, atom_opt_list, e) ->
         let label = Symbol.to_string label in
         let a = make_atom a in
         let atom_opt_list = mk_xlist_term (List.map (make_option make_atom) atom_opt_list) in
         let e = make_exp e in
         let params = [make_param (Token label)] in
         let op = mk_op opname_Call params in
            mk_term op [mk_bterm [] a;
                        mk_bterm [] atom_opt_list;
                        mk_bterm [] e]

    | Assert (label, pred, e) ->
         let label = Symbol.to_string label in
         let pred = make_poly_pred make_ty make_atom pred in
         let e = make_exp e in
         let params = [make_param (Token label)] in
         let op = mk_op opname_Assert params in
            mk_term op [mk_bterm [] pred; mk_bterm [] e]

    | TypeCase _ ->
         raise (RefineError ("make_exp", StringError "TypeCase is not supported"))

    | Debug (_, e) ->
         (* Ignore debugging *)
         make_exp e

(*
 * Initializers.
 *)
let term_InitAtom = << InitAtom{'a} >>
let opname_InitAtom = opname_of_term term_InitAtom
let term_InitAlloc = << InitAlloc{'alloc_op} >>
let opname_InitAlloc = opname_of_term term_InitAlloc
let term_InitRawData = << InitRawData[p:n]{'int_array} >>
let opname_InitRawData = opname_of_term term_InitRawData
let term_InitNames = << InitNames{'ty_var; 'names} >>
let opname_InitNames = opname_of_term term_InitNames
let term_InitName = << InitName{'v; 'v_opt} >>
let opname_InitName = opname_of_term term_InitName
let term_InitTag = << InitTag{'ty_var; 'ty_list} >>
let opname_InitTag = opname_of_term term_InitTag

let dest_init_name t =
    let { term_op = op; term_terms = bterms } = dest_term t in
   let { op_name = op; op_params = params } = dest_op op in
   let params = dest_params params in
   let bterms = List.map dest_bterm bterms in
      match params, bterms with
         [], [{ bvars = []; bterm = v };
              { bvars = []; bterm = v_opt }]
         when Opname.eq op opname_InitName ->
            let v = dest_symbol v in
            let v_opt = dest_option dest_symbol v_opt in
               v, v_opt

       | _ ->
            raise (RefineError ("dest_init_name", StringTermError ("not an init_name", t)))

let make_init_name (v, v_opt) =
   let v = make_symbol v in
   let v_opt = make_option make_symbol v_opt in
      mk_simple_term opname_InitName [v; v_opt]

let dest_poly_init dest_ty dest_atom t =
   let { term_op = op; term_terms = bterms } = dest_term t in
   let { op_name = op; op_params = params } = dest_op op in
   let params = dest_params params in
   let bterms = List.map dest_bterm bterms in
      match params, bterms with
         [], [{ bvars = []; bterm = a }]
         when Opname.eq op opname_InitAtom ->
            let a = dest_atom a in
               InitAtom a

       | [], [{ bvars = []; bterm = alloc_op }]
         when Opname.eq op opname_InitAlloc ->
            let alloc_op = dest_poly_alloc_op dest_ty dest_atom alloc_op in
               InitAlloc alloc_op

       | [Number p], [{ bvars = []; bterm = int_array }]
         when Opname.eq op opname_InitRawData ->
            let p = rawint_precision_of_num p in
            let int_array = Array.of_list (List.map dest_int (dest_xlist int_array)) in
               InitRawData (p, int_array)

       | [], [{ bvars = []; bterm = ty_var };
              { bvars = []; bterm = names }]
         when Opname.eq op opname_InitNames ->
            let ty_var = dest_symbol ty_var in
            let names = List.map dest_init_name (dest_xlist names) in
               InitNames (ty_var, names)

       | [], [{ bvars = []; bterm = ty_var };
              { bvars = []; bterm = ty_list }]
         when Opname.eq op opname_InitTag ->
            let ty_var = dest_symbol ty_var in
            let ty_list = List.map (dest_poly_mutable dest_ty) (dest_xlist ty_list) in
               InitTag (ty_var, ty_list)

       | _ ->
            raise (RefineError ("dest_poly_init", StringTermError ("not an init", t)))

let make_poly_init make_ty make_atom init =
   match init with
      InitAtom a ->
         let a = make_atom a in
            mk_simple_term opname_InitAtom [a]
    | InitAlloc alloc_op ->
         let alloc_op = make_poly_alloc_op make_ty make_atom alloc_op in
            mk_simple_term opname_InitAlloc [alloc_op]
    | InitRawData (p, int_array) ->
         let p = num_of_rawint_precision p in
         let int_array = mk_xlist_term (List.map make_int (Array.to_list int_array)) in
         let params = [make_param (Number p)] in
         let op = mk_op opname_InitRawData params in
            mk_term op [mk_bterm [] int_array]
    | InitNames (ty_var, names) ->
         let ty_var = make_symbol ty_var in
         let names = mk_xlist_term (List.map make_init_name names) in
            mk_simple_term opname_InitNames [ty_var; names]
    | InitTag (ty_var, ty_mutable_list) ->
         let ty_var = make_symbol ty_var in
         let ty_mutable_list = mk_xlist_term (List.map (make_poly_mutable make_ty) ty_mutable_list) in
            mk_simple_term opname_InitTag [ty_var; ty_mutable_list]

(*
 * Function definition.
 *)
let term_lambda = << lambda{v. 'e['v]} >>
let opname_lambda = opname_of_term term_lambda
let term_FunDef = << FunDef{'ty; 'body} >>
let opname_FunDef = opname_of_term term_FunDef

let rec dest_lambda t =
   let { term_op = op; term_terms = bterms } = dest_term t in
   let { op_name = op; op_params = params } = dest_op op in
   let params = dest_params params in
   let bterms = List.map dest_bterm bterms in
      match params, bterms with
         [], [{ bvars = [v]; bterm = t }]
         when Opname.eq op opname_lambda ->
            let vars, t = dest_lambda t in
               Symbol.add v :: vars, t
       | _ ->
            [], t

let make_lambda vars ty =
   let op = mk_op opname_lambda [] in
      List.fold_right (fun v ty ->
            mk_term op [mk_bterm [Symbol.to_string v] ty]) vars ty

let bogus_line = Lm_location.bogus_loc "m_fir_term"

let dest_poly_fundef dest_ty dest_exp t =
   let ty_vars, t = dest_ty_lambda t in
   let { term_op = op; term_terms = bterms } = dest_term t in
   let { op_name = op; op_params = params } = dest_op op in
   let params = dest_params params in
   let bterms = List.map dest_bterm bterms in
      match params, bterms with
         [], [{ bvars = []; bterm = ty };
              { bvars = []; bterm = body }]
         when Opname.eq op opname_FunDef ->
            let ty = dest_ty ty in
            let vars, e = dest_lambda body in
            let e = dest_exp e in
               bogus_line, ty_vars, ty, vars, e

       | _ ->
            raise (RefineError ("dest_poly_fundef", StringTermError ("not a fundef", t)))

let make_poly_fundef make_ty make_exp (_, ty_vars, ty, vars, e) =
   let ty = make_ty ty in
   let e = make_exp e in
   let body = make_lambda vars e in
   let fundef = mk_simple_term opname_FunDef [ty; body] in
      make_ty_lambda ty_vars fundef

(*
 * Program.
 *)
let term_Global = << Global{'ty; 'init_exp} >>
let opname_Global = opname_of_term term_Global

let dest_poly_global dest_ty dest_atom t =
   let { term_op = op; term_terms = bterms } = dest_term t in
   let { op_name = op; op_params = params } = dest_op op in
   let params = dest_params params in
   let bterms = List.map dest_bterm bterms in
      match params, bterms with
         [], [{ bvars = []; bterm = ty };
              { bvars = []; bterm = init }]
         when Opname.eq op opname_Global ->
            let ty = dest_ty ty in
            let init = dest_poly_init dest_ty dest_atom init in
               ty, init

       | _ ->
            raise (RefineError ("dest_poly_global", StringTermError ("not a global", t)))

let make_poly_global make_ty make_atom (ty, init) =
   let ty = make_ty ty in
   let init = make_poly_init make_ty make_atom init in
      mk_simple_term opname_Global [ty; init]

(*
 * General debugging info.
 *)
let term_FileFC = << FileFC >>
let opname_FileFC = opname_of_term term_FileFC
let term_FileNaml = << FileNaml >>
let opname_FileNaml = opname_of_term term_FileNaml
let term_FileJava = << FileJava >>
let opname_FileJava = opname_of_term term_FileJava
let term_FileAml = << FileAml >>
let opname_FileAml = opname_of_term term_FileAml

let dest_file_class t =
   let op = opname_of_term t in
      if Opname.eq op opname_FileFC then
         FileFC
      else if Opname.eq op opname_FileNaml then
         FileNaml
      else if Opname.eq op opname_FileJava then
         FileJava
      else if Opname.eq op opname_FileAml then
         FileAml
      else
         raise (RefineError ("dest_file_class", StringTermError ("not a file class", t)))

let make_file_class fc =
   match fc with
      FileFC -> term_FileFC
    | FileNaml -> term_FileNaml
    | FileJava -> term_FileJava
    | FileAml -> term_FileAml

let term_FileInfo = << FileInfo[dir:s, name:s]{'file_class} >>
let opname_FileInfo = opname_of_term term_FileInfo

let dest_file_info t =
   let { term_op = op; term_terms = bterms } = dest_term t in
   let { op_name = op; op_params = params } = dest_op op in
   let params = dest_params params in
   let bterms = List.map dest_bterm bterms in
      match params, bterms with
         [String dir; String name],
         [{ bvars = []; bterm = file_class }]
         when Opname.eq op opname_FileInfo ->
            let file_class = dest_file_class file_class in
               { file_dir = dir;
                 file_name = name;
                 file_class = file_class
               }

       | _ ->
            raise (RefineError ("dest_file_info", StringTermError ("not a file_info", t)))

let make_file_info info =
   let { file_dir = dir;
         file_name = name;
         file_class = fc
       } = info
   in
   let params = [make_param (String dir); make_param (String name)] in
   let op = mk_op opname_FileInfo params in
      mk_term op [mk_bterm [] (make_file_class fc)]

(*
 * For imports, we save information about the _original_
 * argument types so we can recover the original calling
 * convention.
 *)
let term_ArgFunction = << ArgFunction >>
let opname_ArgFunction = opname_of_term term_ArgFunction
let term_ArgPointer = << ArgPointer >>
let opname_ArgPointer = opname_of_term term_ArgPointer
let term_ArgRawInt = << ArgRawInt[p:n, s:t] >>
let opname_ArgRawInt = opname_of_term term_ArgRawInt
let term_ArgRawFloat = << ArgRawFloat[p:n] >>
let opname_ArgRawFloat = opname_of_term term_ArgRawFloat

let dest_import_arg t =
   let { term_op = op; term_terms = bterms } = dest_term t in
   let { op_name = op; op_params = params } = dest_op op in
   let params = dest_params params in
   let bterms = List.map dest_bterm bterms in
      match params, bterms with
         [], [] ->
            if Opname.eq op opname_ArgFunction then
               ArgFunction
            else if Opname.eq op opname_ArgPointer then
               ArgPointer
            else
               raise (RefineError ("dest_import_arg", StringTermError ("not an import_arg", t)))
       | [Number p; Token s], []
         when Opname.eq op opname_ArgRawInt ->
            let p = rawint_precision_of_num p in
            let s = boolean_of_string s in
               ArgRawInt (p, s)
       | [Number p], []
         when Opname.eq op opname_ArgRawFloat ->
            let p = rawfloat_precision_of_num p in
               ArgRawFloat p
       | _ ->
            raise (RefineError ("dest_import_arg", StringTermError ("not an import_arg", t)))

let make_import_arg arg =
   match arg with
      ArgFunction ->
         term_ArgFunction
    | ArgPointer ->
         term_ArgPointer
    | ArgRawInt (p, s) ->
         let p = num_of_rawint_precision p in
         let s = string_of_boolean s in
         let params = [make_param (Number p); make_param (Token s)] in
         let op = mk_op opname_ArgRawInt params in
            mk_term op []
    | ArgRawFloat p ->
         let p = num_of_rawfloat_precision p in
         let params = [make_param (Number p)] in
         let op = mk_op opname_ArgRawFloat params in
            mk_term op []

(*
 * On ImportFun, the bool is true iff this function
 * uses the stdargs convention.
 *)
let term_ImportGlobal = << ImportGlobal >>
let opname_ImportGlobal = opname_of_term term_ImportGlobal
let term_ImportFun = << ImportFun[b:t]{'import_arg_list} >>
let opname_ImportFun = opname_of_term term_ImportFun

let dest_import_info t =
   let { term_op = op; term_terms = bterms } = dest_term t in
   let { op_name = op; op_params = params } = dest_op op in
   let params = dest_params params in
   let bterms = List.map dest_bterm bterms in
      match params, bterms with
         [], []
         when Opname.eq op opname_ImportGlobal ->
            ImportGlobal

       | [Token b], [{ bvars = []; bterm = import_arg_list }]
         when Opname.eq op opname_ImportFun ->
            let b = boolean_of_string b in
            let import_arg_list = List.map dest_import_arg (dest_xlist import_arg_list) in
               ImportFun (b, import_arg_list)

       | _ ->
            raise (RefineError ("dest_import_info", StringTermError ("not import_info", t)))

let make_import_info info =
   match info with
      ImportGlobal ->
         term_ImportGlobal
    | ImportFun (b, args) ->
         let b = string_of_boolean b in
         let args = mk_xlist_term (List.map make_import_arg args) in
         let params = [make_param (Token b)] in
         let op = mk_op opname_ImportFun params in
            mk_term op [mk_bterm [] args]

let term_Import = << Import[name:s]{'ty; 'info} >>
let opname_Import = opname_of_term term_Import

let dest_poly_import dest_ty t =
   let { term_op = op; term_terms = bterms } = dest_term t in
   let { op_name = op; op_params = params } = dest_op op in
   let params = dest_params params in
   let bterms = List.map dest_bterm bterms in
      match params, bterms with
         [String name],
         [{ bvars = []; bterm = ty };
          { bvars = []; bterm = info }]
         when Opname.eq op opname_Import ->
            let ty = dest_ty ty in
            let info = dest_import_info info in
               { import_name = name;
                 import_type = ty;
                 import_info = info
               }

       | _ ->
            raise (RefineError ("dest_poly_import", StringTermError ("not an import", t)))

let make_poly_import make_ty info =
   let { import_name = name;
         import_type = ty;
         import_info = info
       } = info
   in
   let ty = make_ty ty in
   let info = make_import_info info in
   let params = [make_param (String name)] in
   let op = mk_op opname_Import params in
      mk_term op [mk_bterm [] ty; mk_bterm [] info]

(*
 * For exports, we just keep the name and type.
 *)
let term_Export = << Export[name:s]{'ty} >>
let opname_Export = opname_of_term term_Export

let dest_poly_export dest_ty t =
   let { term_op = op; term_terms = bterms } = dest_term t in
   let { op_name = op; op_params = params } = dest_op op in
   let params = dest_params params in
   let bterms = List.map dest_bterm bterms in
      match params, bterms with
         [String name], [{ bvars = []; bterm = ty }]
         when Opname.eq op opname_Export ->
            let ty = dest_ty ty in
               { export_name = name;
                 export_type = ty
               }

       | _ ->
            raise (RefineError ("dest_poly_export", StringTermError ("not an export", t)))

let make_poly_export make_ty info =
   let { export_name = name;
         export_type = ty
       } = info
   in
   let ty = make_ty ty in
   let params = [make_param (String name)] in
   let op = mk_op opname_Export params in
      mk_term op [mk_bterm [] ty]

(************************************************************************
 * Globals.
 *)

(*
 * One-level destruction.
 *)
let id x = x

let dest_type_term (t : term) : term_ty =
   dest_poly_type id t

let dest_atom_term (a : term) : term_atom =
   dest_poly_atom id id a

let dest_exp_term (e : term) : term_exp =
   dest_poly_exp id id id e

(*
 * Full destruction.
 *)
let rec dest_type (t : term) : ty =
   dest_poly_type dest_type t

and dest_atom (a : term) : atom =
   dest_poly_atom dest_type dest_atom a

and dest_exp (e : term) : exp =
   dest_poly_exp dest_type dest_atom dest_exp e

(*
 * One-level make.
 *)
let make_type_term (t : term_ty) : term =
   make_poly_type id t

let make_atom_term (a : term_atom) : term =
   make_poly_atom id id a

let make_exp_term (e : term_exp) : term =
   make_poly_exp id id id e

(*
 * Full make.
 *)
let rec make_type (t : ty) : term =
   make_poly_type make_type t

and make_atom (a : atom) : term =
   make_poly_atom make_type make_atom a

and make_exp (e : exp) : term =
   make_poly_exp make_type make_atom make_exp e

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
