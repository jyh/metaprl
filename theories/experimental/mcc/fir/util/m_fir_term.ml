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
open Refiner.Refiner.RefineError

open Lm_symbol

open Fir

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

(*
 * sub_index.
 *)
let term_ByteIndex = << ByteIndex >>
let opname_ByteIndex = opname_of_term term_ByteIndex
let term_WordIndex = << WordIndex >>
let opname_WordIndex = opname_of_term term_WordIndex

(*
 * sub_script.
 *)
let term_IntIndex = << IntIndex >>
let opname_IntIndex = opname_of_term term_IntIndex
let term_RawIntIndex = << RawIntIndex[precision:n, signed:t] >>
let opname_RawIntIndex = opname_of_term term_RawIntIndex

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
 * subop.
 *)
let term_subop = << subop{'block; 'value; 'index; 'script} >>
let opname_subop = opname_of_term term_subop

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

let term_TyMutable = << TyMutable[m:t]{'ty} >>
let opname_TyMutable = opname_of_term term_TyMutable

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

(*
 * Type definitions are the toplevel constructions.
 *)
let term_TyLambda = << TyLambda{v. 'ty['v]} >>
let opname_TyLambda = opname_of_term term_TyLambda
let term_TyDefUnionList = << TyDefUnionList{'ty_list_list} >>
let opname_TyDefUnionList = opname_of_term term_TyDefUnionList
let term_TyDefUnion = << TyDefUnion{'ty} >>
let opname_TyDefUnion = opname_of_term term_TyDefUnion
let term_TyDefLambda = << TyDefLambda{'ty} >>
let opname_TyDefLambda = opname_of_term term_TyDefLambda
let term_TyDefDTuple = << TyDefDTuple{'ty_var} >>
let opname_TyDefDTuple = opname_of_term term_TyDefDTuple

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

(*
 * A field is identified by a triple (frame, field, subfield).
 *)
let term_FrameLabel = << FrameLabel[frame:t, field:t, subfield:t] >>
let opname_FrameLabel = opname_of_term term_FrameLabel

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
let term_Match = << Match{'a; 'cases} >>
let opname_Match = opname_of_term term_Match
let term_MatchCase = << MatchCase[label:t]{'set; 'e} >>
let opname_MatchCase = opname_of_term term_MatchCase

let term_MatchDTuple = << MatchDTuple{'a; 'cases} >>
let opname_MatchDTuple = opname_of_term term_MatchDTuple
let term_MatchDTupleCase = << MatchDTupleCase[label:t]{'atom_opt; 'e} >>
let opname_MatchDTupleCase = opname_of_term term_MatchDTupleCase

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


(*
 * Function definition.
 *)
let term_lambda = << lambda{v. 'e['v]} >>
let opname_lambda = opname_of_term term_lambda
let term_FunDef = << FunDef{'ty; 'body} >>
let opname_FunDef = opname_of_term term_FunDef

(*
 * Program.
 *)
let term_Global = << Global{'ty; 'init_exp} >>
let opname_Global = opname_of_term term_Global

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

let term_FileInfo = << FileInfo[dir:s, name:s]{'file_class} >>
let opname_FileInfo = opname_of_term term_FileInfo

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

(*
 * On ImportFun, the bool is true iff this function
 * uses the stdargs convention.
 *)
let term_ImportGlobal = << ImportGlobal >>
let opname_ImportGlobal = opname_of_term term_ImportGlobal
let term_ImportFun = << ImportFun[b:t]{'import_arg_list} >>
let opname_ImportFun = opname_of_term term_ImportFun
let term_Import = << Import{'name; 'ty; 'info} >>
let opname_Import = opname_of_term term_Import

(*
 * For exports, we just keep the name and type.
 *)
let term_Export = << Export{'name; 'ty} >>
let opname_Export = opname_of_term term_Export

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
