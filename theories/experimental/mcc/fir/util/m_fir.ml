(*
 * Define the MCC FIR language.
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
extends M_int
extends M_rawint
extends M_rawfloat
extends M_set

open M_prec

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
declare NormalTuple
declare RawTuple
declare BoxTuple

doc docoff

dform normal_tuple_df : NormalTuple =
   bf["NormalTuple"]

dform raw_tuple_df : RawTuple =
   bf["RawTuple"]

dform box_tuple_df : BoxTuple =
   bf["BoxTuple"]

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
declare Mutable
declare Immutable
declare MutableDelayed
declare MutableVar{'v}

doc docoff

dform mutable_df : Mutable =
   bf["Mutable"]

dform immutable_df : Immutable =
   bf["Immutable"]

dform mutable_delayed_df : MutableDelayed =
   bf["MutableDelayed"]

dform mutable_var_df : MutableVar{'v} =
   bf["MutableVar("] slot{'v} bf[")"]

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
declare BlockSub
declare RawDataSub
declare TupleSub
declare RawTupleSub

doc docoff

dform block_sub_df : BlockSub =
   bf["BlockSub"]

dform raw_data_sub_df : RawDataSub =
   bf["RawDataSub"]

dform tuple_sub_df : TupleSub =
   bf["TupleSub"]

dform raw_tuple_sub_df : RawTupleSub =
   bf["RawTupleSub"]

(*
 * sub_index.
 *)
declare ByteIndex
declare WordIndex

doc docoff

dform byte_index_df : ByteIndex =
   bf["ByteIndex"]

dform word_index_df : WordIndex =
   bf["WordIndex"]

(*
 * sub_script.
 *)
declare IntIndex
declare RawIntIndex[precision:n, signed:t]

doc docoff

dform int_index_df : IntIndex =
   bf["IntIndex"]

dform raw_int_index_df : RawIntIndex[p:n, s:t] =
   bf["RawIntIndex"] M_rawint!precision[p:n, s:t]

(*
 * sub_value.
 *)
declare EnumSub[i:n]
declare IntSub
declare TagSub{'ty_var; 'ty_list}
declare PolySub
declare RawIntSub[precision:n, signed:t]
declare RawFloatSub[precision:n]
declare PointerInfixSub
declare BlockPointerSub
declare RawPointerSub
declare FunctionSub

doc docoff

dform enum_sub_df : EnumSub[i:n] =
   bf["EnumSub["] slot[i:n] bf["]"]

dform int_sub_df : IntSub =
   bf["IntSub"]

dform tag_sub_df : TagSub{'ty_var; 'ty_list} =
   bf["TagSub["] slot{'ty_var} `", " slot{'ty_list} bf["]"]

dform poly_sub_df : PolySub =
   bf["PolySub"]

dform raw_int_sub_df : RawIntSub[p:n, s:t] =
   bf["RawIntSub"] M_rawint!precision[p:n, s:t]

dform raw_float_sub_df : RawFloatSub[p:n] =
   bf["RawFloatSub"] M_rawfloat!precision[p:n]

dform pointer_infix_sub : PointerInfixSub =
   bf["PointerInfixSub"]

dform block_pointer_sub : BlockPointerSub =
   bf["BlockPointerSub"]

dform raw_pointer_sub : RawPointerSub =
   bf["RawPointerSub"]

dform function_sub : FunctionSub =
   bf["FunctionSub"]

(*
 * subop.
 *)
declare subop{'block; 'value; 'index; 'script}

doc docoff

dform subop_df : subop{'block; 'value; 'index; 'script} =
   szone pushm[0] bf["subop"] `"(" slot{'block} `","
   hspace slot{'value} `","
   hspace slot{'index} `","
   hspace slot{'script} `")" popm ezone

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
declare TyInt
declare TyEnum[i:n]
declare TyRawInt[precision:n, signed:t]
declare TyFloat[precision:n]
declare TyFun{'ty_args; 'ty_res}
declare TyUnion{'ty_var; 'ty_list; 'int_set}
declare TyTuple{'tuple_class; 'mutable_ty_list}
declare TyDTuple{'ty_var; 'mutable_ty_list}
declare TyTag{'ty_var; 'mutable_ty_list}
declare TyArray{'ty}
declare TyRawData
declare TyPointer{'sub_block}
declare TyFrame{'ty_var; 'ty_list}
declare TyVar{'ty_var}
declare TyApply{'ty_var; 'ty_list}
declare TyExists{v. 'ty['v]}
declare TyAll{v. 'ty['v]}
declare TyProject[i:n]{'v}
declare TyDelayed

declare TyMutable[m:t]{'ty}

doc docoff

dform ty_int_df : TyInt =
   Nuprl_font!mathbbZ

dform ty_enum_df : TyEnum[i:n] =
   Nuprl_font!mathbbN `"[" slot[i:n] `"]"

dform ty_raw_int_df : TyRawInt[p:n, s:t] =
   Nuprl_font!mathbbZ `":" M_rawint!precision[p:n, s:t]

dform ty_float_df : TyFloat[p:n] =
   Nuprl_font!mathbbR `":" M_rawfloat!precision[p:n]

dform ty_fun_df : parens :: "prec"[prec_fun] :: TyFun{'ty_args; 'ty_res} =
   `"(" display_list["*"]{'ty_args} `") " Nuprl_font!rightarrow slot{'ty_res}

dform ty_union_df : TyUnion{'ty_var; 'ty_list; 'int_set} =
   bf["union "] slot{'ty_var} `"(" display_list[","]{'ty_list} `": " slot{'int_set} `")"

dform ty_tuple_df : TyTuple{'tuple_class; 'ty_list} =
   bf["tuple["] slot{'tuple_class} bf["]("] display_list[","]{'ty_list} bf[")"]

dform ty_dtuple_df : TyDTuple{'ty_var; 'ty_list} =
   bf["deptuple "] slot{'ty_var} `"(" display_list[","]{'ty_list} `")"

dform ty_tag_df : TyTag{'ty_var; 'ty_list} =
   bf["tag "] slot{'ty_var} `"(" display_list[","]{'ty_list} `")"

dform ty_array_df : TyArray{'ty} =
   slot{'ty} bf[" array"]

dform ty_raw_data_df : TyRawData =
   bf["rawdata"]

dform ty_pointer_df : TyPointer{'sub_block} =
   bf["pointer["] slot{'sub_block} bf["]"]

dform ty_frame_df : TyFrame{'ty_var; 'ty_list} =
   bf["frame "] slot{'ty_var} `"(" display_list[","]{'ty_list} `")"

dform ty_var_df : TyVar{'ty_var} =
   slot{'ty_var}

dform ty_apply_df : TyApply{'ty_var; 'ty_list} =
   slot{'ty_var} `"(" display_list[","]{'ty_list} `")"

dform ty_exists_df : parens :: "prec"[prec_exists] :: TyExists{v. 'ty} =
   Nuprl_font!exists slot{'v} `"." slot{'ty}

dform ty_all_df : parens :: "prec"[prec_exists] :: TyAll{v. 'ty} =
   Nuprl_font!forall slot{'v} `"." slot{'ty}

dform ty_project_df : TyProject[i:n]{'v} =
   slot{'v} `"." slot[i:n]

dform ty_delayed_df : TyDelayed =
   bf["<delayed>"]

dform ty_mutable_df1 : TyMutable["true":t]{'ty} =
   bf["mutable "] slot{'ty}

dform ty_mutable_df2 : TyMutable["false":t]{'ty} =
   bf["immutable "] slot{'ty}

(*
 * A frame has a list of fields, each of which has a list of subfields.
 * The var list is a universal quantifier.
 *
 * The outer symbol table is indexed on the field names.  The list is
 * a list of subfields for that field --- certain fields (e.g. pointers)
 * must be broken into multiple subfields, such as pointers which become
 * a base/offset pair. The subfield tuple is (sf_name, sf_type, sf_size)
 *)
declare FrameSubfield[size:n]{'v; 'ty}
declare FrameField{'v; 'subfields}
declare FrameType{'fields}

doc docoff

dform frame_subfield_df : FrameSubfield[size:n]{'v; 'ty} =
   slot{'v} `" : " slot{'ty} bf["[size = "] slot[size:n] bf["]"]

dform frame_field_df : FrameField{'v; 'subfields} =
   szone pushm[0] pushm[3] slot{'v} `" { " display_list[";"]{'subfields} popm hspace `"}" popm ezone

dform frame_type_df : FrameType{'fields} =
   szone pushm[0] pushm[2] `"{ " display_list[";"]{'fields} popm `"}" popm ezone

(*
 * Type definitions are the toplevel constructions.
 *)
declare TyLambda{v. 'ty['v]}
declare TyDefUnionList{'ty_list_list}
declare TyDefUnion{'ty}
declare TyDefLambda{'ty}
declare TyDefDTuple{'ty_var}

doc docoff

declare display_Lambda1{'ty}
declare display_Lambda2{'ty}
declare display_Union{'ty_list_list}

dform display_Lambda1_df : display_Lambda1{TyLambda{v. 'ty}} =
   slot{'v} display_Lambda2{'ty}

dform display_Lambda2_df1 : display_Lambda2{TyLambda{v. 'ty}} =
   `", " slot{'v} display_Lambda2{'ty}

dform display_Lambda2_df2 : display_Lambda2{'ty} =
   `"." hspace slot{'ty}

dform ty_lambda_df1 : TyLambda{v. 'ty} =
   Nuprl_font!lambda display_Lambda1{TyLambda{v. 'ty}}

dform ty_def_union_list_df : parens :: "prec"[prec_union] :: TyDefUnionList{'ty_list_list} =
   szone pushm[0] display_Union{'ty_list_list} popm ezone

dform display_union_df1 : display_Union{nil} =
   `""

dform display_union_df2 : display_Union{cons{'ty_list; nil}} =
   display_list["*"]{'ty_list}

dform display_union_df3 : display_Union{cons{'ty_list1; cons{'ty_list2; 'ty_list_list}}} =
   display_list["*"]{'ty_list1} hspace `"+ " display_Union{cons{'ty_list2; 'ty_list_list}}

dform ty_def_union_df : TyDefUnion{'ty} =
   bf["union "] slot{'ty}

dform ty_def_lambda_df : TyDefLambda{'ty} =
   bf["Lambda "] slot{'ty}

dform ty_def_dtuple_df : TyDefDTuple{'ty_var} =
   bf["DTuple "] slot{'ty_var}

(************************************************************************
 * EXPRESSIONS                                                          *
 ************************************************************************)

(*
 * Unary operators.
 *)
declare NotEnumOp[i:n]
declare UMinusIntOp
declare NotIntOp
declare AbsIntOp

declare UMinusRawIntOp[p:n, s:t]
declare NotRawIntOp[p:n, s:t]
declare RawBitFieldOp[p:n, s:t, off:n, len:n]

declare UMinusFloatOp[p:n]
declare AbsFloatOp[p:n]
declare SinFloatOp[p:n]
declare CosFloatOp[p:n]
declare TanFloatOp[p:n]
declare ASinFloatOp[p:n]
declare ACosFloatOp[p:n]
declare ATanFloatOp[p:n]
declare SinHFloatOp[p:n]
declare CosHFloatOp[p:n]
declare TanHFloatOp[p:n]
declare ExpFloatOp[p:n]
declare LogFloatOp[p:n]
declare Log10FloatOp[p:n]
declare SqrtFloatOp[p:n]
declare CeilFloatOp[p:n]
declare FloorFloatOp[p:n]

declare IntOfFloatOp[p:n]
declare IntOfRawIntOp[p:n, s:t]
declare FloatOfIntOp[p:n]
declare FloatOfFloatOp[p1:n, p2:n]
declare FloatOfRawIntOp[fp:n, ip:n, s:t]
declare RawIntOfIntOp[p:n, s:t]
declare RawIntOfEnumOp[p:n, s:t, i:n]
declare RawIntOfFloatOp[ip:n, s:t, fp:n]
declare RawIntOfRawIntOp[p1:n, s1:t, p2:n, s2:t]
declare RawIntOfPointerOp[p:n, s:t]
declare PointerOfRawIntOp[p:n, s:t]
declare PointerOfBlockOp{'sub_block}
declare LengthOfBlockOp{'subop; 'ty}
declare DTupleOfDTupleOp{'ty_var; 'mutable_ty_list}
declare UnionOfUnionOp{'ty_var; 'ty_list; 'int_set1; 'int_set2}
declare RawDataOfFrameOp{'ty_var; 'ty_list}

doc docoff

dform not_enum_op_df : NotEnumOp[i:n] =
   bf["~["] slot[i:n] bf["]"]

dform uminus_int_op_df : UMinusIntOp =
   `"-"

dform not_int_op_df : NotIntOp =
   bf["lnot"]

dform abs_int_op_df : AbsIntOp =
   bf["abs"]

dform uminus_raw_int_op_df : UMinusRawIntOp[p:n, s:t] =
   bf["-"] M_rawint!precision[p:n, s:t]

dform not_raw_int_op_df : NotRawIntOp[p:n, s:t] =
   bf["~"] M_rawint!precision[p:n, s:t]

dform raw_bit_field_op_df : RawBitFieldOp[p:n, s:t, off:n, len:n] =
   bf["bitfield:"] M_rawint!precision[p:n, s:t] `"(" slot[off:n] `", " slot[len:n] `")"

dform uminus_float_op_df : UMinusFloatOp[p:n] =
   bf["-"] M_rawfloat!precision[p:n]

dform abs_float_op_df : AbsFloatOp[p:n] =
   bf["abs"] M_rawfloat!precision[p:n]

dform sin_float_op_df : SinFloatOp[p:n] =
   bf["sin"] M_rawfloat!precision[p:n]

dform cos_float_op_df : CosFloatOp[p:n] =
   bf["cos"] M_rawfloat!precision[p:n]

dform tan_float_op_df : TanFloatOp[p:n] =
   bf["tan"] M_rawfloat!precision[p:n]

dform asin_float_op_df : ASinFloatOp[p:n] =
   bf["asin"] M_rawfloat!precision[p:n]

dform acos_float_op_df : ACosFloatOp[p:n] =
   bf["acos"] M_rawfloat!precision[p:n]

dform atan_float_op_df : ATanFloatOp[p:n] =
   bf["atan"] M_rawfloat!precision[p:n]

dform sinh_float_op_df : SinHFloatOp[p:n] =
   bf["sinh"] M_rawfloat!precision[p:n]

dform cosh_float_op_df : CosHFloatOp[p:n] =
   bf["cosh"] M_rawfloat!precision[p:n]

dform tanh_float_op_df : TanHFloatOp[p:n] =
   bf["-"] M_rawfloat!precision[p:n]

dform exp_float_op_df : ExpFloatOp[p:n] =
   bf["exp"] M_rawfloat!precision[p:n]

dform log_float_op_df : LogFloatOp[p:n] =
   bf["log"] M_rawfloat!precision[p:n]

dform log10_float_op_df : Log10FloatOp[p:n] =
   bf["log10"] M_rawfloat!precision[p:n]

dform sqrt_float_op_df : SqrtFloatOp[p:n] =
   bf["sqrt"] M_rawfloat!precision[p:n]

dform ceil_float_op_df : CeilFloatOp[p:n] =
   bf["ceil"] M_rawfloat!precision[p:n]

dform floor_float_op_df : FloorFloatOp[p:n] =
   bf["floor"] M_rawfloat!precision[p:n]

dform int_of_float_op_df : IntOfFloatOp[p:n] =
   bf["int_of_float"] M_rawfloat!precision[p:n]

dform int_of_raw_int_op_df : IntOfRawIntOp[p:n, s:t] =
   bf["int_of_rawint"] M_rawint!precision[p:n, s:t]

dform float_of_int_op_df : FloatOfIntOp[p:n] =
   bf["float_of_int"] M_rawfloat!precision[p:n]

dform float_of_rawint_op_df : FloatOfRawIntOp[fp:n, ip:n, s:t] =
   bf["float_of_rawint"] M_rawfloat!precision[fp:n] M_rawint!precision[ip:n, s:t]

dform rawint_of_int_op_df : RawIntOfIntOp[p:n, s:t] =
   bf["rawint_of_int"] M_rawint!precision[p:n, s:t]

dform rawint_of_enum_op_df : RawIntOfEnumOp[p:n, s:t, i:n] =
   bf["rawint_of_enum"] M_rawint!precision[p:n, s:t] `":" slot[i:n]

dform rawint_of_float_op_df : RawIntOfFloatOp[ip:n, s:t, fp:n] =
   bf["rawint_of_float"] M_rawint!precision[ip:n, s:t] M_rawfloat!precision[fp:n]

dform rawint_of_rawint_op_df : RawIntOfRawIntOp[p1:n, s1:t, p2:n, s2:t] =
   bf["rawint_of_rawint"] M_rawint!precision[p1:n, s1:t] M_rawint!precision[p2:n, s2:t]

dform rawint_of_pointer_op_df : RawIntOfPointerOp[p:n, s:t] =
   bf["rawint_of_pointer"] M_rawint!precision[p:n, s:t]

dform pointer_of_rawint_op_df : PointerOfRawIntOp[p:n, s:t] =
   bf["pointer_of_rawint"] M_rawint!precision[p:n, s:t]

dform length_of_block_op_df : LengthOfBlockOp{'subop; 'ty} =
   bf["length_of_block"] `"(" slot{'subop} `", " slot{'ty} `")"

dform dtuple_of_dtuple_op_df : DTupleOfDTupleOp{'ty_var; 'ty_list} =
   bf["dtuple_of_dtuple"] `"(" slot{'ty_var} `", " slot{'ty_list} `")"

dform union_of_union_op_df : UnionOfUnionOp{'ty_var; 'ty_list; 'int_set1; 'int_set2} =
   szone pushm[3] bf["union_of_union"] `"(" slot{'ty_var} `","
   hspace slot{'ty_list} `","
   hspace slot{'int_set1} `","
   hspace slot{'int_set2} `")" popm ezone

dform raw_data_of_frame_op_df : RawDataOfFrameOp{'ty_var; 'ty_list} =
   bf["raw_data_of_frame"] `"(" slot{'ty_var} `", " display_list[","]{'ty_list} `")"

(*
 * Binary operators.
 *)
declare AndEnumOp[i:n]
declare OrEnumOp[i:n]
declare XorEnumOp[i:n]

doc docoff

declare enum_precision[i:n]

dform enum_precision_df : enum_precision[i:n] =
   `":enum" slot[i:n]

dform and_enum_op_df : AndEnumOp[i:n] =
   bf["&"] enum_precision[i:n]

dform or_enum_op_df : OrEnumOp[i:n] =
   bf["|"] enum_precision[i:n]

dform xor_enum_op_df : XorEnumOp[i:n] =
   bf["^"] enum_precision[i:n]

(* Standard binary operations on NAML ints *)
declare PlusIntOp
declare MinusIntOp
declare MulIntOp
declare DivIntOp
declare RemIntOp
declare LslIntOp
declare LsrIntOp
declare AsrIntOp
declare AndIntOp
declare OrIntOp
declare XorIntOp
declare MaxIntOp
declare MinIntOp

doc docoff

dform plus_int_op_df : PlusIntOp =
   bf["+"]

dform minus_int_op_df : MinusIntOp =
   bf["-"]

dform mul_int_op_df : MulIntOp =
   bf["*"]

dform div_int_op_df : DivIntOp =
   bf["/"]

dform rem_int_op_df : RemIntOp =
   bf["rem"]

dform lsl_int_op_df : LslIntOp =
   bf["<<"]

dform lsr_int_op_df : LsrIntOp =
   bf[">>>"]

dform asr_int_op_df : AsrIntOp =
   bf[">>"]

dform and_int_op_df : AndIntOp =
   bf["&"]

dform or_int_op_df : OrIntOp =
   bf["|"]

dform xor_int_op_df : XorIntOp =
   bf["^"]

dform max_int_op_df : MaxIntOp =
   bf["max"]

dform min_int_op_df : MinIntOp =
   bf["min"]

(*
 * Equality and comparison.
 *)
declare EqIntOp
declare NeqIntOp
declare LtIntOp
declare LeIntOp
declare GtIntOp
declare GeIntOp
declare CmpIntOp

doc docoff

dform eq_int_op_df : EqIntOp =
   bf["="]

dform neq_int_op_df : NeqIntOp =
   Nuprl_font!neq

dform lt_int_op_df : LtIntOp =
   bf["<"]

dform le_int_op_df : LeIntOp =
   Nuprl_font!le

dform gt_int_op_df : GtIntOp =
   bf[">"]

dform ge_int_op_df : GeIntOp =
   Nuprl_font!ge

dform cmp_int_op_df : CmpIntOp =
   bf["cmp"]

(*
 * Standard binary operations on native ints.  The precision is
 * the result precision; the inputs should match this precision.
 *)
declare PlusRawIntOp[p:n, s:t]
declare MinusRawIntOp[p:n, s:t]
declare MulRawIntOp[p:n, s:t]
declare DivRawIntOp[p:n, s:t]
declare RemRawIntOp[p:n, s:t]
declare SlRawIntOp[p:n, s:t]
declare SrRawIntOp[p:n, s:t]
declare AndRawIntOp[p:n, s:t]
declare OrRawIntOp[p:n, s:t]
declare XorRawIntOp[p:n, s:t]
declare MaxRawIntOp[p:n, s:t]
declare MinRawIntOp[p:n, s:t]

doc docoff

dform plus_raw_int_op_df : PlusRawIntOp[p:n, s:t] =
   bf["+"] M_rawint!precision[p:n, s:t]

dform minus_raw_int_op_df : MinusRawIntOp[p:n, s:t] =
   bf["-"] M_rawint!precision[p:n, s:t]

dform mul_raw_int_op_df : MulRawIntOp[p:n, s:t] =
   bf["*"] M_rawint!precision[p:n, s:t]

dform div_raw_int_op_df : DivRawIntOp[p:n, s:t] =
   bf["/"] M_rawint!precision[p:n, s:t]

dform rem_raw_int_op_df : RemRawIntOp[p:n, s:t] =
   bf["rem"] M_rawint!precision[p:n, s:t]

dform and_raw_int_op_df : AndRawIntOp[p:n, s:t] =
   bf["&"] M_rawint!precision[p:n, s:t]

dform or_raw_int_op_df : OrRawIntOp[p:n, s:t] =
   bf["|"] M_rawint!precision[p:n, s:t]

dform xor_raw_int_op_df : XorRawIntOp[p:n, s:t] =
   bf["^"] M_rawint!precision[p:n, s:t]

dform sl_raw_int_op_df : SlRawIntOp[p:n, s:t] =
   bf["<<"] M_rawint!precision[p:n, s:t]

dform sr_raw_int_op_df : SrRawIntOp[p:n, s:t] =
   bf[">>"] M_rawint!precision[p:n, s:t]

dform max_raw_int_op_df : MaxRawIntOp[p:n, s:t] =
   bf["max"] M_rawint!precision[p:n, s:t]

dform min_raw_int_op_df : MinRawIntOp[p:n, s:t] =
   bf["min"] M_rawint!precision[p:n, s:t]

(*
 * RawSetBitFieldOp (pre, signed, offset, length)
 *    See comments for RawBitFieldOp. This modifies the bitfield starting
 *    at bit <offset> and extending <length> bits.  There are two atoms:
 *       First atom is the integer containing the field.
 *       Second atom is the value to be set in the field.
 *    The resulting integer contains the revised field, with type
 *    ACRawInt (pre, signed)
 *)
declare RawSetBitFieldOp[p:n, s:t, off:n, len:n]

doc docoff

dform raw_set_bit_field_op : RawSetBitFieldOp[p:n, s:t, off:n, len:n] =
   bf["raw_set_bit_field"] M_rawint!precision[p:n, s:t] `"(" slot[off:n] `", " slot[len:n] `")"

(* Comparisons on native ints *)
declare EqRawIntOp[p:n, s:t]
declare NeqRawIntOp[p:n, s:t]
declare LtRawIntOp[p:n, s:t]
declare LeRawIntOp[p:n, s:t]
declare GtRawIntOp[p:n, s:t]
declare GeRawIntOp[p:n, s:t]
declare CmpRawIntOp[p:n, s:t]

doc docoff

dform eq_raw_int_op_df : EqRawIntOp[p:n, s:t] =
   bf["="] M_rawint!precision[p:n, s:t]

dform neq_raw_int_op_df : NeqRawIntOp[p:n, s:t] =
   Nuprl_font!neq M_rawint!precision[p:n, s:t]

dform lt_raw_int_op_df : LtRawIntOp[p:n, s:t] =
   bf["<"] M_rawint!precision[p:n, s:t]

dform le_raw_int_op_df : LeRawIntOp[p:n, s:t] =
   Nuprl_font!le M_rawint!precision[p:n, s:t]

dform gt_raw_int_op_df : GtRawIntOp[p:n, s:t] =
   bf[">"] M_rawint!precision[p:n, s:t]

dform ge_raw_int_op_df : GeRawIntOp[p:n, s:t] =
   Nuprl_font!ge M_rawint!precision[p:n, s:t]

dform cmp_raw_int_op_df : CmpRawIntOp[p:n, s:t] =
   bf["cmp"] M_rawint!precision[p:n, s:t]

(* Standard binary operations on floats *)
declare PlusFloatOp[p:n]
declare MinusFloatOp[p:n]
declare MulFloatOp[p:n]
declare DivFloatOp[p:n]
declare RemFloatOp[p:n]
declare MaxFloatOp[p:n]
declare MinFloatOp[p:n]

doc docoff

dform plus_float_op_df : PlusFloatOp[p:n] =
   bf["+"] M_rawfloat!precision[p:n]

dform minus_float_op_df : MinusFloatOp[p:n] =
   bf["-"] M_rawfloat!precision[p:n]

dform mul_float_op_df : MulFloatOp[p:n] =
   bf["*"] M_rawfloat!precision[p:n]

dform div_float_op_df : DivFloatOp[p:n] =
   bf["/"] M_rawfloat!precision[p:n]

dform rem_float_op_df : RemFloatOp[p:n] =
   bf["rem"] M_rawfloat!precision[p:n]

dform max_float_op_df : MaxFloatOp[p:n] =
   bf["max"] M_rawfloat!precision[p:n]

dform min_float_op_df : MinFloatOp[p:n] =
   bf["min"] M_rawfloat!precision[p:n]

(* Comparisons on floats *)
declare EqFloatOp[p:n]
declare NeqFloatOp[p:n]
declare LtFloatOp[p:n]
declare LeFloatOp[p:n]
declare GtFloatOp[p:n]
declare GeFloatOp[p:n]
declare CmpFloatOp[p:n]

doc docoff

dform eq_float_op_df : EqFloatOp[p:n] =
   bf["="] M_rawfloat!precision[p:n]

dform neq_float_op_df : NeqFloatOp[p:n] =
   Nuprl_font!neq M_rawfloat!precision[p:n]

dform lt_float_op_df : LtFloatOp[p:n] =
   bf["<"] M_rawfloat!precision[p:n]

dform le_float_op_df : LeFloatOp[p:n] =
   Nuprl_font!le M_rawfloat!precision[p:n]

dform gt_float_op_df : GtFloatOp[p:n] =
   bf[">"] M_rawfloat!precision[p:n]

dform ge_float_op_df : GeFloatOp[p:n] =
   Nuprl_font!ge M_rawfloat!precision[p:n]

dform cmp_float_op_df : CmpFloatOp[p:n] =
   bf["cmp"] M_rawfloat!precision[p:n]

(*
 * Arctangent.  This computes arctan(y/x), where y is the first atom
 * and x is the second atom given.  Handles case when x = 0 correctly.
 *)
declare ATan2FloatOp[p:n]

doc docoff

dform atan2_float_op_df : ATan2FloatOp[p:n] =
   bf["atan2"] M_rawfloat!precision[p:n]

(*
 * Power.  This computes x^y.
 *)
declare PowerFloatOp[p:n]

doc docoff

dform power_float_op_df : PowerFloatOp[p:n] =
   bf["power"] M_rawfloat!precision[p:n]

(*
 * Float hacking.
 * This sets the exponent field of the float.
 *)
declare LdExpFloatIntOp[p:n]

doc docoff

dform ld_exp_float_int_op_df : LdExpFloatIntOp[p:n] =
   bf["ldexp"] M_rawfloat!precision[p:n]

(* Pointer (in)equality.  Arguments must have the given type *)
declare EqEqOp{'ty}
declare NeqEqOp{'ty}

doc docoff

dform eq_eq_op_df : EqEqOp{'ty} =
   bf["==["] slot{'ty} bf["]"]

dform neq_eq_op_df : NeqEqOp{'ty} =
   Nuprl_font!neq bf["["] slot{'ty} bf["]"]

(*
 * Pointer arithmetic. The pointer in the first argument, and the
 * returned pointer should be infix pointers (which keep the base
 * pointer as well as a pointer to anywhere within the block).
 *)
declare PlusPointerOp[p:n, s:t]{'sub_block}

doc docoff

dform plus_pointer_op_df : PlusPointerOp[p:n, s:t]{'sub_block} =
   bf["+ptr"] M_rawint!precision[p:n, s:t] `"[" slot{'sub_block} `"]"

(*
 * A field is identified by a triple (frame, field, subfield).
 *)
declare FrameLabel[frame:t, field:t, subfield:t]

doc docoff

dform frame_label_df : FrameLabel[frame:t, field:t, subfield:t] =
   slot[frame:t] `"." slot[field:t] `"." slot[subfield:t]

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
declare AtomNil{'ty}
declare AtomInt{'i}
declare AtomEnum[n:n, i:n]
declare AtomRawInt{'i}
declare AtomFloat{'x}
declare AtomLabel{'frame_label; 'rawint}
declare AtomSizeof{'ty_var_list; 'rawint}
declare AtomConst[i:n]{'ty; 'ty_var}
declare AtomVar{'v}
declare AtomFun{'v}

   (* Polymorphism *)
declare AtomTyApply{'a; 'ty; 'ty_list}
declare AtomTyPack{'v; 'ty; 'ty_list}
declare AtomTyUnpack{'v}

   (* Arithmetic *)
declare AtomUnop{'op; 'a}
declare AtomBinop{'op; 'a1; 'a2}

doc docoff

dform atom_nil_df : AtomNil{'ty} =
   bf["nil["] slot{'ty} bf["]"]

dform atom_int_df : AtomInt{'i} =
   bf["int("] slot{'i} bf[")"]

dform atom_enum_df : AtomEnum[n:n, i:n] =
   bf["enum("] slot[i:n] bf[")"] enum_precision[n:n]

dform atom_raw_int_df : AtomRawInt{'i} =
   bf["rawint("] slot{'i} bf[")"]

dform atom_float_df : AtomFloat{'x} =
   bf["float("] slot{'x} bf[")"]

dform atom_label_df : AtomLabel{'label; 'i} =
   slot{'label} `":" slot{'i}

dform atom_sizeof_df : AtomSizeof{'ty_var_list; 'i} =
   bf["sizeof("] display_list[","]{'ty_var_list} `" = " slot{'i} bf[")"]

dform atom_const_df : AtomConst[i:n]{'ty; 'ty_var} =
   bf["const["] slot[i:n] bf["]("] slot{'ty_var} bf[") : "] slot{'ty}

dform atom_var_df : AtomVar{'v} =
   bf["var("] slot{'v} bf[")"]

dform atom_fun_df : AtomFun{'f} =
   bf["fun("] slot{'f} bf[")"]

dform atom_ty_apply_df : parens :: "prec"[prec_colon] :: AtomTyApply{'a; 'ty; 'ty_list} =
   slot{'a} bf["["] display_list[","]{'ty_list} bf["] :"] hspace slot{'ty}

dform atom_ty_pack_df : parens :: "prec"[prec_colon] :: AtomTyPack{'v; 'ty; 'ty_list} =
   bf["pack("] slot{'v} `"[" display_list[","]{'ty_list} `"]) :" hspace slot{'ty}

dform atom_ty_unpack_df : AtomTyUnpack{'v} =
   bf["unpack("] slot{'v} bf[")"]

dform atom_unop_df : AtomUnop{'op; 'a} =
   szone pushm[0] bf["unop("] slot{'op} `"," hspace slot{'a} bf[")"] popm ezone

dform atom_binop_df : AtomBinop{'op; 'a1; 'a2} =
   szone pushm[0] bf["binop("] slot{'op} `"," hspace slot{'a1} `"," hspace slot{'a2} bf[")"] popm ezone

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
declare AllocTuple{'tuple_class; 'ty; 'atom_list}
declare AllocUnion[i:n]{'ty; 'ty_var; 'atom_list}
declare AllocDTuple{'ty; 'ty_var; 'atom; 'atom_list}
declare AllocArray{'ty; 'atom_list}
declare AllocVArray{'ty; 'sub_index; 'atom1; 'atom2}
declare AllocMalloc{'ty; 'atom}
declare AllocFrame{'ty_var; 'ty_list}

doc docoff

dform alloc_tuple_df : AllocTuple{'tuple_class; 'ty; 'atom_list} =
   bf["AllocTuple["] slot{'tuple_class} bf["]("] display_list[","]{'atom_list} `") :" hspace slot{'ty}

dform alloc_union_df : AllocUnion[i:n]{'ty; 'ty_var; 'atom_list} =
   bf["AllocUnion["] slot{'ty_var} bf["]("] display_list[","]{'atom_list} `") :" hspace slot{'ty}

dform alloc_dtuple_df : AllocDTuple{'ty; 'ty_var; 'atom; 'atom_list} =
   bf["AllocDTuple["] slot{'ty_var} bf["]("] slot{'atom} bf["; "] display_list[","]{'atom_list} `") :" hspace slot{'ty}

dform alloc_array_df : AllocArray{'ty; 'atom_list} =
   bf["AllocArray("] display_list[","]{'atom_list} bf[") :"] hspace slot{'ty}

dform alloc_varray_df : AllocVArray{'ty; 'sub_index; 'atom1; 'atom2} =
   bf["AllocVarray["] slot{'sub_index} bf["]("] slot{'atom1} `", " slot{'atom2} bf[") :"] hspace slot{'ty}

dform alloc_malloc_df : AllocMalloc{'ty; 'atom} =
   bf["AllocMalloc("] slot{'atom} bf[") :"] hspace slot{'ty}

dform alloc_frame_df : AllocFrame{'ty_var; 'ty_list} =
   bf["AllocFrame("] slot{'ty_var} `"[" display_list[","]{'ty_list} `"])"

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
declare TailMigrate[i:n]{'a1; 'a2; 'a3; 'atom_list}
declare TailSpeculate{'a1; 'a2; 'atom_list}
declare TailAbort{'a1; 'a2}
declare TailCommit{'a1; 'a2; 'atom_list}

doc docoff

dform tail_migrate_df : TailMigrate[i:n]{'a1; 'a2; 'a3; 'atom_list} =
   bf["migrate["] slot[i:n] bf["]("] slot{'a1} `", " slot{'a2} `", " slot{'a3} `"; " display_list[","]{'atom_list} bf[")"]

dform tail_speculate_df : TailSpeculate{'a1; 'a2; 'atom_list} =
   bf["speculate("] slot{'a1} `", " slot{'a2} `"; " display_list[","]{'atom_list} bf[")"]

dform tail_abort_df : TailAbort{'a1; 'a2} =
   bf["abort("] slot{'a1} `", " slot{'a2} bf[")"]

dform tail_commit_df : TailCommit{'a1; 'a2; 'atom_list} =
   bf["commit("] slot{'a1} `", " slot{'a2} `"; " display_list[","]{'atom_list} bf[")"]

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
declare IsMutable{'a}
declare Reserve{'a1; 'a2}
declare BoundsCheck{'subop; 'a1; 'a2; 'a3}
declare ElementCheck{'ty; 'subop; 'a1; 'a2}

doc docoff

dform is_mutable_df : IsMutable{'a} =
   bf["IsMutable("] slot{'a} bf[")"]

dform reserve_df : Reserve{'a1; 'a2} =
   bf["Reserve("] slot{'a1} `", " slot{'a2} bf[")"]

dform bounds_check_df : BoundsCheck{'subop; 'a1; 'a2; 'a3} =
   bf["BoundsCheck["] slot{'subop} bf["]("] slot{'a1} `", " slot{'a2} `", " slot{'a3} bf[")"]

dform element_check_df : ElementCheck{'ty; 'subop; 'a1; 'a2} =
   bf["ElementCheck["] slot{'subop} bf["]("] slot{'a1} `", " slot{'a2} bf[") :"] hspace slot{'ty}


(*
 * Expressions.
 *)

(* Primitive operations *)
declare LetAtom{'ty; 'a; v. 'e['v]}

doc docoff

dform let_atom_df : LetAtom{'ty; 'a; v. 'e} =
   bf["let "] slot{'v} bf[" : "] slot{'ty} bf[" = "] slot{'a} bf[" in"] hspace slot{'e}

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
declare LetExt[f:s, b:t]{'ty; 'ty_fun; 'ty_list; 'atom_list; v. 'e['v]}
declare TailCall[label:t]{'a; 'atom_list}
declare SpecialCall[label:t]{'tailop}

doc docoff

dform let_ext_df : LetExt[f:s, b:t]{'ty; 'ty_fun; 'ty_list; 'atom_list; v. 'e} =
   bf["let "] slot{'v} bf[" : "] slot{'ty} bf[" = external("]
      slot[f:s] `", " slot[b:t] `" : " slot{'ty} `")[" display_list[","]{'ty_list}
     `"](" display_list[","]{'atom_list} bf[") in"] hspace slot{'e}

dform tail_call_df : TailCall[label:t]{'a; 'atom_list} =
   slot{'a} `"(" display_list[","]{'atom_list} `")"

dform special_call_df : SpecialCall[label:t]{'tailop} =
   bf["special["] slot[label:t] bf["] "] slot{'tailop}

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
declare Match{'a; 'cases}
declare MatchCase[label:t]{'set; 'e}

declare MatchDTuple{'a; 'cases}
declare MatchDTupleCase[label:t]{'atom_opt; 'e}

doc docoff

dform match_df : Match{'a; 'cases} =
   szone pushm[1] bf["match "] slot{'a} bf[" with"]
   'cases
   popm ezone

dform match_dtuple_df : MatchDTuple{'a; 'cases} =
   szone pushm[1] bf["match-dtuple "] slot{'a} bf[" with"]
   'cases
   popm ezone

dform match_case_df : MatchCase[label:t]{'set; 'e} =
   hspace szone pushm[3] bf["|["] slot[label:t] `"] " slot{'set} `" " Nuprl_font!rightarrow hspace slot{'e} popm ezone

dform match_dtuple_case_df : MatchDTupleCase[label:t]{'atom_opt; 'e} =
   hspace szone pushm[3] bf["|["] slot[label:t] `"] " slot{'atom_opt} `" " Nuprl_font!rightarrow hspace slot{'e} popm ezone

(* Allocation *)
declare LetAlloc{'alloc_op; v. 'e['v]}

doc docoff

dform let_alloc_df : LetAlloc{'alloc_op; v. 'e} =
   bf["let "] slot{'v} bf[" = "] slot{'alloc_op} bf[" in"] hspace slot{'e}

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
declare LetSubscript{'subop; 'ty; 'a1; 'a2; v. 'e['v]}
declare SetSubscript[label:t]{'subop; 'a1; 'a2; 'ty; 'a3; 'e}
declare LetGlobal[label:t]{'sub_value; 'ty; v. 'e['v]}
declare SetGlobal[label:t, global:t]{'sub_value; 'ty; 'a; 'e}
declare Memcpy[label:t]{'subop; 'a1; 'a2; 'a3; 'a4; 'a5; 'e}

doc docoff

dform let_subscript_df : LetSubscript{'subop; 'ty; 'a1; 'a2; v. 'e} =
   bf["let "] slot{'v} bf[" : "] slot{'ty} bf[" = "] slot{'a1} bf["["] slot{'a2} bf["] in"] hspace slot{'e}

dform set_subscript_df : SetSubscript[label:t]{'subop; 'a1; 'a2; 'ty; 'a3; 'e} =
   slot{'a1} bf["["] slot{'a2} bf["] : "] slot{'ty} `" " Nuprl_font!leftarrow `" " slot{'a3} bf[";"] hspace slot{'e}

dform let_global_df : LetGlobal[label:t]{'sub_value; 'ty; v. 'e} =
   bf["let global "] slot{'v} bf[" : "] slot{'ty} bf[" = "] slot[label:t] bf[" in"] hspace slot{'e}

dform set_global_df : SetGlobal[label:t, global:t]{'sub_value; 'ty; 'a; 'e} =
   bf["set global "] slot[global:t] `" " Nuprl_font!leftarrow `" " slot{'a} bf[";"] hspace slot{'e}

dform memcpy_df : Memcpy[label:t]{'subop; 'a1; 'a2; 'a3; 'a4; 'a5; 'e} =
   bf["memcpy("] slot{'a1} `", " slot{'a2} `", " slot{'a3} `", " slot{'a4} `", " slot{'a5} `");" hspace slot{'e}

(* Assertions: label is a unique label identifying this assertion *)
declare Call[label:t]{'a; 'atop_opt_list; 'e}
declare Assert[label:t]{'pred; 'e}

doc docoff

dform call_df : Call[label:t]{'a; 'atom_opt_list; 'e} =
   bf["call "] slot{'a} `"(" display_list[","]{'atom_opt_list} `");" hspace slot{'e}

dform assert_df : Assert[label:t]{'pred; 'e} =
   bf["assert "] slot{'pred} `";" hspace slot{'e}

(*
 * Initializers.
 *)
declare InitAtom{'a}
declare InitAlloc{'alloc_op}
declare InitRawData[p:n]{'int_array}
declare InitNames{'ty_var; 'names}
declare InitName{'v; 'v_opt}
declare InitTag{'ty_var; 'ty_list}

doc docoff

dform init_atom_df : InitAtom{'a} =
   bf["atom("] slot{'a} bf[")"]

dform init_alloc_df : InitAlloc{'alloc_op} =
   bf["alloc("] slot{'alloc_op} bf[")"]

dform init_rawdata_df : InitRawData[p:n]{'int_array} =
   szone pushm[0] pushm[3] bf["rawdata"] M_rawint!precision[p:n, "true":t] `" {" display_list[","]{'int_array} popm hspace `"}" popm ezone

dform init_names_df : InitNames{'ty_var; 'names} =
   bf["names("] slot{'ty_var} `", " display_list[","]{'names} bf[")"]

dform init_name_df : InitName{'v; 'v_opt} =
   bf["name("] slot{'v} `", " slot{'v_opt} bf[")"]

dform init_tag_df : InitTag{'ty_var; 'ty_list} =
   bf["tag("] slot{'ty_var} `"[" display_list[","]{'ty_list} `"])"


(*
 * Function definition.
 *)
declare lambda{v. 'e['v]}
declare FunDef{'ty; 'body}

doc docoff

dform lambda_df : lambda{v. 'e} =
   Nuprl_font!lambda slot{'v} `"." slot{'e}

dform fun_def_df : FunDef{'ty; 'body} =
   szone pushm[3] bf["fun["] slot{'ty} bf["] ="] hspace slot{'body} popm ezone

(*
 * Program.
 *)
declare Global{'ty; 'init_exp}

doc docoff

dform global_df : Global{'ty; 'init_exp} =
   szone pushm[3] bf["global["] slot{'ty} bf["] ="] hspace slot{'init_exp} popm ezone


(*
 * General debugging info.
 *)
declare FileFC
declare FileNaml
declare FileJava
declare FileAml

declare FileInfo[dir:s, name:s]{'file_class}

doc docoff

dform file_fc_df : FileFC =
   bf["FC"]

dform file_naml_df : FileNaml =
   bf["Naml"]

dform file_java_df : FileJava =
   bf["Java"]

dform file_aml_df : FileAml =
   bf["Aml"]

dform file_info_df : FileInfo[dir:s, name:s]{'file_class} =
   bf["file("] slot[dir:s] `", " slot[name:s] `", " slot{'file_class} bf[")"]


(*
 * For imports, we save information about the _original_
 * argument types so we can recover the original calling
 * convention.
 *)
declare ArgFunction
declare ArgPointer
declare ArgRawInt[p:n, s:t]
declare ArgRawFloat[p:n]

doc docoff

dform arg_function_df : ArgFunction =
   bf["fun"]

dform arg_pointer_df : ArgPointer =
   bf["ptr"]

dform arg_raw_int_df : ArgRawInt[p:n, s:t] =
   bf["rawint"] M_rawint!precision[p:n,s:t]

dform arg_raw_float_df : ArgRawFloat[p:n] =
   bf["rawfloat"] M_rawfloat!precision[p:n]

(*
 * On ImportFun, the bool is true iff this function
 * uses the stdargs convention.
 *)
declare ImportGlobal
declare ImportFun[b:t]{'import_arg_list}
declare Import{'name; 'ty; 'info}

doc docoff

dform import_global_df : ImportGlobal =
   bf["import-global"]

dform import_fun_df : ImportFun[b:t]{'import_arg_list} =
   bf["import-fun["] slot[b:t] bf["]("] display_list[","]{'import_arg_list} bf[")"]

dform import_df : Import{'name; 'ty; 'info} =
   bf["import "] slot{'name} bf[" : "] slot{'ty} bf[" ="] hspace slot{'info}

(*
 * For exports, we just keep the name and type.
 *)
declare Export{'name; 'ty}

doc docoff

dform export_df : Export{'name; 'ty} =
   bf["export "] slot{'name} bf[" : "] slot{'ty}

(*
 * This is all the info for a program.
type prog =
   { prog_file    : file_info;            (* Source path/filename *)
     prog_import  : import SymbolTable.t; (* Imports are external definitions *)
     prog_export  : export SymbolTable.t; (* Exports are global values *)
     prog_types   : tydef  SymbolTable.t; (* List of type definitions *)
     prog_frames  : frame  SymbolTable.t; (* List of frame definitions *)
     prog_names   : ty     SymbolTable.t; (* Names for some of the types *)
     prog_globals : global SymbolTable.t; (* List of program globals *)
     prog_funs    : fundef SymbolTable.t; (* List of functions *)
   }
 *)

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
