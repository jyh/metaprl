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

(*
 * sub_index.
 *)
declare ByteIndex
declare WordIndex

(*
 * sub_script.
 *)
declare IntIndex
declare RawIntIndex[precision:n, signed:t]

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

(*
 * subop.
 *)
declare subop{'block; 'value; 'index; 'script}

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

(*
 * Type definitions are the toplevel constructions.
 *)
declare TyLambda{v. 'ty['v]}
declare TyDefUnionList{'ty_list_list}
declare TyDefUnion{'ty}
declare TyDefLambda{'ty}
declare TyDefDTuple{'ty_var}

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

(*
 * Binary operators.
 *)
declare AndEnumOp[i:n]
declare OrEnumOp[i:n]
declare XorEnumOp[i:n]

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

(* Comparisons on native ints *)
declare EqRawIntOp[p:n, s:t]
declare NeqRawIntOp[p:n, s:t]
declare LtRawIntOp[p:n, s:t]
declare LeRawIntOp[p:n, s:t]
declare GtRawIntOp[p:n, s:t]
declare GeRawIntOp[p:n, s:t]
declare CmpRawIntOp[p:n, s:t]

(* Standard binary operations on floats *)
declare PlusFloatOp[p:n]
declare MinusFloatOp[p:n]
declare MulFloatOp[p:n]
declare DivFloatOp[p:n]
declare RemFloatOp[p:n]
declare MaxFloatOp[p:n]
declare MinFloatOp[p:n]

(* Comparisons on floats *)
declare EqFloatOp[p:n]
declare NeqFloatOp[p:n]
declare LtFloatOp[p:n]
declare LeFloatOp[p:n]
declare GtFloatOp[p:n]
declare GeFloatOp[p:n]
declare CmpFloatOp[p:n]

(*
 * Arctangent.  This computes arctan(y/x), where y is the first atom
 * and x is the second atom given.  Handles case when x = 0 correctly.
 *)
declare ATan2FloatOp[p:n]

(*
 * Power.  This computes x^y.
 *)
declare PowerFloatOp[p:n]

(*
 * Float hacking.
 * This sets the exponent field of the float.
 *)
declare LdExpFloatIntOp[p:n]

(* Pointer (in)equality.  Arguments must have the given type *)
declare EqEqOp{'ty}
declare NeqEqOp{'ty}

(*
 * Pointer arithmetic. The pointer in the first argument, and the
 * returned pointer should be infix pointers (which keep the base
 * pointer as well as a pointer to anywhere within the block).
 *)
declare PlusPointerOp[p:n, s:t]{'sub_block}

(*
 * A field is identified by a triple (frame, field, subfield).
 *)
declare FrameLabel[frame:t, field:t, subfield:t]

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

(*
 * Expressions.
 *)

(* Primitive operations *)
declare LetAtom{'ty; 'a; v. 'e['v]}

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

declare LetAlloc{'alloc_op; v. 'e['v]}

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

(* Assertions: label is a unique label identifying this assertion *)
declare Call[label:t]{'a; 'atop_opt_list; 'e}
declare Assert[label:t]{'pred; 'e}

(*
 * Initializers.
 *)
declare InitAtom{'a}
declare InitAlloc{'alloc_op}
declare InitRawData[p:n]{'int_array}
declare InitNames{'ty_var; 'names}
declare InitName{'v; 'v_opt}
declare InitTag{'ty_var; 'ty_list}


(*
 * Function definition.
 *)
declare lambda{v. 'e['v]}
declare FunDef{'ty; 'body}

(*
 * Program.
 *)
declare Global{'ty; 'init_exp}

(*
 * General debugging info.
 *)
declare FileFC
declare FileNaml
declare FileJava
declare FileAml

declare FileInfo[dir:s, name:s]{'file_class}

(*
 * For imports, we save information about the _original_
 * argument types so we can recover the original calling
 * convention.
 *)
declare ArgFunction
declare ArgPointer
declare ArgRawInt[p:n, s:t]
declare ArgRawFloat[p:n]

(*
 * On ImportFun, the bool is true iff this function
 * uses the stdargs convention.
 *)
declare ImportGlobal
declare ImportFun[b:t]{'import_arg_list}
declare Import{'name; 'ty; 'info}

(*
 * For exports, we just keep the name and type.
 *)
declare Export{'name; 'ty}

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
