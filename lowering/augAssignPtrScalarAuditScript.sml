(* Scalar-result provenance audit. References below are definition names in
   defs/exprLoweringScript.sml unless another file is named. This is a source
   inventory, NOT a semantic endpoint/dominance theorem.

   Available typing boundary: body_stmt_ptr_ok supplies type_stmt and
   expr_sim_inv; expr_body_pre supplies well_typed_expr, byte_widths_expr,
   alloc_limits_expr and call_evaluation_safe. stmt_exprs_ok supplies allocation
   and width restrictions, NOT a provenance invariant. body_inv fixes function
   metadata to build_func_info/build_func_return_type and struct metadata to
   make_struct_fields_map; expr_sim_inv fixes local declared types to
   ce_var_type and their representation to PtrVar. No assumption on arbitrary
   ghost provenance was present in the pre-merge ptr_val_ok interface. The
   strengthened word post now explicitly requires op_prov NONE, so this
   historical source inventory is not a remaining cleanliness obstruction.

   compile_expr_body (2935-3029), exhaustive constructor partition:
   Literal: compile_literal_vv; word literals are Lit, complex literals are
     LocatedValue and loaded if consumed as words. well_typed_literal excludes
     a complex literal carrying a scalar annotation.
   Name: LocatedValue at expression type, then unwrap_value loads; typing is
     FLOOKUP env.var_types, tied to ce_var_type by expr_sim_inv.
   IfExp: ASSIGN of each arm into shared result variable. For word result,
     compile_ifexp_arm unwraps the arm, no materialization buffer is returned.
     well_typed_expr requires both arm expression types equal result type.
     Internal-call arm actual declared type still needs metadata/widening lemma.
   Special AddMod/MulMod/PowMod256 Name forms: name unwrap loads, then
     ADDMOD/MULMOD/Exp respectively (compile_*_names).
   Builtin/TypeBuiltin: inventories below.
   Subscript/Attribute: always LocatedValue at result annotation, hence a word
     consumer loads; place_type/layout correctness is separate from clearing.
   StructLit: LocatedValue; well_typed_expr forces StructT, not a word.
   FlagMember: Lit (2 ** flag_id), no variable provenance.
   TopLevelName: LocatedValue for storage/transient/code; word unwrap loads.
     Missing module entry produces INVALID and Lit 0.
   Call: see below.
   Pop: LocatedValue at annotation, so word unwrap loads irrespective of place.

   compile_builtin_dispatch_body (3032-3307), exhaustive builtin partition:
   Bop: array membership returns booleans via comparisons/ASSIGN; bytestring
     equality hashes then EQ/ISZERO. Ordinary compile_binop is scalar recursive
     flow: ADD/SUB may propagate provenance; all other result arithmetic clears
     it, except forwarding helper paths must inherit operand cleanliness.
     Min/Max use compile_select (builtinSimple), final XOR, not pointer select.
     Exp ends with Exp even for exponents 0 and 1 (compile_safe_pow).
   Not: ISZERO or NOT/XOR (compile_invert); Neg: SUB of 0 and operand;
   Abs: compile_builtin_abs ends compile_select/XOR.
   Env: compile_env_var returns fresh environment opcode (PrevHash uses
     BLOCKHASH after NUMBER/SUB); none is PARAM or allocation.
   Acc: balance/codesize/codehash are scalar opcode outputs; Code is located
     buffer, excluded as scalar by well_typed_builtin_app.
   Keccak256/Sha256: SHA3 or precompile result load; never returns input buffer.
   CalldataLen: CALLDATASIZE. CalldataSlice: located buffer.
   Len: compile_ptr_load. BlockHash/BlobHash: BLOCKHASH/BLOBHASH.
   AddMod/MulMod: ADDMOD/MULMOD; Ceil/Floor: arithmetic/branch result,
     operand cleanliness needed wherever an input is forwarded.
   PowMod256: Exp. ECRecover: output MLOAD; ECAdd/ECMul: located buffers.
   Concat/Slice/Uint2Str: located buffers. MethodId: literal result via
     compile_literal_vv or runtime fixed-byte scalar vs located bytestring.
   AsWeiValue: integer scale=1 forwards input (builtinMisc 222), otherwise MUL;
     decimal ends Div. Source type comes from expr_type of argument, not ty.
   MakeArray NONE/SOME: located tuple/array buffer. well_typed_builtin_app
     must exclude word annotations for each buffer-producing builtin.

   compile_type_builtin_dispatch_body (3309-3405), exhaustive partition:
   Convert: well_typed_expr forces vv_ty=target_ty, singleton args and
     valid_conversion source target. With well-formed source widths, word
     targets admit only word or bytestring sources; valid_conversion alone
     only excludes aggregate source constructors (see checked shape lemma).
     Arbitrary ConvIdentity fallback on aggregates is NOT
     reachable under valid_conversion. Integer/bytesM/flag casts may forward
     already-scalar operand; they do not clear provenance themselves.
     Bytestring->word uses load_bytestring_as_word (MLOAD length, ADD data,
     MLOAD data, SAR/SHR); zero-capacity source returns Lit 0 before data load.
     Widen-copy only when both source and target are bytestrings (not words).
     Flag target only accepts uint256, so ConvToFlag's return-v case is scalar.
   Empty: Lit 0 for word target, otherwise LocatedValue buffer; vv_ty=target.
   MaxValue/MinValue/Epsilon: Lit bounds/1, vv_ty=target.
   Extract32: data MLOAD then compile_clamp_basetype may forward loaded scalar.
   AbiEncode: located buffer; type_builtin_result_ok forces dynamic Bytes.
   AbiDecode: located decoder output buffer; result_ty=target_ty. A word
     consumer unwraps via MLOAD, NOT via forwarding decoded buffer.

   compile_call (2626-2800), exhaustive target partition:
   IntCall: actual VyperValue type is ce_func_return_type, NOT ret_ty. With
     returns_count>0, INVOKE outputs are stored into return buffer and returned
     LocatedValue; unwrap of a declared word loads. With buffer-only return,
     LocatedValue likewise. No-buffer void path returns Lit 0. The NONE branch
     with returns_count>0 is structurally unreachable after allocation. Need
     body_inv + env_consistent fn_sigs + well_typed_expr type_widens_to to show
     that a word annotation cannot receive a nonword call_ty; do NOT assume
     ce_func_return_type equals annotation (widening is allowed).
   ExtCall: LocatedValue result if ABI size nonzero, so scalar result loads;
     zero-size path StackValue, excluded for well-formed scalar return by ABI
     size facts. Default operands are typed by return_type and materialized
     for nonwords (compile_ext_call_kwarg); default join must retain scalar
     cleanliness, not infer it from empty taint.
   Send: Lit 0 after CALL/ASSERT (or INVALID).
   RawCallTarget/RawCallCalldataTarget: maxout=0 StackValue CALL success or
     Lit, maxout>0 LocatedValue (SETFMP suffix in calldata variant).
   RawLog/RawRevert/SelfDestruct: INVALID then Lit 0 in this compiler.
   CreateTarget: compile_create_call returns create opcode result/address.

   Audit outcome: no concrete well-typed pointer-forwarding witness found.
   Unproved obligations are recursive scalar flow plus declared-type/annotation
   compatibility for calls, and same-path execution/transport. This inventory
   must not be mistaken for a proof of the missing universal invariant.
*)
Theory augAssignPtrScalarAudit
Ancestors
  augAssignPtrProvenanceProbe vyperTypeSystem ptrDiscipline venomInst finite_map compileEnv exprLowering

Theorem non_propagating_result_has_no_provenance:
  opc <> ALLOCA /\ opc <> DALLOCA /\ opc <> PARAM /\
  opc <> ADD /\ opc <> SUB /\ opc <> ASSIGN ==>
  op_prov (step_prov PG G (mk_inst id opc args [tmp]) u) (Var tmp) = NONE
Proof
  simp[step_prov_def, out_prov_def, set_prov_def, mk_inst_def,
       op_prov_def, FLOOKUP_DRESTRICT]
QED

Theorem valid_flag_conversion_source:
  valid_conversion src (FlagT nsid) <=> src = BaseT (UintT 256)
Proof
  Cases_on `src` >> simp[valid_conversion_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> simp[valid_conversion_def]
QED

(* Source shape is independent of width validity. In particular, converting
   bytes33 to bool passes valid_conversion alone, but bytes33 is not a word
   according to is_word_type. well_formed_type is needed for the stronger
   representation classification; do not drop it in a future induction. *)
Theorem valid_conversion_source_shape:
  valid_conversion src dst ==>
  (?bt. src = BaseT bt) \/ (?nsid. src = FlagT nsid)
Proof
  Cases_on `src` >> simp[] >>
  Cases_on `dst` >> simp[valid_conversion_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> simp[valid_conversion_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >> simp[valid_conversion_def]
QED

Theorem zero_capacity_word_convert_is_literal:
  is_bytestring_type (expr_type e) /\ is_word_type dst /\
  (lowered_value_type cenv e = BaseT (BytesT (Dynamic 0)) \/
   lowered_value_type cenv e = BaseT (StringT 0)) /\
  lower_value cfn cenv (expr_type e) e st = (v, st1) ==>
  compile_type_builtin_dispatch_body cfn cenv vv_ty ty Convert dst [e] st =
    (StackValue vv_ty (Lit 0w), st1)
Proof
  simp[compile_type_builtin_dispatch_body_def]
QED
