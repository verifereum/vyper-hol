(* Source/compiler boundaries for the calldata slice memory proof. *)
Theory bodyMemBiCalldataSliceFacts
Ancestors
  exprSimCalldataSlice exprSimMemoryRead bodyMemoryPreds
  vyperTyping vyperInterpreter vyperValueOperation vyperTypeSystem
  exprLowering exprLoweringProps builtinSimple emitHelper compileEnv
  loweringSlice context fragExec emitHelperProps freshWrites exprSimHypsDefs
  exprBopLowering list builtinBytes vyperContext allocLimits
  vyperAST vyperState vyperValue venomInst venomState

(* Also local in exprSimCalldataSlice: dispatch prerequisite. *)
Theorem calldata_slice_memory_bytes:
  type_memory_bytes cenv (BaseT (BytesT (Dynamic n))) =
    32 + 32 * word_size n
Proof
  simp[type_memory_bytes_def, vfmConstantsTheory.word_size_def]
QED

Theorem calldata_slice_lowered_value_type:
  lowered_value_type cenv (Builtin (BaseT (BytesT (Dynamic n)))
    (CalldataSlice n) [e]) = BaseT (BytesT (Dynamic n))
Proof
  simp[lowered_value_type_def, expr_type_def]
QED

Theorem calldata_slice_allocation_limit:
  expr_body_pre cenv cx env (Builtin ann (CalldataSlice n) args) es ==>
  32 + 32 * word_size n < 2 ** 64
Proof
  simp[expr_body_pre_def, Once alloc_limits_expr_def]
QED

(* Extension consequence of local slice_bounds_shape in
   exprSimCalldataSliceScript.sml. *)
Theorem calldata_slice_bounds_extends:
  compile_assert_slice_bounds a n limit sa = ((),sb) ==>
  inst_extends sa sb
Proof
  simp[compile_assert_slice_bounds_def, comp_bind_def, comp_ignore_bind_def,
       emit_op_def, emit_void_def, fresh_id_def, fresh_var_def,
       emit_def, comp_return_def] >> strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def, rich_listTheory.DROP_APPEND1]
QED

Theorem calldata_slice_after_alloc_extends:
  emit_op ADD [buf_op; Lit 32w] sa = (data,s1) /\
  emit_op CALLDATASIZE [] s1 = (len,s2) /\
  compile_assert_slice_bounds start num len s2 = ((),s3) /\
  emit_void CALLDATACOPY [data; start; num] s3 = ((),s4) /\
  emit_void MSTORE [buf_op; num] s4 = ((),sb) ==>
  inst_extends sa sb
Proof
  strip_tac >>
  imp_res_tac inst_extends_emit_op >>
  imp_res_tac inst_extends_emit_void >>
  drule calldata_slice_bounds_extends >> strip_tac >>
  metis_tac[inst_extends_trans]
QED

Theorem calldata_slice_allocation_split:
  emit_op CALLDATASIZE [] sa = (len,s1) /\
  compile_assert_slice_bounds start num len s1 = ((),s2) /\
  compile_alloc_buffer sz s2 = (buf,s3) /\
  emit_op ADD [buf.buf_operand; Lit 32w] s3 = (data,s4) /\
  emit_void CALLDATACOPY [data; start; num] s4 = ((),s5) /\
  emit_void MSTORE [buf.buf_operand; num] s5 = ((),sb) ==>
  emitted_insts sa sb = emitted_insts sa s1 ++ emitted_insts s1 s2 ++
    emitted_insts s2 s3 ++ emitted_insts s3 sb /\
  s1.cs_next_var = sa.cs_next_var + 1 /\
  s2.cs_next_id = sa.cs_next_id + 7 /\ s2.cs_next_var = sa.cs_next_var + 6 /\
  s3.cs_next_var = sa.cs_next_var + 7
Proof
  simp[emit_op_def, emit_void_def, compile_assert_slice_bounds_def,
       compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def,
       fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, DROP_APPEND, DROP_LENGTH_TOO_LONG]
QED
