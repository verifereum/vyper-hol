Theory runtimeSymSrcBuiltinMisc
Ancestors
  runtimeSymSrcBuiltinData runtimeSymSrcGeneratorContracts
  runtimeSymSrcContext runtimeSymSrcEmission runtimeSymSrcInterfaces
  compileEnv builtinMisc builtinSimple
  emitHelper context loweringShapeDefs venomInst list stackPlanTypes

Theorem runtime_sym_blockhash:
  ~is_label_operand v /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_blockhash v s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  simp[compile_blockhash_def, comp_bind_def, comp_ignore_bind_def,
       emit_op_def, emit_void_def, fresh_id_def, fresh_var_def, emit_def,
       comp_return_def] >> rpt strip_tac >> gvs[] >>
  gvs[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND,
      EVERY_APPEND, runtime_sym_inst_def, mk_inst_def, is_label_operand_def] >>
  metis_tac[runtime_sym_nonlabel_reserved]
QED

Theorem runtime_sym_blobhash:
  ~is_label_operand v /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_blobhash v s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  simp[compile_blobhash_def] >> strip_tac >>
  drule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >> simp[]
QED

Theorem runtime_sym_as_wei_value_int:
  ~is_label_operand v /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_as_wei_value_int v scale signed s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  Cases_on `scale = 1` >> Cases_on `signed` >>
  simp[compile_as_wei_value_int_def, comp_bind_def, comp_ignore_bind_def,
       emit_op_def, emit_void_def, fresh_id_def, fresh_var_def, emit_def,
       comp_return_def] >> rpt strip_tac >> gvs[] >>
  gvs[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND,
      EVERY_APPEND, runtime_sym_inst_def, mk_inst_def, is_label_operand_def] >>
  metis_tac[runtime_sym_nonlabel_reserved]
QED

Theorem runtime_sym_as_wei_value_decimal:
  ~is_label_operand v /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_as_wei_value_decimal v scale divisor s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  Cases_on `scale = 1` >>
  simp[compile_as_wei_value_decimal_def, comp_bind_def, comp_ignore_bind_def,
       emit_op_def, emit_void_def, fresh_id_def, fresh_var_def, emit_def,
       comp_return_def] >> rpt strip_tac >> gvs[] >>
  gvs[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND,
      EVERY_APPEND, runtime_sym_inst_def, mk_inst_def, is_label_operand_def] >>
  metis_tac[runtime_sym_nonlabel_reserved]
QED

Theorem runtime_sym_ecrecover:
  EVERY (\a. ~is_label_operand a) [h;v;r;x] /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_ecrecover h v r x s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  simp[compile_ecrecover_def, compile_alloc_buffer_def,
       comp_bind_def, comp_ignore_bind_def,
       emit_op_def, emit_void_def, fresh_id_def, fresh_var_def, emit_def,
       comp_return_def] >> rpt strip_tac >> gvs[] >>
  gvs[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND,
      EVERY_APPEND, runtime_sym_inst_def, mk_inst_def, is_label_operand_def] >>
  metis_tac[runtime_sym_nonlabel_reserved]
QED

Theorem runtime_sym_ecadd_points:
  ~is_label_operand p /\ ~is_label_operand q /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_ecadd_points p q s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  simp[compile_ecadd_points_def, compile_alloc_buffer_def,
       comp_bind_def, comp_ignore_bind_def,
       emit_op_def, emit_void_def, fresh_id_def, fresh_var_def, emit_def,
       comp_return_def] >> rpt strip_tac >> gvs[] >>
  gvs[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND,
      EVERY_APPEND, runtime_sym_inst_def, mk_inst_def, is_label_operand_def] >>
  metis_tac[runtime_sym_nonlabel_reserved]
QED

Theorem runtime_sym_ecmul_point:
  ~is_label_operand p /\ ~is_label_operand q /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_ecmul_point p q s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  simp[compile_ecmul_point_def, compile_alloc_buffer_def,
       comp_bind_def, comp_ignore_bind_def,
       emit_op_def, emit_void_def, fresh_id_def, fresh_var_def, emit_def,
       comp_return_def] >> rpt strip_tac >> gvs[] >>
  gvs[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND,
      EVERY_APPEND, runtime_sym_inst_def, mk_inst_def, is_label_operand_def] >>
  metis_tac[runtime_sym_nonlabel_reserved]
QED

Theorem runtime_sym_floor:
  ~is_label_operand v /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_floor v divisor s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  simp[compile_floor_def, compile_select_def,
       comp_bind_def, comp_ignore_bind_def,
       emit_op_def, emit_void_def, fresh_id_def, fresh_var_def, emit_def,
       comp_return_def] >> rpt strip_tac >> gvs[] >>
  gvs[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND,
      EVERY_APPEND, runtime_sym_inst_def, mk_inst_def, is_label_operand_def] >>
  metis_tac[runtime_sym_nonlabel_reserved]
QED

Theorem runtime_sym_ceil:
  ~is_label_operand v /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_ceil v divisor s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  simp[compile_ceil_def, compile_select_def,
       comp_bind_def, comp_ignore_bind_def,
       emit_op_def, emit_void_def, fresh_id_def, fresh_var_def, emit_def,
       comp_return_def] >> rpt strip_tac >> gvs[] >>
  gvs[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND,
      EVERY_APPEND, runtime_sym_inst_def, mk_inst_def, is_label_operand_def] >>
  metis_tac[runtime_sym_nonlabel_reserved]
QED

Theorem runtime_sym_misc_clauses:
  runtime_sym_misc_clauses
Proof
  rewrite_tac[runtime_sym_misc_clauses_def] >>
  rpt conj_tac
  >- metis_tac[runtime_sym_blockhash]
  >- metis_tac[runtime_sym_blobhash]
  >- metis_tac[runtime_sym_ecrecover]
  >- metis_tac[runtime_sym_ecadd_points]
  >- metis_tac[runtime_sym_ecmul_point]
  >- metis_tac[runtime_sym_as_wei_value_int] >>
  metis_tac[runtime_sym_as_wei_value_decimal]
QED
