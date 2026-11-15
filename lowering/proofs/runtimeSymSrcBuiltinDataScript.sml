Theory runtimeSymSrcBuiltinData
Ancestors
  runtimeSymSrcContext runtimeSymSrcInterfaces runtimeSymSrcEmission builtinBytes builtinHashing
  builtinMisc builtinSimple builtinStrings exprLowering compileEnv context
  emitHelper loweringShapeDefs venomInst list stackPlanTypes


Theorem runtime_sym_assert_slice_bounds:
  EVERY (\x. ~is_label_operand x) [start;len;src] /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_assert_slice_bounds start len src s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  simp[compile_assert_slice_bounds_def, comp_bind_def, comp_ignore_bind_def,
       emit_op_def, emit_void_def, fresh_id_def, fresh_var_def, emit_def,
       comp_return_def] >> rpt strip_tac >> gvs[] >>
  gvs[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND,
      EVERY_APPEND, runtime_sym_inst_def, mk_inst_def, is_label_operand_def] >>
  metis_tac[runtime_sym_nonlabel_reserved]
QED

Theorem runtime_sym_bytestring_src:
  ~is_label_operand p /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_bytestring_src p s = ((len,data),s') ==>
  EVERY runtime_sym_inst (state_insts s') /\
  ~is_label_operand len /\ ~is_label_operand data
Proof
  simp[compile_bytestring_src_def, comp_bind_def, comp_ignore_bind_def,
       emit_op_def, fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  rpt strip_tac >> gvs[] >>
  gvs[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND,
      EVERY_APPEND, runtime_sym_inst_def, mk_inst_def, is_label_operand_def] >>
  metis_tac[runtime_sym_nonlabel_reserved]
QED

Theorem runtime_sym_keccak256_bytes:
  ~is_label_operand p /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_keccak256_bytes p s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  simp[compile_keccak256_bytes_def, comp_bind_def, comp_ignore_bind_def,
       emit_op_def, fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  rpt strip_tac >> gvs[] >>
  gvs[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND,
      EVERY_APPEND, runtime_sym_inst_def, mk_inst_def, is_label_operand_def] >>
  metis_tac[runtime_sym_nonlabel_reserved]
QED
