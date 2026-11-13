Theory runtimeSymSrcBuiltinByteSimple
Ancestors
  runtimeSymSrcBuiltinData runtimeSymSrcContext runtimeSymSrcEmission
  runtimeSymSrcInterfaces builtinBytes builtinSimple context compileEnv
  emitHelper loweringShapeDefs venomInst list stackPlanTypes

Theorem runtime_sym_builtin_calldatasize:
  EVERY runtime_sym_inst (state_insts s) /\
  compile_builtin_calldatasize s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  simp[compile_builtin_calldatasize_def] >> strip_tac >>
  drule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >> simp[]
QED

Theorem runtime_sym_builtin_empty_prim:
  EVERY runtime_sym_inst (state_insts s) /\
  compile_builtin_empty_prim s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  simp[compile_builtin_empty_prim_def, comp_return_def] >>
  rpt strip_tac >> gvs[is_label_operand_def]
QED

Theorem runtime_sym_builtin_len:
  ~is_label_operand p /\ (!b. imm = SOME b ==> ~is_label_operand b) /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_builtin_len ctor imm p loc s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  simp[compile_builtin_len_def] >> metis_tac[runtime_sym_ptr_load]
QED

Theorem runtime_sym_builtin_min:
  ~is_label_operand a /\ ~is_label_operand b /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_builtin_min a b unsigned s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  Cases_on `unsigned` >>
  simp[compile_builtin_min_def, compile_select_def, comp_bind_def,
       comp_ignore_bind_def, emit_op_def, fresh_id_def, fresh_var_def,
       emit_def, comp_return_def] >> rpt strip_tac >> gvs[] >>
  gvs[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND,
      EVERY_APPEND, runtime_sym_inst_def, mk_inst_def, is_label_operand_def] >>
  metis_tac[runtime_sym_nonlabel_reserved]
QED

Theorem runtime_sym_builtin_max:
  ~is_label_operand a /\ ~is_label_operand b /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_builtin_max a b unsigned s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  Cases_on `unsigned` >>
  simp[compile_builtin_max_def, compile_select_def, comp_bind_def,
       comp_ignore_bind_def, emit_op_def, fresh_id_def, fresh_var_def,
       emit_def, comp_return_def] >> rpt strip_tac >> gvs[] >>
  gvs[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND,
      EVERY_APPEND, runtime_sym_inst_def, mk_inst_def, is_label_operand_def] >>
  metis_tac[runtime_sym_nonlabel_reserved]
QED

Theorem runtime_sym_builtin_abs:
  ~is_label_operand v /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_builtin_abs v s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  simp[compile_builtin_abs_def, compile_select_def, comp_bind_def,
       comp_ignore_bind_def, emit_op_def, emit_void_def, fresh_id_def,
       fresh_var_def, emit_def, comp_return_def] >> rpt strip_tac >> gvs[] >>
  gvs[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND,
      EVERY_APPEND, runtime_sym_inst_def, mk_inst_def, is_label_operand_def] >>
  metis_tac[runtime_sym_nonlabel_reserved]
QED

Theorem runtime_sym_zero_words:
  !n p s u s'. ~is_label_operand p /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_zero_words p n s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  Induct >> simp[compile_zero_words_def, comp_return_def,
    comp_bind_def, comp_ignore_bind_def] >> rpt gen_tac >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >>
  simp[is_label_operand_def] >> strip_tac >>
  drule_at (Pat `emit_void _ _ _ = _`) runtime_sym_emit_void >>
  simp[is_label_operand_def]
QED
