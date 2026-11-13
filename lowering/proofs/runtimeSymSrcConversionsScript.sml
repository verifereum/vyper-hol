Theory runtimeSymSrcConversions
Ancestors
  runtimeSymSrcEmission runtimeSymSrcInterfaces runtimeSymSrcContextValues
  exprLowering compileEnv emitHelper loweringShapeDefs venomInst list stackPlanTypes

Theorem runtime_sym_int_clamp:
  ~is_label_operand v /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_int_clamp sign bits v s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  Cases_on `sign` >>
  simp[compile_int_clamp_def, comp_bind_def, comp_ignore_bind_def,
       emit_op_def, emit_void_def, fresh_id_def, fresh_var_def,
       emit_def, comp_return_def] >> strip_tac >> gvs[] >>
  gvs[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND,
      EVERY_APPEND, runtime_sym_inst_def, mk_inst_def, is_label_operand_def] >>
  simp[runtime_sym_nonlabel_reserved]
QED

Theorem runtime_sym_type_convert:
  ~is_label_operand v /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_type_convert v cv s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  Cases_on `cv` >> simp[compile_type_convert_def] >>
  rpt IF_CASES_TAC >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, emit_void_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt (pairarg_tac >> simp[comp_return_def]) >> strip_tac >> gvs[] >>
  gvs[COND_RAND, COND_RATOR, COND_EXPAND, AllCaseEqs(), comp_return_def] >>
  rpt (qpat_x_assum `load_bytestring_as_word _ _ _ = _`
    (mp_then (Pat `load_bytestring_as_word _ _ _ = _`)
      mp_tac runtime_sym_load_bytestring_as_word) >> simp[] >> strip_tac) >>
  gvs[comp_bind_def, comp_ignore_bind_def, emit_op_def, emit_void_def,
      fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  rpt (qpat_x_assum `compile_int_clamp _ _ _ _ = _`
    (mp_then (Pat `compile_int_clamp _ _ _ _ = _`)
      mp_tac runtime_sym_int_clamp) >>
    simp[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND,
         EVERY_APPEND, runtime_sym_inst_def, mk_inst_def, is_label_operand_def]) >>
  gvs[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND,
      EVERY_APPEND, runtime_sym_inst_def, mk_inst_def, is_label_operand_def] >>
  simp[runtime_sym_nonlabel_reserved]
QED
