Theory runtimeSymSrcBuiltinStrings
Ancestors
  runtimeSymSrcContext runtimeSymSrcContextCopy runtimeSymSrcModuleDispatch
  runtimeSymSrcEmission runtimeSymSrcInterfaces builtinStrings
  compileEnv emitHelper loweringShapeDefs venomInst list stackPlanTypes

Theorem runtime_sym_uint2str:
  !v digits size s op s'.
  ~is_label_operand v /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_uint2str v digits size s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  simp[compile_uint2str_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> rpt gen_tac >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  imp_res_tac runtime_sym_fresh_var >>
  imp_res_tac runtime_sym_fresh_label >>
  imp_res_tac runtime_sym_new_block_result >> gvs[] >>
  drule_all runtime_sym_alloc_buffer >> strip_tac >>
  rpt (FIRST (map (fn rule =>
    first_x_assum (fn eqn =>
      mp_then Any mp_tac rule eqn >>
      (impl_tac >- simp[is_label_operand_def]) >> strip_tac >>
      gvs[]))
    [runtime_sym_assign, runtime_sym_jump, runtime_sym_jnz,
     runtime_sym_emit_op, runtime_sym_emit_void])) >>
  simp[is_label_operand_def]
QED
