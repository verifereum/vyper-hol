Theory deploySymSrcHistory
Ancestors
  runtimeSymSrcInterfaces moduleLowering compileEnv emitHelper
  loweringShapeDefs list venomInst context

Definition deploy_sym_inst_def:
  deploy_sym_inst i <=>
    i.inst_opcode <> CODESIZE /\
    (i.inst_opcode = CODECOPY ==>
      ?dst sz. i.inst_operands = [dst; Label "runtime_begin"; sz]) /\
    ~MEM (Label "code_end") i.inst_operands
End

Theorem runtime_sym_inst_deploy:
  runtime_sym_inst i ==> deploy_sym_inst i
Proof
  simp[runtime_sym_inst_def, deploy_sym_inst_def]
QED

Theorem deploy_sym_simple_deploy:
  EVERY deploy_sym_inst (state_insts s) ==>
  EVERY deploy_sym_inst
    (state_insts (SND (compile_simple_deploy runtime_size immutables_len s)))
Proof
  simp[compile_simple_deploy_def, compile_alloc_buffer_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, emit_void_def, emit_inst_def, fresh_var_def,
       fresh_id_def, emit_def, state_insts_def, all_blocks_def,
       MAP_APPEND, FLAT_APPEND, EVERY_APPEND, mk_inst_def,
       deploy_sym_inst_def]
QED

Theorem deploy_sym_constructor_epilogue:
  ~is_label_operand imm /\ EVERY deploy_sym_inst (state_insts s) ==>
  EVERY deploy_sym_inst
    (state_insts (SND (compile_constructor_epilogue rt_size len imm s)))
Proof
  Cases_on `len > 0` >>
  simp[compile_constructor_epilogue_def, compile_alloc_buffer_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, emit_void_def, emit_inst_def, fresh_var_def,
       fresh_id_def, emit_def, state_insts_def, all_blocks_def,
       MAP_APPEND, FLAT_APPEND, EVERY_APPEND, mk_inst_def,
       deploy_sym_inst_def] >>
  metis_tac[runtime_sym_nonlabel_reserved]
QED
