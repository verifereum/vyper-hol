Theory runtimeSymSrcDeclarations
Ancestors
  runtimeSymSrcInterfaces stmtLowering compileEnv loweringShapeDefs
  finite_map list venomInst stackPlanTypes emitHelper

Theorem runtime_sym_declare_local:
  runtime_sym_env ce /\ EVERY runtime_sym_inst (state_insts s) /\
  declare_local ce id ty s = (ce',s') ==>
  runtime_sym_env ce' /\ EVERY runtime_sym_inst (state_insts s')
Proof
  simp[declare_local_def] >>
  Cases_on `ce.ce_alloca_locals` >>
  simp[comp_bind_def, comp_return_def, fresh_var_def] >>
  rpt strip_tac >> gvs[] >>
  fs[state_insts_def, all_blocks_def] >>
  gvs[runtime_sym_env_def, FLOOKUP_UPDATE, runtime_sym_loc_def,
      is_label_operand_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[runtime_sym_loc_def, is_label_operand_def] >>
  metis_tac[]
QED

Theorem runtime_sym_declare_stmt_local:
  runtime_sym_env ce /\ EVERY runtime_sym_inst (state_insts s) /\
  declare_stmt_local ce stmt s = (ce',s') ==>
  runtime_sym_env ce' /\ EVERY runtime_sym_inst (state_insts s')
Proof
  Cases_on `stmt` >> simp[declare_stmt_local_def, comp_return_def] >>
  metis_tac[runtime_sym_declare_local]
QED

Theorem runtime_sym_emit_local_alloca:
  EVERY runtime_sym_inst (state_insts s) /\
  emit_local_alloca ce id s = ((),s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  simp[emit_local_alloca_def] >>
  Cases_on `FLOOKUP ce.ce_vars id` >>
  simp[comp_return_def] >- (rpt strip_tac >> gvs[]) >>
  Cases_on `x` >> simp[comp_return_def] >>
  gvs[AllCaseEqs(), emit_inst_def, comp_bind_def, fresh_id_def,
      emit_def, comp_return_def, state_insts_def, all_blocks_def,
      MAP_APPEND, FLAT_APPEND, EVERY_APPEND, runtime_sym_inst_def,
      mk_inst_def] >> rpt strip_tac >> gvs[] >>
  Cases_on `o'` >>
  gvs[comp_return_def, comp_bind_def, fresh_id_def, emit_def,
      state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND,
      EVERY_APPEND, runtime_sym_inst_def]
QED
