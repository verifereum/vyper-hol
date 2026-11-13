Theory runtimeSymSrcContextComplete
Ancestors
  runtimeSymSrcContext context compileEnv stackPlanTypes emitHelper runtimeSymSrcEmission
  runtimeSymSrcContextCopy runtimeSymSrcContextTyped runtimeSymSrcContextValues
  runtimeSymSrcGeneratorContracts

Theorem runtime_sym_unwrap_value:
  runtime_sym_env ce /\ runtime_sym_value vv /\
  EVERY runtime_sym_inst (state_insts s) /\
  unwrap_value ce vv s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  strip_tac >> irule runtime_sym_unwrap_value_cond >>
  simp[] >> metis_tac[runtime_sym_ensure_in_memory]
QED

Theorem runtime_sym_materialize_vv:
  runtime_sym_env ce /\ runtime_sym_value vv /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_materialize_vv ce ty vv s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  strip_tac >> irule runtime_sym_materialize_vv_cond >>
  qexistsl [`ce`, `s`, `ty`, `vv`] >> simp[] >>
  metis_tac[runtime_sym_unwrap_value, runtime_sym_store_memory]
QED

Theorem runtime_sym_ifexp_arm:
  runtime_sym_env ce /\ runtime_sym_value vv /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_ifexp_arm ce rt at vv s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  strip_tac >> irule runtime_sym_ifexp_arm_cond >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[runtime_sym_unwrap_value, runtime_sym_store_memory]
QED

Theorem runtime_sym_snapshot_vv:
  runtime_sym_env ce /\ runtime_sym_value vv /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_snapshot_vv ce copy vv s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  strip_tac >> irule runtime_sym_snapshot_vv_cond >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[runtime_sym_unwrap_value, runtime_sym_materialize_vv]
QED

Theorem runtime_sym_context_contracts:
  runtime_sym_context_clauses
Proof
  simp[runtime_sym_context_clauses_def] >> rpt conj_tac
  >- metis_tac[runtime_sym_unwrap_value]
  >- metis_tac[runtime_sym_ifexp_arm]
  >- metis_tac[runtime_sym_alloc_buffer] >>
  metis_tac[runtime_sym_bytestring_widen_copy]
QED

Theorem runtime_sym_encode_log_topic:
  ~is_label_operand v /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_encode_log_topic v bytes s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  Cases_on `bytes` >>
  simp[compile_encode_log_topic_def, comp_return_def, comp_bind_def]
  >- (ntac 2 (pairarg_tac >> simp[]) >> strip_tac >>
      qpat_assum `emit_op ADD _ _ = _`
        (mp_then Any mp_tac runtime_sym_emit_op) >>
      simp[is_label_operand_def] >> strip_tac >>
      qpat_assum `emit_op MLOAD _ _ = _`
        (mp_then Any mp_tac runtime_sym_emit_op) >> simp[] >> strip_tac >>
      qpat_assum `emit_op SHA3 _ _ = _`
        (mp_then Any mp_tac runtime_sym_emit_op) >> simp[]) >>
  strip_tac >> gvs[]
QED
