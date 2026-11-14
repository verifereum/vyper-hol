(* Operand exclusion for statement log and return boundaries. *)
Theory runtimeLabelStmtIO
Ancestors
  runtimeLabelExprCallbacks
  runtimeLabelPrimitives runtimeLabelInvariant runtimeLabelValues runtimeLabelBuiltins runtimeLabelABI
  stmtLowering exprLowering compileEnv context emitHelper venomInst list

Theorem rb_compile_log_save_arg:
  rb_env_ok ce /\ rb_operand_ok op ==>
  rb_step rb_operand_ok (compile_log_save_arg ce src_ty op es)
Proof
  strip_tac >> pure_rewrite_tac[compile_log_save_arg_def] >>
  IF_CASES_TAC >> simp[rb_step_return, rb_compile_materialize_vv,
                       rb_value_ok_def]
QED

Theorem rb_compile_log_eval_all:
  !es. rb_expr_contract /\ rb_env_ok ce ==>
  rb_step (EVERY (rb_operand_ok o FST)) (compile_log_eval_all ce es)
Proof
  Induct >> simp[compile_log_eval_all_def, rb_step_return] >>
  rpt strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- (irule rb_lower_value >> gvs[rb_expr_contract_def]) >>
  gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_log_save_arg] >>
  gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `EVERY (rb_operand_ok o FST)` >>
  BETA_TAC >> reverse conj_tac >- simp[] >>
  simp[rb_step_return]
QED

Theorem rb_compile_log_topic_ops:
  !ops. EVERY (rb_operand_ok o FST) ops ==>
  rb_step (EVERY rb_operand_ok) (compile_log_topic_ops ops)
Proof
  Induct >> simp[compile_log_topic_ops_def, rb_step_return] >>
  rpt strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_encode_log_topic] >>
  gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `EVERY rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[] >> simp[rb_step_return]
QED

Theorem rb_split_log_ops:
  !ops flags. EVERY (rb_operand_ok o FST) ops ==>
  EVERY (rb_operand_ok o FST) (FST (split_log_ops ops flags)) /\
  EVERY (rb_operand_ok o FST) (SND (split_log_ops ops flags))
Proof
  recInduct split_log_ops_ind >>
  simp[split_log_ops_def] >> rpt strip_tac >>
  pairarg_tac >> gvs[] >> metis_tac[]
QED

Theorem rb_compile_log_store_data:
  !ops tys buf off. rb_env_ok ce /\ EVERY (rb_operand_ok o FST) ops /\
  rb_operand_ok buf ==>
  rb_step (K T) (compile_log_store_data ce ops tys buf off)
Proof
  Induct >> Cases_on `tys` >>
  simp[compile_log_store_data_def, rb_step_return, rb_emit_void] >>
  rpt strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >>
  gen_tac >> strip_tac >> irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >>
  conj_tac >- simp[rb_compile_store_memory] >>
  first_x_assum irule >> simp[]
QED

Theorem rb_compile_load_tuple_elements:
  !tys off. rb_operand_ok base_op ==>
  rb_step (EVERY rb_operand_ok) (compile_load_tuple_elements ce base_op tys off)
Proof
  Induct >> simp[compile_load_tuple_elements_def, rb_step_return] >>
  rpt strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `EVERY rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[] >> simp[rb_step_return]
QED

Theorem rb_compile_internal_return:
  rb_env_ok ce /\ rb_operand_ok pc /\
  (case rv of NONE => T | SOME v => rb_operand_ok v) /\
  (case buf of NONE => T | SOME b => rb_operand_ok b) ==>
  rb_step (K T) (compile_internal_return ce rv pc n rty sty tys buf)
Proof
  strip_tac >> pure_rewrite_tac[compile_internal_return_def] >>
  Cases_on `n > 0` >> simp[]
  >- (Cases_on `rv` >> gvs[rb_emit_inst] >>
      Cases_on `tys = []` >> simp[rb_emit_inst] >>
      irule rb_step_bind >> qexists_tac `EVERY rb_operand_ok` >> BETA_TAC >>
      reverse conj_tac >- simp[rb_compile_load_tuple_elements] >>
      gen_tac >> strip_tac >> simp[rb_emit_inst, EVERY_APPEND]) >>
  Cases_on `buf` >> gvs[rb_emit_inst] >>
  Cases_on `rv` >> gvs[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_compile_store_memory, rb_emit_inst]
QED

Theorem rb_compile_external_return:
  (case rv of NONE => T | SOME v => rb_operand_ok v) ==>
  rb_step (K T) (compile_external_return rv prim raw info maxsz guard key transient view)
Proof
  strip_tac >> pure_rewrite_tac[compile_external_return_def] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
  >- (Cases_on `guard` >> simp[rb_compile_nonreentrant_unlock, rb_step_return]) >>
  Cases_on `rv` >> gvs[rb_emit_inst] >>
  Cases_on `raw` >> simp[]
  >- (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      simp[rb_emit_inst]) >>
  Cases_on `prim` >> simp[]
  >- (irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
      reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
      gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
      irule rb_bind_return >> BETA_TAC >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_emit_inst]) >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_bind_return >> BETA_TAC >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_abi_encode] >>
  gen_tac >> strip_tac >> simp[rb_emit_inst]
QED

Theorem rb_compile_internal_return_from_env:
  rb_env_ok ce /\ rb_operand_ok v /\ rb_operand_ok rpc ==>
  rb_step (K T) (compile_internal_return_from_env ce ty sty v rpc)
Proof
  strip_tac >> pure_rewrite_tac[compile_internal_return_from_env_def] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_compile_return_unlock] >>
  irule rb_step_bind >>
  qexists_tac `\b. case b of NONE => T | SOME op => rb_operand_ok op` >>
  BETA_TAC >> reverse conj_tac
  >- (Cases_on `ce.ce_return_buf` >> simp[rb_step_return] >>
      rename1 `SOME loc` >> Cases_on `loc` >> simp[rb_step_return]
      >- (irule rb_bind_emit_op >> BETA_TAC >> simp[rb_step_return]) >>
      gvs[rb_env_ok_def, rb_location_ok_def, rb_step_return]) >>
  gen_tac >> strip_tac >> irule rb_bind_return >> BETA_TAC >>
  irule rb_compile_internal_return >> simp[]
QED
