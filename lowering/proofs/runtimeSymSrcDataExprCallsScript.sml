Theory runtimeSymSrcDataExprCalls
Ancestors
  runtimeSymSrcDataFrame runtimeSymSrcDataExprCallbacks exprLowering compileEnv

Theorem runtime_data_frame_store_words:
  !vs buf off. runtime_data_frame (compile_store_words buf vs off)
Proof
  Induct >> rpt gen_tac >> Cases_on `off = 0` >>
  simp[compile_store_words_def]
QED

Theorem runtime_data_frame_invert:
  runtime_data_frame (compile_invert v ty cenv)
Proof
  Cases_on `ty` >> simp[compile_invert_def]
QED

Theorem runtime_data_frame_acc:
  (!vv. runtime_data_frame (unwrap_value cenv vv)) /\
  runtime_data_frame (cfn cenv (BaseT AddressT) e) ==>
  runtime_data_frame (compile_acc cfn cenv e acc)
Proof
  strip_tac >>
  `runtime_data_frame (lower_value cfn cenv (BaseT AddressT) e)` by
    simp[runtime_data_frame_lower_value] >>
  Cases_on `acc` >> rw[runtime_data_frame_def, compile_acc_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  fs[runtime_data_frame_def] >>
  metis_tac[runtime_data_frame_emit_op, runtime_data_frame_emit_inst,
            runtime_data_frame_def, pairTheory.SND]
QED

Theorem runtime_data_frame_call_internal:
  (!e ty. MEM e args ==> runtime_data_frame (cfn cenv ty e)) /\
  (!es. (!e ty. MEM e es ==> runtime_data_frame (cfn cenv ty e)) ==>
        runtime_data_frame (compile_multi_vvs cfn cenv es)) /\
  (!n. runtime_data_frame (compile_alloc_buffer n)) /\
  (!vs stack tys. runtime_data_frame (compile_stage_intcall_args cenv vs stack tys)) /\
  (!buf vs off. runtime_data_frame (store_multi_results buf vs off)) ==>
  runtime_data_frame (compile_call cfn cenv rt ty (IntCall id) args dr)
Proof
  strip_tac >> rw[runtime_data_frame_def, compile_call_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `returns_count > 0` >> Cases_on `return_buf_size > 0` >>
  gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  fs[runtime_data_frame_def] >>
  metis_tac[runtime_data_frame_def, runtime_data_frame_emit_op,
    runtime_data_frame_emit_multi_op, runtime_data_frame_emit_void, pairTheory.SND]
QED

Theorem runtime_data_frame_addmod_names:
  (!ty nm. runtime_data_frame (compile_name_vv cenv ty nm)) /\
  (!vv. runtime_data_frame (unwrap_value cenv vv)) /\
  (!a b m. runtime_data_frame (compile_addmod a b m)) ==>
  runtime_data_frame (compile_addmod_names cenv rt aty a bty b mty m)
Proof
  strip_tac >> rw[runtime_data_frame_def, compile_addmod_names_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[oneline as_stack_val_def] >> split_pair_case_tac >>
  gvs[] >> fs[runtime_data_frame_def] >>
  metis_tac[pairTheory.SND]
QED

Theorem runtime_data_frame_mulmod_names:
  (!ty nm. runtime_data_frame (compile_name_vv cenv ty nm)) /\
  (!vv. runtime_data_frame (unwrap_value cenv vv)) /\
  (!a b m. runtime_data_frame (compile_mulmod a b m)) ==>
  runtime_data_frame (compile_mulmod_names cenv rt aty a bty b mty m)
Proof
  strip_tac >> rw[runtime_data_frame_def, compile_mulmod_names_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[oneline as_stack_val_def] >> split_pair_case_tac >>
  gvs[] >> fs[runtime_data_frame_def] >>
  metis_tac[pairTheory.SND]
QED

Theorem runtime_data_frame_powmod256_names:
  (!ty nm. runtime_data_frame (compile_name_vv cenv ty nm)) /\
  (!vv. runtime_data_frame (unwrap_value cenv vv)) /\
  (!a b. runtime_data_frame (compile_pow_mod256 a b)) ==>
  runtime_data_frame (compile_powmod256_names cenv rt aty a bty b)
Proof
  strip_tac >> rw[runtime_data_frame_def, compile_powmod256_names_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[oneline as_stack_val_def] >> split_pair_case_tac >>
  gvs[] >> fs[runtime_data_frame_def] >>
  metis_tac[pairTheory.SND]
QED

Theorem runtime_data_frame_call_external:
  (!e ty. MEM e args ==> runtime_data_frame (cfn cenv ty e)) /\
  (!vv. runtime_data_frame (unwrap_value cenv vv)) /\
  (!es. (!e ty. MEM e es ==> runtime_data_frame (cfn cenv ty e)) ==>
    runtime_data_frame (compile_multi_vvs cfn cenv es)) /\
  (!es rt ks. (!e ty. MEM e es ==> runtime_data_frame (cfn cenv ty e)) ==>
    runtime_data_frame (compile_ext_call_kwargs cfn cenv rt ks es)) /\
  (!a vs ts ms az mid rz mn rb sc v g sk hd d rt dt ei di.
    runtime_data_frame (compile_external_call_kwargs cenv a vs ts ms az mid rz mn rb
      sc v g sk hd d rt dt ei di)) ==>
  runtime_data_frame (compile_call cfn cenv rt ty (ExtCall sc sk sig opts) args dr)
Proof
  strip_tac >> PairCases_on `sig` >> Cases_on `args`
  >- (rw[runtime_data_frame_def, compile_call_def] >>
      rpt (pairarg_tac >> gvs[]) >>
      metis_tac[runtime_data_frame_def, runtime_data_frame_emit_inst, pairTheory.SND]) >>
  `runtime_data_frame (lower_value cfn cenv (BaseT AddressT) h)` by
    (irule runtime_data_frame_lower_value >> simp[]) >>
  `runtime_data_frame (compile_multi_vvs cfn cenv (TAKE (LENGTH sig1) t))` by
    (first_x_assum irule >> metis_tac[rich_listTheory.MEM_TAKE, listTheory.MEM]) >>
  `runtime_data_frame (compile_ext_call_kwargs cfn cenv sig2 opts (DROP (LENGTH sig1) t))` by
    (first_x_assum irule >> metis_tac[rich_listTheory.MEM_DROP_IMP, listTheory.MEM]) >>
  rw[runtime_data_frame_def, compile_call_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `gas_opt` >> Cases_on `value_opt` >> Cases_on `default_opt` >>
  gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  IF_CASES_TAC >> simp[] >> fs[runtime_data_frame_def] >>
  metis_tac[runtime_data_frame_def, runtime_data_frame_emit_op, pairTheory.SND]
QED

Theorem runtime_data_frame_call_send:
  (!e ty. MEM e args ==> runtime_data_frame (cfn cenv ty e)) /\
  (!vv. runtime_data_frame (unwrap_value cenv vv)) ==>
  runtime_data_frame (compile_call cfn cenv rt ty (Send gas) args dr)
Proof
  strip_tac >> Cases_on `args` >>
  rw[runtime_data_frame_def, compile_call_def] >>
  rpt (CASE_TAC >> gvs[]) >> rpt (pairarg_tac >> gvs[]) >>
  fs[runtime_data_frame_def, lower_value_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  metis_tac[runtime_data_frame_def, runtime_data_frame_emit_op,
    runtime_data_frame_emit_void, runtime_data_frame_emit_inst, pairTheory.SND]
QED

Theorem runtime_data_frame_call_raw_revert:
  (!e ty. MEM e args ==> runtime_data_frame (cfn cenv ty e)) /\
  (!vv. runtime_data_frame (unwrap_value cenv vv)) /\
  (!v. runtime_data_frame (compile_raw_revert v)) ==>
  runtime_data_frame (compile_call cfn cenv rt ty RawRevert args dr)
Proof
  strip_tac >> Cases_on `args` >>
  rw[runtime_data_frame_def, compile_call_def] >>
  rpt (CASE_TAC >> gvs[]) >> rpt (pairarg_tac >> gvs[]) >>
  fs[runtime_data_frame_def, lower_value_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  metis_tac[runtime_data_frame_def, runtime_data_frame_emit_inst, pairTheory.SND]
QED

Theorem runtime_data_frame_call_selfdestruct:
  (!e ty. MEM e args ==> runtime_data_frame (cfn cenv ty e)) /\
  (!vv. runtime_data_frame (unwrap_value cenv vv)) /\
  (!v. runtime_data_frame (compile_selfdestruct v)) ==>
  runtime_data_frame (compile_call cfn cenv rt ty SelfDestructTarget args dr)
Proof
  strip_tac >> Cases_on `args` >>
  rw[runtime_data_frame_def, compile_call_def] >>
  rpt (CASE_TAC >> gvs[]) >> rpt (pairarg_tac >> gvs[]) >>
  fs[runtime_data_frame_def, lower_value_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  metis_tac[runtime_data_frame_def, runtime_data_frame_emit_inst, pairTheory.SND]
QED

Theorem runtime_data_frame_call_raw:
  (!e ty. MEM e args ==> runtime_data_frame (cfn cenv ty e)) /\
  (!vv. runtime_data_frame (unwrap_value cenv vv)) /\
  (!es rt ks. (!e ty. MEM e es ==> runtime_data_frame (cfn cenv ty e)) ==>
    runtime_data_frame (compile_ext_call_kwargs cfn cenv rt ks es)) /\
  (!n. runtime_data_frame (compile_raw_call_outbuf n)) /\
  (!a p n g v ct sz rof ov op.
    runtime_data_frame (compile_raw_call_finish a p n g v ct sz rof ov op)) ==>
  runtime_data_frame (compile_call cfn cenv rt ty (RawCallTarget rcf) args dr)
Proof
  strip_tac >> Cases_on `args`
  >- (rw[runtime_data_frame_def, compile_call_def] >> rpt (pairarg_tac >> gvs[]) >>
      metis_tac[runtime_data_frame_def, runtime_data_frame_emit_inst, pairTheory.SND]) >>
  Cases_on `t`
  >- (rw[runtime_data_frame_def, compile_call_def] >> rpt (pairarg_tac >> gvs[]) >>
      metis_tac[runtime_data_frame_def, runtime_data_frame_emit_inst, pairTheory.SND]) >>
  `runtime_data_frame (compile_ext_call_kwargs cfn cenv NoneT rcf.rcf_kws t')` by
    (first_x_assum irule >> simp[]) >>
  rw[runtime_data_frame_def, compile_call_def] >> rpt (pairarg_tac >> gvs[]) >>
  Cases_on `gas_opt` >> Cases_on `value_opt` >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >> IF_CASES_TAC >> simp[] >>
  fs[runtime_data_frame_def, lower_value_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  metis_tac[runtime_data_frame_def, runtime_data_frame_emit_op,
    runtime_data_frame_emit_inst, pairTheory.SND]
QED

Theorem runtime_data_frame_call_raw_calldata:
  (!e ty. MEM e args ==> runtime_data_frame (cfn cenv ty e)) /\
  (!vv. runtime_data_frame (unwrap_value cenv vv)) /\
  (!es rt ks. (!e ty. MEM e es ==> runtime_data_frame (cfn cenv ty e)) ==>
    runtime_data_frame (compile_ext_call_kwargs cfn cenv rt ks es)) /\
  (!n. runtime_data_frame (compile_raw_call_outbuf n)) /\
  runtime_data_frame compile_msg_data_to_memory /\
  (!a p n g v ct sz rof ov op.
    runtime_data_frame (compile_raw_call_finish a p n g v ct sz rof ov op)) ==>
  runtime_data_frame (compile_call cfn cenv rt ty (RawCallCalldataTarget rcf) args dr)
Proof
  strip_tac >> Cases_on `args`
  >- (rw[runtime_data_frame_def, compile_call_def] >> rpt (pairarg_tac >> gvs[]) >>
      metis_tac[runtime_data_frame_def, runtime_data_frame_emit_inst, pairTheory.SND]) >>
  `runtime_data_frame (compile_ext_call_kwargs cfn cenv NoneT rcf.rcf_kws t)` by
    (first_x_assum irule >> simp[]) >>
  rw[runtime_data_frame_def, compile_call_def] >> rpt (pairarg_tac >> gvs[]) >>
  Cases_on `gas_opt` >> Cases_on `value_opt` >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >> IF_CASES_TAC >> simp[] >>
  fs[runtime_data_frame_def, lower_value_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  metis_tac[runtime_data_frame_def, runtime_data_frame_emit_op,
    runtime_data_frame_emit_void, runtime_data_frame_emit_inst, pairTheory.SND]
QED

Theorem runtime_data_frame_call_raw_log_pair:
  (!e. MEM e (raw_log_topic_exprs topics) ==>
       runtime_data_frame (cfn cenv (expr_type e) e)) /\
  runtime_data_frame (cfn cenv (expr_type data) data) /\
  (!vv. runtime_data_frame (unwrap_value cenv vv)) /\
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_call cfn cenv rt ty RawLog [topics; data] dr)
Proof
  strip_tac >>
  `runtime_data_frame (compile_multi_exprs cfn cenv (raw_log_topic_exprs topics))` by
    (irule runtime_data_frame_multi_exprs >> simp[]) >>
  `runtime_data_frame (lower_value cfn cenv (expr_type data) data)` by
    simp[runtime_data_frame_lower_value] >>
  rw[runtime_data_frame_def, compile_call_def] >>
  rpt (pairarg_tac >> gvs[]) >> IF_CASES_TAC >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >> fs[runtime_data_frame_def] >>
  metis_tac[runtime_data_frame_def, runtime_data_frame_emit_op,
    runtime_data_frame_emit_void, runtime_data_frame_emit_inst, pairTheory.SND]
QED

Theorem runtime_data_frame_call_raw_log:
  (!e ty. MEM e args ==> runtime_data_frame (cfn cenv ty e)) /\
  (!topics data e. args = [topics; data] /\ MEM e (raw_log_topic_exprs topics) ==>
       runtime_data_frame (cfn cenv (expr_type e) e)) /\
  (!vv. runtime_data_frame (unwrap_value cenv vv)) /\
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_call cfn cenv rt ty RawLog args dr)
Proof
  strip_tac >> Cases_on `args`
  >- (rw[runtime_data_frame_def, compile_call_def] >> rpt (pairarg_tac >> gvs[]) >>
      metis_tac[runtime_data_frame_def, runtime_data_frame_emit_inst, pairTheory.SND]) >>
  Cases_on `t`
  >- (rw[runtime_data_frame_def, compile_call_def] >> rpt (pairarg_tac >> gvs[]) >>
      metis_tac[runtime_data_frame_def, runtime_data_frame_emit_inst, pairTheory.SND]) >>
  Cases_on `t'`
  >- (irule runtime_data_frame_call_raw_log_pair >> simp[]) >>
  rw[runtime_data_frame_def, compile_call_def] >> rpt (pairarg_tac >> gvs[]) >>
  metis_tac[runtime_data_frame_def, runtime_data_frame_emit_inst, pairTheory.SND]
QED

Theorem runtime_data_frame_call:
  (!e ty. MEM e args ==> runtime_data_frame (cfn cenv ty e)) /\
  (!topics data e. target = RawLog /\ args = [topics; data] /\
     MEM e (raw_log_topic_exprs topics) ==>
     runtime_data_frame (cfn cenv (expr_type e) e)) /\
  (!vv. runtime_data_frame (unwrap_value cenv vv)) /\
  (!es. (!e ty. MEM e es ==> runtime_data_frame (cfn cenv ty e)) ==>
    runtime_data_frame (compile_multi_vvs cfn cenv es)) /\
  (!es rt ks. (!e ty. MEM e es ==> runtime_data_frame (cfn cenv ty e)) ==>
    runtime_data_frame (compile_ext_call_kwargs cfn cenv rt ks es)) /\
  (!n. runtime_data_frame (compile_alloc_buffer n)) /\
  (!vs stack tys. runtime_data_frame (compile_stage_intcall_args cenv vs stack tys)) /\
  (!buf vs off. runtime_data_frame (store_multi_results buf vs off)) /\
  (!a vs ts ms az mid rz mn rb sc v g sk hd d rt dt ei di.
    runtime_data_frame (compile_external_call_kwargs cenv a vs ts ms az mid rz mn rb
      sc v g sk hd d rt dt ei di)) /\
  (!n. runtime_data_frame (compile_raw_call_outbuf n)) /\
  (!a p n g v ct sz rof ov op.
    runtime_data_frame (compile_raw_call_finish a p n g v ct sz rof ov op)) /\
  runtime_data_frame compile_msg_data_to_memory /\
  (!v. runtime_data_frame (compile_raw_revert v)) /\
  (!v. runtime_data_frame (compile_selfdestruct v)) /\
  (!ck salt rof. runtime_data_frame (compile_create_call cfn cenv ck salt rof args)) ==>
  runtime_data_frame (compile_call cfn cenv rt ty target args dr)
Proof
  strip_tac >> Cases_on `target`
  >- (irule runtime_data_frame_call_internal >> simp[])
  >- (irule runtime_data_frame_call_external >> simp[])
  >- (irule runtime_data_frame_call_send >> simp[])
  >- (irule runtime_data_frame_call_raw >> simp[])
  >- (irule runtime_data_frame_call_raw_calldata >> simp[])
  >- (irule runtime_data_frame_call_raw_log >> simp[])
  >- (irule runtime_data_frame_call_raw_revert >> simp[])
  >- (irule runtime_data_frame_call_selfdestruct >> simp[]) >>
  rw[runtime_data_frame_def, compile_call_def] >>
  simp[oneline as_stack_val_def] >> split_pair_case_tac >> gvs[] >>
  fs[runtime_data_frame_def] >> metis_tac[pairTheory.SND]
QED
