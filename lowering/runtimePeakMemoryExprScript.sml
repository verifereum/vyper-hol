(* Allocation window coverage through expression and call lowering. *)
Theory runtimePeakMemoryExpr
Ancestors
  runtimePeakMemoryCode runtimePeakMemorySourceGate runtimePeakMemoryAbi
  exprValueWrapperStateProps exprLowering exprLoweringProps supportedExprTraverse
  compileEnv context builtinSystem builtinCreate emitHelper venomInst list rich_list

fun windows_tac thms =
  rpt (FIRST [
    CHANGED_TAC (simp(thms @ [LET_THM, pairTheory.FORALL_PROD, pairTheory.UNCURRY_DEF,
      dalloca_windows_emit_helpers, dalloca_windows_new_block,
      dalloca_windows_fresh, dalloca_windows_return, dalloca_windows_select,
      dalloca_windows_alloc_buffer])),
    gen_tac, irule dalloca_windows_bind >> conj_tac,
    irule dalloca_windows_ignore_bind >> conj_tac,
    COND_CASES_TAC, BasicProvers.TOP_CASE_TAC]);

val windows_pure_tac = windows_tac [];

Theorem dalloca_windows_imm_load[local]:
  preserves_dalloca_windows window (compile_imm_load_word ctor imm off)
Proof
  Cases_on `imm` >> simp[compile_imm_load_word_def] >> windows_pure_tac
QED

Theorem dalloca_windows_imm_store:
  preserves_dalloca_windows window (compile_imm_store_word imm off value)
Proof
  Cases_on `imm` >> simp[compile_imm_store_word_def] >> windows_pure_tac
QED

Theorem dalloca_windows_ptr_access:
  preserves_dalloca_windows window (compile_ptr_load ctor imm loc off) /\
  preserves_dalloca_windows window (compile_ptr_store ctor imm loc off value)
Proof
  Cases_on `loc` >>
  simp[compile_ptr_load_def, compile_ptr_store_def, dalloca_windows_imm_load,
       dalloca_windows_imm_store, dalloca_windows_emit_helpers] >>
  windows_pure_tac >> simp[dalloca_windows_imm_store]
QED

Theorem dalloca_windows_word_copy:
  preserves_dalloca_windows window
    (compile_word_copy_loop_base src dst count_op load_loc store_loc ctor imm)
Proof
  rewrite_tac[compile_word_copy_loop_base_def] >>
  windows_tac [dalloca_windows_ptr_access]
QED

Theorem dalloca_windows_imm_copy:
  !n off. preserves_dalloca_windows window
    (compile_imm_copy_to_memory ctor imm src dst n off)
Proof
  Induct >> simp[compile_imm_copy_to_memory_def, dalloca_windows_return] >>
  simp[compile_lit_byte_offset_def] >>
  windows_tac [dalloca_windows_imm_load] >> fs[]
QED

Theorem dalloca_windows_ensure_in_memory[local]:
  preserves_dalloca_windows window
    (compile_ensure_in_memory op loc nwords nbytes ctor imm)
Proof
  Cases_on `loc` >>
  simp[compile_ensure_in_memory_def, compile_storage_to_memory_def,
       compile_transient_to_memory_def, compile_word_copy_loop_def,
       compile_word_copy_loop_op_def] >>
  windows_tac [dalloca_windows_word_copy, dalloca_windows_imm_copy]
QED

Theorem dalloca_windows_unwrap_value:
  preserves_dalloca_windows window (unwrap_value cenv vv)
Proof
  Cases_on `vv` >> simp[unwrap_value_def, dalloca_windows_return] >>
  windows_tac [dalloca_windows_ptr_access, dalloca_windows_ensure_in_memory]
QED

Theorem dalloca_windows_lower_value:
  preserves_dalloca_windows window (cfn cenv ty e) ==>
  preserves_dalloca_windows window (lower_value cfn cenv ty e)
Proof
  strip_tac >> rewrite_tac[lower_value_def] >>
  irule dalloca_windows_bind >> simp[dalloca_windows_unwrap_value]
QED

Theorem dalloca_windows_store_same_type[local]:
  preserves_dalloca_windows window (compile_store_memory cenv src dst ty ty)
Proof
  simp[compile_store_memory_def, compile_store_bytestring_def,
       compile_bytestring_copy_len_def] >> windows_pure_tac >>
  Cases_on `type_memory_bytes cenv ty` >>
  simp[compile_copy_memory_def, dalloca_windows_emit_helpers, dalloca_windows_return]
QED

Theorem dalloca_windows_materialize_vv:
  preserves_dalloca_windows window (compile_materialize_vv cenv ty vv)
Proof
  rewrite_tac[compile_materialize_vv_def] >>
  windows_tac [dalloca_windows_unwrap_value, dalloca_windows_store_same_type]
QED

Theorem dalloca_windows_ext_call_kwargs:
  !ks es.
    (!ty e. MEM e es ==> preserves_dalloca_windows window (cfn cenv ty e)) ==>
    preserves_dalloca_windows window
      (compile_ext_call_kwargs cfn cenv return_type ks es)
Proof
  Induct >> Cases_on `es` >> simp[compile_ext_call_kwargs_def, dalloca_windows_return] >>
  simp[compile_ext_call_kwarg_def] >> rpt strip_tac >>
  windows_tac [dalloca_windows_materialize_vv, dalloca_windows_lower_value] >>
  res_tac
QED

Theorem dalloca_windows_raw_call_calldata:
  (!chunk. raw_call_dalloca_chunk chunk 1 ==> window chunk 1) /\
  (!ty e. MEM e args ==> preserves_dalloca_windows window (cfn cenv ty e)) ==>
  preserves_dalloca_windows window
    (compile_call cfn cenv ret_ty ty (RawCallCalldataTarget rcf) args default_ret)
Proof
  strip_tac >>
  rw[preserves_dalloca_windows_def] >>
  Cases_on `args`
  >- (`preserves_dalloca_windows window (emit_inst INVALID [] [])` by
        simp[dalloca_windows_emit_helpers] >>
      gvs[compile_call_def, LET_THM, pairTheory.UNCURRY_DEF,
          preserves_dalloca_windows_def] >>
      Cases_on `emit_inst INVALID [] [] st` >> gvs[] >> metis_tac[]) >>
  qpat_x_assum `compile_call _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_call_def, LET_THM] >>
  rpt (pairarg_tac >> simp[]) >>
  strip_tac >> gvs[] >>
  `preserves_dalloca_windows window (cfn cenv (BaseT AddressT) h)` by
    (first_x_assum match_mp_tac >> simp[]) >>
  `compiler_dalloca_windows window st1` by
    (drule dalloca_windows_lower_value >>
     simp[preserves_dalloca_windows_def] >> metis_tac[]) >>
  `!ety e. MEM e t ==> preserves_dalloca_windows window (cfn cenv ety e)` by
    metis_tac[] >>
  `compiler_dalloca_windows window st2` by
    (mp_tac (Q.SPECL [`rcf.rcf_kws`, `t`] (Q.INST [`return_type` |-> `NoneT`]
       dalloca_windows_ext_call_kwargs)) >>
     simp[preserves_dalloca_windows_def] >> metis_tac[]) >>
  `compiler_dalloca_windows window st3` by
    (Cases_on `gas_opt` >> gvs[] >>
     `preserves_dalloca_windows window (emit_op GAS [])` by
       simp[dalloca_windows_emit_helpers] >>
     fs[preserves_dalloca_windows_def] >> metis_tac[]) >>
  `compiler_dalloca_windows window st4` by
    (mp_tac (Q.INST [`max_outsize` |-> `rcf.rcf_max_outsize`]
      dalloca_windows_raw_call_outbuf) >> simp[preserves_dalloca_windows_def] >>
     metis_tac[]) >>
  `compiler_dalloca_windows window st6` by
    (mp_tac (Q.INST [`addr` |-> `addr_op`, `gas` |-> `gas_op`,
       `value` |-> `case value_opt of NONE => Lit 0w | SOME v => v`,
       `ty` |-> `if rcf.rcf_is_delegate then DelegateCall
                else if rcf.rcf_is_static then StaticCall else RegularCall`,
       `n` |-> `rcf.rcf_max_outsize`, `rev` |-> `rcf.rcf_revert_on_failure`,
       `out` |-> `out_val`, `dest` |-> `out_ptr`]
      dalloca_windows_msg_data_followed_by_call) >>
     simp[preserves_dalloca_windows_def, comp_bind_def] >>
     disch_then (qspecl_then [`st4`, `result_op`, `st6`] mp_tac) >> simp[]) >>
  Cases_on `rcf.rcf_max_outsize = 0` >> gvs[]
QED

Theorem dalloca_windows_create_salt[local]:
  (!ty e. salt = SOME e ==> preserves_dalloca_windows window (cfn cenv ty e)) ==>
  preserves_dalloca_windows window (compile_create_salt cfn cenv salt)
Proof
  Cases_on `salt` >> simp[compile_create_salt_def, dalloca_windows_return] >>
  strip_tac >> windows_tac [dalloca_windows_lower_value]
QED

Theorem dalloca_windows_create_copy_call:
  (!chunk. create_copy_dalloca_chunk chunk 5 ==> window chunk 5) /\
  (!ty e. MEM e args ==> preserves_dalloca_windows window (cfn cenv ty e)) ==>
  preserves_dalloca_windows window
    (compile_create_call cfn cenv CreateCopyOf salted rof args)
Proof
  strip_tac >>
  Cases_on `args` >- (simp[compile_create_call_def] >> windows_pure_tac) >>
  Cases_on `t` >- (simp[compile_create_call_def] >> windows_pure_tac) >>
  gvs[compile_create_call_def, MEM] >>
  windows_tac [dalloca_windows_lower_value, dalloca_windows_create_copy] >>
  irule dalloca_windows_create_salt >>
  Cases_on `salted` >> gvs[] >> rpt strip_tac >> gvs[] >>
  Cases_on `t'` >> gvs[]
QED

Theorem dalloca_windows_compile_call_create_copy:
  (!chunk. create_copy_dalloca_chunk chunk 5 ==> window chunk 5) /\
  (!ty e. MEM e args ==> preserves_dalloca_windows window (cfn cenv ty e)) ==>
  preserves_dalloca_windows window
    (compile_call cfn cenv ret_ty ty (CreateTarget CreateCopyOf salted rof order)
      args default_ret)
Proof
  strip_tac >>
  `preserves_dalloca_windows window (compile_create_call cfn cenv CreateCopyOf salted rof args)`
    by metis_tac[dalloca_windows_create_copy_call] >>
  fs[preserves_dalloca_windows_def, compile_call_def, as_stack_val_def] >>
  rpt strip_tac >>
  Cases_on `compile_create_call cfn cenv CreateCopyOf salted rof args st` >>
  gvs[as_stack_val_def] >> metis_tac[]
QED

Theorem dalloca_windows_copy_memory:
  preserves_dalloca_windows window (compile_copy_memory dst src n) /\
  preserves_dalloca_windows window (compile_copy_memory_dynamic dst src length_op)
Proof
  Cases_on `n` >>
  simp[compile_copy_memory_def, compile_copy_memory_dynamic_def,
       dalloca_windows_return, dalloca_windows_emit_helpers]
QED

Theorem dalloca_windows_store_bytestring:
  preserves_dalloca_windows window (compile_store_bytestring src dst)
Proof
  rewrite_tac[compile_store_bytestring_def, compile_bytestring_copy_len_def] >>
  windows_pure_tac
QED

Theorem dalloca_windows_store_memory_typed:
  (!cenv dst dst_ty src src_ty.
    preserves_dalloca_windows window (compile_store_memory_typed cenv dst dst_ty src src_ty)) /\
  (!cenv dst src dst_tys src_tys dst_off src_off.
    preserves_dalloca_windows window
      (compile_typed_copy_fields cenv dst src dst_tys src_tys dst_off src_off)) /\
  (!cenv dst dst_elem src src_elem n.
    preserves_dalloca_windows window (compile_copy_sarray_typed cenv dst dst_elem src src_elem n)) /\
  (!cenv dst dst_elem cap src src_elem.
    preserves_dalloca_windows window
      (compile_copy_dynarray_typed cenv dst dst_elem cap src src_elem)) /\
  (!cenv dst src dst_fields src_fields dst_off src_off.
    preserves_dalloca_windows window
      (compile_struct_typed_copy cenv dst src dst_fields src_fields dst_off src_off))
Proof
  ho_match_mp_tac compile_store_memory_typed_ind >>
  rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `is_word_type dst_ty`
      >- (simp[Once compile_store_memory_typed_def] >> windows_pure_tac) >>
      Cases_on `is_bytestring_type dst_ty /\ is_bytestring_type src_ty`
      >- simp[Once compile_store_memory_typed_def, dalloca_windows_store_bytestring] >>
      Cases_on `acyclic_struct_metadata cenv.ce_struct_fields`
      >- (Cases_on `dst_ty` >> Cases_on `src_ty` >>
          TRY (rename1 `compile_store_memory_typed ccenv dst (ArrayT dt db) src (ArrayT st sb)` >>
               Cases_on `db` >> Cases_on `sb`) >> gvs[] >>
          simp[Once compile_store_memory_typed_def, LET_THM,
               dalloca_windows_copy_memory] >> metis_tac[]) >>
      simp[Once compile_store_memory_typed_def, dalloca_windows_emit_helpers])
  >- simp[Once compile_store_memory_typed_def, dalloca_windows_return]
  >- simp[Once compile_store_memory_typed_def, dalloca_windows_return]
  >- (rpt gen_tac >> strip_tac >> gvs[] >>
      simp[Once compile_store_memory_typed_def] >>
      windows_tac [compile_with_byte_offset_def] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `type_memory_bytes ccenv dst_ty = type_memory_bytes ccenv src_ty /\
                ~is_abi_dynamic cenv.ce_struct_fields dst_ty` >> gvs[] >>
      simp[Once compile_store_memory_typed_def] >>
      windows_tac [dalloca_windows_copy_memory] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `type_memory_bytes ccenv dst_ty = type_memory_bytes ccenv src_ty /\ dst_ty = src_ty` >> gvs[] >>
      simp[Once compile_store_memory_typed_def] >>
      windows_tac [dalloca_windows_copy_memory] >> metis_tac[])
  >- simp[Once compile_store_memory_typed_def, dalloca_windows_return] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `ALOOKUP src_fields name` >>
  TRY (rename1 `SOME p` >> PairCases_on `p`) >> gvs[] >>
  simp[Once compile_store_memory_typed_def] >>
  windows_tac [compile_with_byte_offset_def] >> metis_tac[]
QED

Theorem dalloca_windows_store_memory:
  preserves_dalloca_windows window (compile_store_memory env src dst dst_ty src_ty)
Proof
  rewrite_tac[compile_store_memory_def] >>
  windows_tac [dalloca_windows_store_memory_typed, dalloca_windows_copy_memory,
               dalloca_windows_store_bytestring]
QED

Theorem dalloca_windows_stage_intcall_args:
  !cfn cenv es flags tys.
    (!ty e. MEM e es ==> preserves_dalloca_windows window (cfn cenv ty e)) ==>
    preserves_dalloca_windows window (compile_stage_intcall_args cfn cenv es flags tys)
Proof
  ho_match_mp_tac compile_stage_intcall_args_ind >>
  rpt conj_tac >> rpt gen_tac >> rpt strip_tac >>
  simp[Once compile_stage_intcall_args_def] >>
  windows_tac [dalloca_windows_unwrap_value, dalloca_windows_store_memory,
               dalloca_windows_store_bytestring] >>
  fs[] >> metis_tac[]
QED

Theorem dalloca_windows_fresh_vars[local]:
  !n. preserves_dalloca_windows window (fresh_vars n)
Proof
  Induct >> simp[fresh_vars_def] >> windows_pure_tac
QED

Theorem dalloca_windows_invoke_multi[local]:
  preserves_dalloca_windows window (emit_multi_op INVOKE ops n)
Proof
  simp[emit_multi_op_def] >> windows_tac [dalloca_windows_fresh_vars]
QED

Theorem dalloca_windows_store_multi_results[local]:
  !ops offset. preserves_dalloca_windows window (store_multi_results buf_op ops offset)
Proof
  Induct >> simp[store_multi_results_def] >> windows_pure_tac
QED

Theorem dalloca_windows_result_state:
  (preserves_dalloca_windows window m <=>
   !st. compiler_dalloca_windows window st ==>
     compiler_dalloca_windows window (SND (m st)))
Proof
  simp[preserves_dalloca_windows_def] >> EQ_TAC >> rpt strip_tac
  >- (qpat_x_assum `!st x st'. _` (qspec_then `st` mp_tac) >>
      Cases_on `m st` >> simp[]) >>
  qpat_x_assum `!st. _` (qspec_then `st` mp_tac) >> simp[]
QED

Theorem dalloca_windows_compile_internal_call:
  (!ct e. MEM e args ==>
     preserves_dalloca_windows window (cfn cenv ct e)) /\
  (!ct e. MEM e (omitted_defaults cenv (nsid_to_string func_id) (LENGTH args)) ==>
     preserves_dalloca_windows window
       (cfn (cenv_without_defaults cenv (nsid_to_string func_id)) ct e)) ==>
  preserves_dalloca_windows window (compile_call cfn cenv ret_ty ty (IntCall func_id) args d)
Proof
  strip_tac >>
  imp_res_tac dalloca_windows_stage_intcall_args >>
  simp[dalloca_windows_result_state, compile_call_def, LET_THM, pairTheory.UNCURRY] >>
  gen_tac >> strip_tac >>
  windows_tac [] >>
  RULE_ASSUM_TAC (REWRITE_RULE [dalloca_windows_result_state]) >>
  let val stages = map (irule o SIMP_RULE (srw_ss()) [dalloca_windows_result_state])
    [dalloca_windows_store_multi_results, dalloca_windows_invoke_multi,
     cj 2 dalloca_windows_emit_helpers, dalloca_windows_alloc_buffer]
  in rpt (FIRST (CHANGED_TAC (simp[]) :: first_assum irule :: stages)) end
QED

fun finish_window_state thms =
  let
    val stages = map (irule o SIMP_RULE (srw_ss()) [dalloca_windows_result_state])
      (map DISCH_ALL (CONJUNCTS (UNDISCH dalloca_windows_emit_helpers)) @ thms)
  in
    RULE_ASSUM_TAC (REWRITE_RULE [dalloca_windows_result_state]) >>
    rpt (FIRST (CHANGED_TAC (simp[]) :: gen_tac :: strip_tac :: first_assum irule :: stages))
  end;

Theorem dalloca_windows_compile_send:
  (!ct e. MEM e args ==> preserves_dalloca_windows window (cfn cenv ct e)) ==>
  preserves_dalloca_windows window (compile_call cfn cenv ret_ty ty (Send has_gas) args d)
Proof
  Cases_on `args` >- (simp[dalloca_windows_result_state, compile_call_def, pairTheory.UNCURRY] >>
                       finish_window_state []) >>
  Cases_on `t` >>
  simp[dalloca_windows_result_state, compile_call_def, LET_THM, pairTheory.UNCURRY] >>
  rpt strip_tac >>
  windows_tac [] >>
  finish_window_state [dalloca_windows_lower_value]
QED

Theorem dalloca_windows_raw_call_target:
  (!ct e. MEM e args ==> preserves_dalloca_windows window (cfn cenv ct e)) ==>
  preserves_dalloca_windows window (compile_call cfn cenv ret_ty ty (RawCallTarget rcf) args d)
Proof
  Cases_on `args` >- (simp[dalloca_windows_result_state, compile_call_def, pairTheory.UNCURRY] >>
                       finish_window_state []) >>
  Cases_on `t` >> strip_tac >>
  fs[] >>
  TRY (`preserves_dalloca_windows window
      (compile_ext_call_kwargs cfn cenv NoneT rcf.rcf_kws t')` by
    (irule dalloca_windows_ext_call_kwargs >> metis_tac[])) >>
  simp[dalloca_windows_result_state, compile_call_def, LET_THM, pairTheory.UNCURRY] >>
  rpt strip_tac >>
  windows_tac [] >>
  finish_window_state [dalloca_windows_raw_call_outbuf, dalloca_windows_raw_call_finish,
    dalloca_windows_lower_value]
QED

Theorem dalloca_windows_multi_exprs:
  !args. (!ct e. MEM e args ==> preserves_dalloca_windows window (cfn cenv ct e)) ==>
    preserves_dalloca_windows window (compile_multi_exprs cfn cenv args)
Proof
  Induct >> simp[compile_multi_exprs_def, dalloca_windows_return] >> rpt strip_tac >>
  windows_tac [dalloca_windows_lower_value] >>
  metis_tac[dalloca_windows_lower_value]
QED

Theorem dalloca_windows_raw_revert_and_selfdestruct:
  preserves_dalloca_windows window (compile_raw_revert data) /\
  preserves_dalloca_windows window (compile_selfdestruct addr)
Proof
  simp[compile_raw_revert_def, compile_selfdestruct_def] >> conj_tac >> windows_pure_tac
QED

Theorem dalloca_windows_compile_raw_revert:
  (!ct e. MEM e args ==> preserves_dalloca_windows window (cfn cenv ct e)) ==>
  preserves_dalloca_windows window (compile_call cfn cenv ret_ty ty RawRevert args d)
Proof
  Cases_on `args` >> TRY (Cases_on `t`) >>
  simp[dalloca_windows_result_state, compile_call_def, LET_THM, pairTheory.UNCURRY] >>
  rpt strip_tac >> finish_window_state
    [dalloca_windows_lower_value, cj 1 dalloca_windows_raw_revert_and_selfdestruct]
QED

Theorem dalloca_windows_compile_selfdestruct:
  (!ct e. MEM e args ==> preserves_dalloca_windows window (cfn cenv ct e)) ==>
  preserves_dalloca_windows window (compile_call cfn cenv ret_ty ty SelfDestructTarget args d)
Proof
  Cases_on `args` >> TRY (Cases_on `t`) >>
  simp[dalloca_windows_result_state, compile_call_def, LET_THM, pairTheory.UNCURRY] >>
  rpt strip_tac >> finish_window_state
    [dalloca_windows_lower_value, cj 2 dalloca_windows_raw_revert_and_selfdestruct]
QED

Theorem dalloca_windows_compile_raw_log:
  (!ct e. MEM e args ==> preserves_dalloca_windows window (cfn cenv ct e)) /\
  (!ct topics e. MEM topics args /\ MEM e (raw_log_topic_exprs topics) ==>
     preserves_dalloca_windows window (cfn cenv ct e)) ==>
  preserves_dalloca_windows window (compile_call cfn cenv ret_ty ty RawLog args d)
Proof
  Cases_on `args` >> TRY (Cases_on `t`) >> TRY (Cases_on `t'`) >> strip_tac >>
  fs[] >>
  TRY (`preserves_dalloca_windows window
      (compile_multi_exprs cfn cenv (raw_log_topic_exprs h))` by
    (irule dalloca_windows_multi_exprs >> metis_tac[])) >>
  simp[dalloca_windows_result_state, compile_call_def, LET_THM, pairTheory.UNCURRY] >>
  rpt strip_tac >> windows_tac [] >>
  finish_window_state [dalloca_windows_lower_value, dalloca_windows_alloc_buffer]
QED

Theorem dalloca_windows_store_byte_chunks[local]:
  !ptr bs off. preserves_dalloca_windows window (compile_store_byte_chunks ptr bs off)
Proof
  ho_match_mp_tac compile_store_byte_chunks_ind >>
  rpt conj_tac >> rpt gen_tac >> rpt strip_tac >>
  simp[Once compile_store_byte_chunks_def] >> windows_pure_tac >>
  fs[] >> first_assum irule >> simp[]
QED

Theorem dalloca_windows_bytelike_literal:
  preserves_dalloca_windows window (compile_bytelike_literal bytes maxlen)
Proof
  simp[compile_bytelike_literal_def] >> windows_tac [dalloca_windows_store_byte_chunks]
QED

Theorem dalloca_windows_simple_values:
  preserves_dalloca_windows window (compile_literal_vv ty lit) /\
  preserves_dalloca_windows window (compile_name_vv cenv ty id) /\
  preserves_dalloca_windows window (compile_ifexp_arm cenv res_ty arm_ty vv)
Proof
  Cases_on `lit` >> TRY (rename1 `BoolL b` >> Cases_on `b`) >>
  simp[compile_literal_vv_def, compile_name_vv_def, compile_ifexp_arm_def] >>
  rpt conj_tac >>
  windows_tac [dalloca_windows_bytelike_literal, dalloca_windows_store_memory,
               dalloca_windows_unwrap_value]
QED

Theorem dalloca_windows_snapshot:
  preserves_dalloca_windows window (compile_snapshot_vv cenv mut vv)
Proof
  simp[compile_snapshot_vv_def] >>
  windows_tac [dalloca_windows_materialize_vv, dalloca_windows_unwrap_value]
QED

Theorem dalloca_windows_ext_call_args:
  !args tys. (!e. MEM e args ==>
    preserves_dalloca_windows window (cfn cenv (expr_type e) e)) ==>
    preserves_dalloca_windows window (compile_ext_call_args cfn cenv kw_es tys args)
Proof
  Induct >> Cases_on `tys` >>
  simp[compile_ext_call_args_def, dalloca_windows_return] >> rpt strip_tac >>
  windows_tac [dalloca_windows_snapshot] >> metis_tac[]
QED

Theorem dalloca_windows_create_ctor_args[local]:
  !args. (!ct e. MEM e args ==> preserves_dalloca_windows window (cfn cenv ct e)) ==>
    preserves_dalloca_windows window (compile_create_ctor_args cfn cenv args)
Proof
  Induct >> simp[compile_create_ctor_args_def, dalloca_windows_return] >> rpt strip_tac >>
  windows_tac [dalloca_windows_snapshot] >> metis_tac[]
QED

Theorem dalloca_windows_extcall_setup[local]:
  preserves_dalloca_windows window (compile_extcodesize_check addr) /\
  preserves_dalloca_windows window (compile_return_value_decode min_sz max_sz)
Proof
  simp[compile_extcodesize_check_def, compile_return_value_decode_def] >>
  conj_tac >> windows_pure_tac
QED

Theorem dalloca_windows_default_return_path[local]:
  preserves_dalloca_windows window
    (compile_default_return_path cenv ret_ty default_ty buf dst default_op addr
      skip min_sz max_sz dec_info)
Proof
  simp[compile_default_return_path_def] >>
  windows_tac [dalloca_windows_store_memory, dalloca_windows_extcall_setup,
               dalloca_windows_abi_decode]
QED

Theorem dalloca_windows_abi_encode_value_rows[local]:
  !rows off.
    preserves_dalloca_windows window (compile_abi_encode_value_rows cenv dst cursor off rows)
Proof
  Induct >> simp[compile_abi_encode_value_rows_def, dalloca_windows_return] >>
  Cases >> simp[compile_abi_encode_value_rows_def, LET_THM] >>
  windows_tac [dalloca_windows_unwrap_value, dalloca_windows_store_memory,
               dalloca_windows_abi_encode]
QED

Theorem dalloca_windows_abi_encode_values:
  preserves_dalloca_windows window (compile_abi_encode_values_to_buf cenv dst rows)
Proof
  simp[compile_abi_encode_values_to_buf_def] >>
  windows_tac [dalloca_windows_abi_encode_value_rows]
QED

Theorem dalloca_windows_external_call_kwargs[local]:
  preserves_dalloca_windows window
    (compile_external_call_kwargs cenv addr vs tys abi_sz mid ret_sz min_sz
      ret_mem static val_op gas skip has_default default_op ret_ty default_ty dec_info)
Proof
  simp[compile_external_call_kwargs_def] >>
  windows_tac [dalloca_windows_abi_encode_values,
               dalloca_windows_extcall_setup, dalloca_windows_abi_decode,
               dalloca_windows_default_return_path]
QED

Theorem dalloca_windows_compile_ext_call:
  (!ct e. MEM e args ==> preserves_dalloca_windows window (cfn cenv ct e)) ==>
  preserves_dalloca_windows window
    (compile_call cfn cenv rt ty (ExtCall use_static skip signature opts) args d)
Proof
  PairCases_on `signature` >> Cases_on `args` >> simp[] >> TRY strip_tac >>
  TRY (`preserves_dalloca_windows window
      (compile_ext_call_args cfn cenv (DROP (LENGTH signature1) t)
        (MAP (lowered_value_type cenv) (TAKE (LENGTH signature1) t))
        (TAKE (LENGTH signature1) t))` by
    (irule dalloca_windows_ext_call_args >> metis_tac[MEM_TAKE])) >>
  TRY (`preserves_dalloca_windows window
      (compile_ext_call_kwargs cfn cenv signature2 opts (DROP (LENGTH signature1) t))` by
    (irule dalloca_windows_ext_call_kwargs >> metis_tac[MEM_DROP_IMP])) >>
  simp[dalloca_windows_result_state, compile_call_def, LET_THM, pairTheory.UNCURRY] >>
  rpt strip_tac >> windows_tac [] >> gvs[] >>
  finish_window_state [dalloca_windows_lower_value, dalloca_windows_external_call_kwargs]
QED

Theorem dalloca_windows_create_dispatch[local]:
  preserves_dalloca_windows window (compile_create_dispatch code_ptr len v salt rof)
Proof
  Cases_on `salt` >> simp[compile_create_dispatch_def, compile_check_create_result_def] >>
  windows_pure_tac
QED

Theorem dalloca_windows_create_proxy_buf[local]:
  preserves_dalloca_windows window (compile_create_proxy_buf target)
Proof
  simp[compile_create_proxy_buf_def] >> windows_pure_tac
QED

Theorem dalloca_windows_create_proxy_call[local]:
  (!ct e. MEM e args ==> preserves_dalloca_windows window (cfn cenv ct e)) ==>
  preserves_dalloca_windows window
    (compile_create_call cfn cenv CreateMinimalProxy salted rof args)
Proof
  Cases_on `args` >> TRY (Cases_on `t`) >> simp[] >> TRY strip_tac >>
  simp[compile_create_call_def, AllCaseEqs()] >>
  windows_tac [dalloca_windows_lower_value, dalloca_windows_create_dispatch,
    dalloca_windows_create_proxy_buf, dalloca_windows_create_salt] >>
  irule dalloca_windows_create_salt >>
  Cases_on `salted` >> gvs[] >> rpt strip_tac >> gvs[] >>
  Cases_on `t'` >> gvs[]
QED

Theorem dalloca_windows_create_snapshot[local]:
  preserves_dalloca_windows window (compile_create_snapshot cenv vv ty)
Proof
  simp[compile_create_snapshot_def, compile_copy_memory_dynamic_def] >>
  windows_tac [dalloca_windows_imm_copy, compile_slot_to_memory_def,
               compile_word_copy_loop_def, compile_word_copy_loop_op_def,
               dalloca_windows_word_copy]
QED

Theorem dalloca_windows_raw_create[local]:
  (!ct e. e = code_e \/ e = value_e \/ MEM e ctor_args \/ salt_e = SOME e ==>
     preserves_dalloca_windows window (cfn cenv ct e)) ==>
  preserves_dalloca_windows window (compile_raw_create cfn cenv code_e value_e ctor_args salt_e rof)
Proof
  strip_tac >>
  simp[compile_raw_create_def, compile_copy_memory_dynamic_def] >>
  windows_tac [dalloca_windows_create_snapshot, dalloca_windows_create_dispatch,
               dalloca_windows_abi_encode_values, dalloca_windows_create_ctor_args,
               dalloca_windows_lower_value, dalloca_windows_create_salt] >>
  metis_tac[]
QED

Theorem dalloca_windows_compile_raw_create[local]:
  (!ct e. MEM e args ==> preserves_dalloca_windows window (cfn cenv ct e)) ==>
  preserves_dalloca_windows window (compile_create_call cfn cenv RawCreate salted rof args)
Proof
  Cases_on `args` >> TRY (Cases_on `t`) >> simp[] >> TRY strip_tac >>
  simp[compile_create_call_def] >> windows_pure_tac >>
  TRY (irule dalloca_windows_raw_create >> rpt strip_tac) >>
  gvs[] >> first_assum irule >>
  metis_tac[MEM_FRONT_NOT_NIL, MEM_LAST_NOT_NIL]
QED

Theorem dalloca_windows_blueprint_args[local]:
  (!ct e. MEM e args ==> preserves_dalloca_windows window (cfn cenv ct e)) ==>
  preserves_dalloca_windows window
    (compile_create_blueprint_args cfn cenv raw later_es args)
Proof
  strip_tac >> Cases_on `raw`
  >- (Cases_on `args`
      >- (simp[compile_create_blueprint_args_def] >> windows_pure_tac) >>
      rename1 `compile_create_blueprint_args _ _ _ _ (e::es)` >>
      Cases_on `es`
      >- (`preserves_dalloca_windows window (cfn cenv (expr_type e) e)` by simp[] >>
          simp[compile_create_blueprint_args_def] >>
          windows_tac [dalloca_windows_snapshot, dalloca_windows_unwrap_value]) >>
      simp[compile_create_blueprint_args_def] >> windows_pure_tac) >>
  Cases_on `args = []`
  >- simp[compile_create_blueprint_args_def, dalloca_windows_return] >>
  `preserves_dalloca_windows window (compile_create_ctor_args cfn cenv args)` by
    (irule dalloca_windows_create_ctor_args >> first_assum ACCEPT_TAC) >>
  simp[compile_create_blueprint_args_def] >>
  windows_tac [dalloca_windows_abi_encode_values]
QED

Theorem dalloca_windows_blueprint_check[local]:
  preserves_dalloca_windows window
    (compile_create_blueprint_check is_lit target offset)
Proof
  Cases_on `is_lit` >> simp[compile_create_blueprint_check_def] >>
  windows_pure_tac
QED

Theorem dalloca_windows_blueprint_call[local]:
  (!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) /\
  (!ct e. MEM e args ==> preserves_dalloca_windows window (cfn cenv ct e)) ==>
  preserves_dalloca_windows window
    (compile_create_call cfn cenv (CreateFromBlueprint raw) salted rof args)
Proof
  strip_tac >>
  Cases_on `args` >- (simp[compile_create_call_def] >> windows_pure_tac) >>
  rename1 `compile_create_call _ _ _ _ _ (_::rest)` >>
  Cases_on `rest` >- (simp[compile_create_call_def] >> windows_pure_tac) >>
  rename1 `compile_create_call _ _ _ _ _ (_::_::rest)` >>
  Cases_on `rest`
  >- (Cases_on `salted` >> simp[compile_create_call_def] >> windows_pure_tac) >>
  rename1 `compile_create_call _ _ _ _ _ (_::_::_::tail)` >>
  Cases_on `salted` >> Cases_on `tail` >>
  fs[compile_create_call_def] >>
  windows_tac [dalloca_windows_create_blueprint_append,
    dalloca_windows_lower_value, dalloca_windows_create_salt,
    dalloca_windows_blueprint_args, dalloca_windows_blueprint_check] >>
  irule dalloca_windows_blueprint_args >> fs[] >> metis_tac[]
QED

Theorem dalloca_windows_compile_call_blueprint:
  (!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) /\
  (!ct e. MEM e args ==> preserves_dalloca_windows window (cfn cenv ct e)) ==>
  preserves_dalloca_windows window
    (compile_call cfn cenv rt ty (CreateTarget (CreateFromBlueprint raw) salted rof order)
      args d)
Proof
  strip_tac >>
  `preserves_dalloca_windows window
      (compile_create_call cfn cenv (CreateFromBlueprint raw) salted rof args)` by
    metis_tac[dalloca_windows_blueprint_call] >>
  fs[preserves_dalloca_windows_def, compile_call_def, as_stack_val_def] >>
  rpt strip_tac >>
  Cases_on `compile_create_call cfn cenv (CreateFromBlueprint raw) salted rof args st` >>
  gvs[as_stack_val_def] >> metis_tac[]
QED

Theorem dalloca_windows_compile_call:
  (!chunk. raw_call_dalloca_chunk chunk 1 ==> window chunk 1) /\
  (!chunk. create_copy_dalloca_chunk chunk 5 ==> window chunk 5) /\
  ((!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) \/
   (!raw salted rof order. target <> CreateTarget (CreateFromBlueprint raw) salted rof order)) /\
  (!ct e. MEM e args ==> preserves_dalloca_windows window (cfn cenv ct e)) /\
  (!ct id e.
     target = IntCall id /\ MEM e (omitted_defaults cenv (nsid_to_string id) (LENGTH args)) ==>
     preserves_dalloca_windows window (cfn (cenv_without_defaults cenv (nsid_to_string id)) ct e)) /\
  (!ct topics e. MEM topics args /\ MEM e (raw_log_topic_exprs topics) ==>
     preserves_dalloca_windows window (cfn cenv ct e)) ==>
  preserves_dalloca_windows window (compile_call cfn cenv rt ty target args d)
Proof
  Cases_on `target` >> rpt strip_tac >> gvs[] >>
  TRY (rename1 `preserves_dalloca_windows _ (compile_call _ _ _ _ (CreateTarget ck _ _ _) _ _)` >>
       Cases_on `ck` >> gvs[]) >>
  TRY (simp[dalloca_windows_result_state, compile_call_def, dalloca_windows_state_wrappers,
            pairTheory.UNCURRY] >> rpt strip_tac >>
       finish_window_state [dalloca_windows_create_proxy_call,
                             dalloca_windows_compile_raw_create] >> NO_TAC) >>
  TRY (FIRST (map irule
    [dalloca_windows_compile_internal_call, dalloca_windows_compile_ext_call,
     dalloca_windows_compile_send, dalloca_windows_raw_call_target,
     dalloca_windows_raw_call_calldata, dalloca_windows_compile_raw_log,
     dalloca_windows_compile_raw_revert, dalloca_windows_compile_selfdestruct,
     dalloca_windows_compile_call_create_copy, dalloca_windows_compile_call_blueprint])) >>
  simp[] >> first_assum ACCEPT_TAC
QED

Theorem dalloca_windows_indexing:
  preserves_dalloca_windows window (compile_mapping_subscript bas key) /\
  preserves_dalloca_windows window (compile_keccak256_key key flag) /\
  preserves_dalloca_windows window (compile_tuple_subscript bas off) /\
  preserves_dalloca_windows window (compile_dynarray_pop bas stride sz ctor imm loc) /\
  (preserves_dalloca_windows window (loader bas) ==>
   preserves_dalloca_windows window
     (compile_array_subscript bas idx dynamic n stride sz signed loader))
Proof
  simp[compile_mapping_subscript_def, compile_keccak256_key_def,
       compile_tuple_subscript_def, compile_dynarray_pop_def, compile_array_subscript_def] >>
  rpt conj_tac >> TRY strip_tac >> windows_tac [dalloca_windows_ptr_access]
QED

Theorem dalloca_windows_make_tuple:
  !args tys buf off. (!ct e. MEM e args ==> preserves_dalloca_windows window (cfn cenv ct e)) ==>
    preserves_dalloca_windows window (compile_make_tuple cfn cenv args tys buf off)
Proof
  Induct >> Cases_on `tys` >> simp[compile_make_tuple_def, dalloca_windows_return] >>
  rpt strip_tac >> windows_tac [dalloca_windows_store_memory, dalloca_windows_unwrap_value] >>
  metis_tac[]
QED

Theorem dalloca_windows_make_array_elems[local]:
  !args off. (!ct e. MEM e args ==> preserves_dalloca_windows window (cfn cenv ct e)) ==>
    preserves_dalloca_windows window (compile_make_array_elems cfn cenv args ty sz lw buf off)
Proof
  Induct >> simp[compile_make_array_elems_def, dalloca_windows_return] >>
  rpt strip_tac >> windows_tac [dalloca_windows_store_memory, dalloca_windows_unwrap_value] >>
  metis_tac[]
QED

Theorem dalloca_windows_make_array:
  (!ct e. MEM e args ==> preserves_dalloca_windows window (cfn cenv ct e)) ==>
  preserves_dalloca_windows window (compile_make_array cfn cenv args ty sz lw buf)
Proof
  strip_tac >> simp[compile_make_array_def] >>
  windows_tac [dalloca_windows_make_array_elems] >> metis_tac[dalloca_windows_make_array_elems]
QED

Theorem dalloca_windows_concat:
  !args infos. (!ct e. MEM e args ==> preserves_dalloca_windows window (cfn cenv ct e)) ==>
    preserves_dalloca_windows window (compile_concat cfn cenv args dst infos off)
Proof
  Induct >> Cases_on `infos` >> simp[compile_concat_def, dalloca_windows_return] >>
  PairCases_on `h` >> simp[compile_concat_def] >> rpt strip_tac >>
  windows_tac [dalloca_windows_lower_value] >> metis_tac[]
QED

Theorem dalloca_windows_abi_encode_args:
  !args. (!ct e. MEM e args ==> preserves_dalloca_windows window (cfn cenv ct e)) ==>
    preserves_dalloca_windows window (compile_abi_encode_args cfn cenv args)
Proof
  simp[compile_abi_encode_args_def, dalloca_windows_ext_call_args]
QED

Theorem dalloca_windows_abi_encode_payload:
  preserves_dalloca_windows window (compile_abi_encode_payload cenv single vs tys dst)
Proof
  Cases_on `single` >> simp[compile_abi_encode_payload_def] >>
  windows_tac [dalloca_windows_unwrap_value, dalloca_windows_abi_encode, dalloca_windows_abi_encode_values]
QED

Theorem dalloca_windows_store_abi_tuple:
  !vals off. preserves_dalloca_windows window (compile_store_abi_tuple cenv dst off vals)
Proof
  Induct >> simp[compile_store_abi_tuple_def, dalloca_windows_return] >>
  Cases >> simp[compile_store_abi_tuple_def] >> windows_tac [dalloca_windows_copy_memory]
QED

Theorem dalloca_windows_get_target_ptr:
  !target. (!ct e. supported_target_exists ($= e) target ==>
     preserves_dalloca_windows window (cfn cenv ct e)) ==>
  preserves_dalloca_windows window (compile_get_target_ptr cfn cenv target)
Proof
  `(!e:expr. T) /\
   (!target. (!ct e. supported_target_exists ($= e) target ==>
      preserves_dalloca_windows window (cfn cenv ct e)) ==>
    preserves_dalloca_windows window (compile_get_target_ptr cfn cenv target))`
    suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >>
  simp[compile_get_target_ptr_def, supported_expr_exists_def] >> rpt strip_tac >>
  windows_tac [dalloca_windows_indexing, dalloca_windows_ptr_access,
               dalloca_windows_lower_value] >>
  irule dalloca_windows_lower_value >> first_assum irule >>
  disj2_tac >> irule supported_expr_exists_root >> simp[]
QED

Theorem dalloca_windows_compile_subscript:
  (!ct. preserves_dalloca_windows window (cfn cenv ct base_e)) /\
  (!ct. preserves_dalloca_windows window (cfn cenv ct idx_e)) ==>
  preserves_dalloca_windows window (compile_subscript cfn cenv rt ty base_e idx_e)
Proof
  strip_tac >> simp[compile_subscript_def] >>
  windows_tac [dalloca_windows_indexing, dalloca_windows_ptr_access,
               dalloca_windows_lower_value, dalloca_windows_snapshot]
QED

Theorem dalloca_windows_compile_attribute:
  preserves_dalloca_windows window (cfn cenv ty base_e) ==>
  preserves_dalloca_windows window (compile_attribute cfn cenv rt ty base_e fld)
Proof
  strip_tac >> simp[compile_attribute_def] >> windows_pure_tac
QED

Theorem dalloca_windows_compile_struct_lit:
  !flds buf off. (!ct e. MEM e (MAP SND flds) ==>
    preserves_dalloca_windows window (cfn cenv ct e)) ==>
  preserves_dalloca_windows window (compile_struct_lit cfn cenv ty flds buf off)
Proof
  Induct >> simp[compile_struct_lit_def, dalloca_windows_return] >>
  Cases >> simp[compile_struct_lit_def] >> rpt strip_tac >>
  windows_tac [dalloca_windows_unwrap_value, dalloca_windows_store_memory] >>
  metis_tac[]
QED
