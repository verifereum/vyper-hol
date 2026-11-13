(* Runtime data metadata is independent of instruction packaging. *)
Theory runtimeSymSrcData
Ancestors
  compileVyper vyperCompiler list
  runtimeSymSrcDataExpr runtimeSymSrcDataStmt runtimeSymSrcDataModule
  runtimeSymSrcDataExprCallbacks runtimeSymSrcDataExprAddressing
  runtimeSymSrcDataExprNonCallback runtimeSymSrcDataExprHelpers
  runtimeSymSrcDataContext runtimeSymSrcDataABI runtimeSymSrcDataFrame

Theorem extract_context_with_internals_data:
  extract_context_with_internals entry internal_fns st = SOME (ctx, data) ==>
  data = REVERSE st.cs_data_sections
Proof
  simp[extract_context_with_internals_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

Theorem runtime_data_frame_statements:
  (!c l t s. runtime_data_frame (compile_stmt c l t s)) /\
  (!c l t ss. runtime_data_frame (compile_stmts c l t ss))
Proof
  irule runtime_data_frame_compile_stmt_conditional >>
  simp[runtime_data_frame_lower_value, runtime_data_frame_get_target_ptr,
       runtime_data_frame_snapshot_vv, runtime_data_frame_binop,
       runtime_data_frame_compile_assign_value, runtime_data_frame_compile_store_at_loc,
       runtime_data_frame_compile_reason_message, runtime_data_frame_compile_revert_with_reason,
       runtime_data_frame_compile_log_eval_all, runtime_data_frame_compile_log_topic_ops,
       runtime_data_frame_compile_log_store_data, runtime_data_frame_compile_return_unlock,
       runtime_data_frame_compile_internal_return_from_env,
       runtime_data_frame_compile_external_return, runtime_data_frame_compile_tuple_unpack,
       runtime_data_frame_compile_iter_elem_copy,
       runtime_data_frame_keccak256_key, runtime_data_frame_mapping_subscript,
       runtime_data_frame_array_subscript, runtime_data_frame_bytelike_literal,
       runtime_data_frame_dynarray_append, runtime_data_frame_compile_tuple_store_all]
QED

(* Close the conditional module contracts at the expression/statement join. *)
val module_frames = [runtime_data_frame_statements,
  runtime_data_frame_decode_args, runtime_data_frame_register_positional_args,
  runtime_data_frame_create_kwarg_allocas, runtime_data_frame_init_kwargs,
  runtime_data_frame_entry_point_kwargs, runtime_data_frame_guarded_body,
  runtime_data_frame_external_function_body, runtime_data_frame_fallback_body,
  runtime_data_frame_internal_function, runtime_data_frame_external_fn_bodies,
  runtime_data_frame_internal_fn_bodies, runtime_data_frame_common_function_body,
  runtime_data_frame_group_entries, runtime_data_frame_external_groups,
  runtime_data_frame_group_dispatch_linear, runtime_data_frame_external_jobs,
  runtime_data_frame_lower_value];

Theorem runtime_data_frame_runtime_closed:
  runtime_data_frame
    (compile_generate_runtime sels ext int fb Linear buckets metadata dense info)
Proof
  irule runtime_data_frame_generate_runtime >> simp module_frames
QED

Theorem runtime_data_frame_grouped_runtime_closed:
  runtime_data_frame (compile_generate_grouped_runtime groups int fb)
Proof
  irule runtime_data_frame_generate_grouped_runtime >>
  simp module_frames >> conj_tac
  >- (rpt gen_tac >> irule runtime_data_frame_group_dispatch_linear >>
      rpt gen_tac >> irule runtime_data_frame_external_groups >>
      simp module_frames) >>
  gen_tac >> irule runtime_data_frame_external_jobs >> simp module_frames
QED

Theorem run_lowering_data_empty:
  run_lowering sels ext int fb policy buckets metadata dense info entry = SOME u ==>
  u.cu_data_segment = []
Proof
  simp[run_lowering_def] >> strip_tac >>
  `policy.rpol_frontend_dispatch = Linear` by fs[lowering_policy_ok_def] >>
  qpat_x_assum `_ = SOME u` mp_tac >> simp[] >> pairarg_tac >>
  gvs[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule extract_context_with_internals_data >> strip_tac >>
  mp_tac (REWRITE_RULE [runtime_data_frame_def]
    runtime_data_frame_runtime_closed) >>
  disch_then (qspec_then `initial_compile_state entry` mp_tac) >>
  simp[initial_compile_state_def] >> gvs[]
QED

Theorem run_grouped_lowering_data_empty:
  run_grouped_lowering groups int fb policy entry = SOME u ==>
  u.cu_data_segment = []
Proof
  simp[run_grouped_lowering_def] >> strip_tac >>
  qpat_x_assum `_ = SOME u` mp_tac >>
  pairarg_tac >> gvs[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule extract_context_with_internals_data >> strip_tac >>
  mp_tac (REWRITE_RULE [runtime_data_frame_def]
    runtime_data_frame_grouped_runtime_closed) >>
  disch_then (qspec_then `initial_compile_state entry` mp_tac) >>
  simp[initial_compile_state_def] >> gvs[]
QED

Theorem lower_vyper_runtime_unit_data_empty:
  lower_vyper_runtime_unit tops policy = SOME u ==> u.cu_data_segment = []
Proof
  Cases_on `classify_functions tops` >> PairCases_on `r` >>
  rw[lower_vyper_runtime_unit_def, AllCaseEqs()] >>
  metis_tac[run_lowering_data_empty, run_grouped_lowering_data_empty]
QED

Theorem lower_vyper_runtime_unit_data_bytes:
  lower_vyper_runtime_unit tops policy = SOME u ==>
  EVERY (\ds. EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
                        ds.ds_items) u.cu_data_segment
Proof
  strip_tac >> drule lower_vyper_runtime_unit_data_empty >> simp[]
QED
