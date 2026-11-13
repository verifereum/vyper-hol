(* Force the counted in-memory slice result without a target suffix. *)
Theory bodyMemBiCalldataSliceRead
Ancestors
  bodyMemBiCalldataSliceCompose bodyMemBiCalldataSliceFacts
  exprSimMemorySource exprSimMemDefs exprSimDefs exprSimProps
  exprSimUnwrapProps loweringPosts exprLowering exprLoweringProps
  gasOutcome gasSummary gasSummaryCompose gasExemptCert gasContext
  vyperInterpreter vyperState vyperAST vyperTypeSystem
  loweringSlice compileEnv venomState context exprSimMemoryPath exprSimCalldataSlice
  gasStorage vyperStorageTrace vyperStorageFootprint

Theorem compile_calldata_slice_sim_mem:
  expr_body_pre cenv cx env
    (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e]) es /\
  expr_type e = BaseT (UintT 256) /\
  expr_sim_mem ctx func cenv cx (expr_type e) e es ==>
  expr_sim_mem ctx func cenv cx ty
    (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e]) es
Proof
  strip_tac >>
  `expr_vv_sim_mem ctx func cenv cx ty
    (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e]) es` by
    metis_tac[compile_calldata_slice_vv_sim_mem] >>
  simp[expr_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >>
  Cases_on `compile_expr cenv ty
    (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e]) sa` >>
  rename1 `_ = (vv,sm)` >> simp[] >>
  `?ptr. vv = LocatedValue (BaseT (BytesT (Dynamic n)))
    (mk_ptr ptr LocMemory)` by
    (qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
     simp[compile_calldata_slice_parts] >>
     Cases_on `lower_value compile_expr cenv (BaseT (UintT 256)) e sa` >>
     simp[] >>
     Cases_on `compile_slice_calldata q (Lit (n2w n))
       (type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))) r` >>
     simp[as_ptr_val_def] >> metis_tac[]) >>
  gvs[] >>
  simp[unwrap_memory_compile, mk_ptr_def, is_word_type_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  `gas_admissible (eval_expr cx
    (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e]))
    expr_vv_res_ok es` by metis_tac[forced_expr_admissible_raw] >>
  qpat_x_assum `expr_vv_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_mem_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `sb`,
    `LocatedValue (BaseT (BytesT (Dynamic n))) (mk_ptr op LocMemory)`, `s0`] mp_tac) >>
  (impl_tac >- simp[mk_ptr_def]) >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      irule gasStorageTheory.gas_bad_storage_at_bind_left >>
      simp[vyperStorageTraceTheory.storage_trace_frame_read_result])
  >- suspend "normal" >>
  suspend "exempt"
QED

Resume compile_calldata_slice_sim_mem[normal]:
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_summary_at_def] >>
  disch_then (qx_choose_then `res` (qx_choose_then `es_end`
    (qx_choose_then `r` (CONJUNCTS_THEN2 assume_tac mp_tac)))) >>
  reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
  >- (disch_then kall_tac >> qexists_tac `marks` >> disj1_tac >>
      irule gasStorageTheory.gas_bad_storage_at_bind_left >>
      simp[vyperStorageTraceTheory.storage_trace_frame_read_result] >>
      irule gasStorageTheory.gas_bad_storage_at_counted_prefix >>
      metis_tac[]) >>
  `valid_horizon cx st0 (storage_trace_horizon es_end.storage_trace)
     es_end.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  disch_then (DISJ_CASES_THEN (strip_assume_tac o BETA_RULE)) >>
  qexists_tac `marks` >> disj2_tac >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >> BETA_TAC
  >- suspend "success" >>
  suspend "exception"
QED

Resume compile_calldata_slice_sim_mem[exempt]:
  qexists_tac `marks` >> disj2_tac >> disj2_tac >>
  metis_tac[force_exempt_cert]
QED

Resume compile_calldata_slice_sim_mem[success]:
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
    (assume_tac o SIMP_RULE (srw_ss()) []) >>
  qpat_assum `!H. valid_horizon _ _ H es_end.storage_trace ==> _`
    (drule_then (qx_choose_then `tv` strip_assume_tac)) >>
  qpat_x_assum `res = INL tv` SUBST_ALL_TAC >>
  qpat_x_assum `!H. valid_horizon _ _ H es_end.storage_trace ==> _`
    (assume_tac o SIMP_RULE (srw_ss()) []) >>
  rename1 `r = OK t1` >>
  qpat_x_assum `r = OK t1` SUBST_ALL_TAC >>
  drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`) buffer_memory_marked_read >>
  simp[mk_ptr_def, is_word_type_def] >> strip_tac >>
  `read_result cx tv (es_end with gas_obs := []) =
     (INL v,es_end with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ (bind _ _) _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     qpat_x_assum `gas_marked_exec _ _ (eval_expr _ _) _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     simp[] >> rpt strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >>
     first_x_assum (qspec_then `[]` mp_tac) >>
     simp[bind_def]) >>
  `expr_store_bound cx
     (expr_type (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e]))
     v op t1` by
    (fs[vv_store_bound_def, expr_store_bound_def, mk_ptr_def] >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H es_end.storage_trace ==>
     expr_post H ctx func cenv cx
       (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e])
       es sa sb s0 (es_end with gas_obs := []) v op t1` by
    (rpt strip_tac >>
     qpat_assum `!H'. valid_horizon _ _ H' es_end.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     drule_all vv_post_read_result >> strip_tac >>
     drule expr_post_of_vv_post_memory >>
     simp[mk_ptr_def, is_word_type_def]) >>
  qexistsl_tac [`INL v`, `es_end with gas_obs := []`, `OK t1`] >>
  simp[]
QED

Resume compile_calldata_slice_sim_mem[exception]:
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
    (assume_tac o SIMP_RULE (srw_ss()) []) >>
  `expr_exit res r` by metis_tac[] >>
  Cases_on `res` >- gvs[expr_exit_def] >>
  qexistsl_tac [`INR y`, `es_end`, `r`] >> simp[] >>
  conj_tac
  >- (irule gas_marked_exec_bind_exception >> simp[]) >>
  Cases_on `r` >> Cases_on `y` >> gvs[expr_exit_def] >>
  rename1 `expr_exit (INR (Error err)) _` >>
  Cases_on `err` >> gvs[expr_exit_def]
QED

Finalise compile_calldata_slice_sim_mem
