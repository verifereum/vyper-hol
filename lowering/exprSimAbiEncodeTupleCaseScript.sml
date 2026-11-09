Theory exprSimAbiEncodeTupleCase
Ancestors
  exprSimAbiEncodeTupleCompletionFresh exprSimAbiEncodeArgs exprSimAbiEncodeNonwordCase
  exprSimSource vyperTypeABI vyperTypeExprSoundness vyperTypeInvariants vyperABI
  exprSimHypsDefs exprSimDefs exprLowering exprBopLowering exprLoweringProps
  exprSimHash exprSimWordArgs exprSimProps abiEncodeArgsSim
  abiTupleEncodePrepare abiTupleEncodeMemory abiBuiltinAllocation
  exprSimAbiEncodeOblivious compileEnv emitHelper emitHelperProps fragExec
  gasOutcome gasSummary gasSummaryCompose gasExemptCert fragGasMode fragGasPath
  vyperAST vyperInterpreter vyperState vyperContext list
  vyperEvalExprPreservesScopesDom exprSimAbiEncodeRuntimeInputs
  pair vyperTypeSystem vyperTypeDefaults

Theorem abi_encode_tuple_lowering_shape[local]:
  ~(LENGTH args = 1 /\ ~ensure) ==>
  compile_expr ce cty (TypeBuiltin ann (AbiEncode ensure mid) target args) sa =
    let (ops,st) = compile_abi_encode_args compile_expr ce args sa in
    let (buf,allocated) = compile_alloc_buffer (type_memory_bytes ce (TupleT (MAP expr_type args))) st in
    let (_,staged) = compile_store_abi_tuple ce buf.buf_operand 0 (ZIP (ops,MAP expr_type args)) allocated in
    as_ptr_val ann LocMemory
      (lower_abi_encode ensure (OPTION_MAP bytes_method_id_word mid) buf.buf_operand
        (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP expr_type args)))
        (abi_size_bound ce.ce_struct_fields (TupleT (MAP expr_type args))) staged)
Proof
  strip_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def] >>
  simp[Once (CONJUNCT2 (CONJUNCT2 compile_expr_raw_def)),
       compile_type_builtin_dispatch_body_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[expr_size_def, list_size_def, expr_type_def, comp_bind_def] >>
  AP_TERM_TAC >> AP_THM_TAC >>
  irule compile_abi_encode_args_callback_cong >>
  rpt strip_tac >> simp[FUN_EQ_THM] >> rpt gen_tac >>
  simp[exprRecursionRegressionTheory.expr_size_member]
QED

Theorem abi_encode_args_ci_mono[local]:
  !args ce st. ci_mono st (SND (compile_abi_encode_args compile_expr ce args st))
Proof
  Induct >> rpt gen_tac >> rewrite_tac[compile_abi_encode_args_def] >>
  simp[ci_mono_comp_return] >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[cj 1 compile_expr_ci_mono] >>
  rpt strip_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[ci_mono_compile_materialize_vv, ci_mono_unwrap_value]) >>
  rpt strip_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[] >>
  simp[ci_mono_comp_return]
QED

Theorem abi_encode_store_ci_mono[local]:
  !ce buf off elems sa.
    ci_mono sa (SND (compile_store_abi_tuple ce buf off elems sa))
Proof
  ho_match_mp_tac compile_store_abi_tuple_ind >> rpt strip_tac
  >- simp[compile_store_abi_tuple_def, ci_mono_comp_return] >>
  rewrite_tac[compile_store_abi_tuple_def] >> BETA_TAC >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >>
  rpt strip_tac >> irule ci_mono_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[ci_mono_emit_void, ci_mono_compile_copy_memory]) >>
  rpt strip_tac >> first_x_assum irule
QED

Theorem eval_expr_abi_encode_tuple_action[local]:
  1 <= LENGTH args ==>
  eval_expr cx (TypeBuiltin ann (AbiEncode ensure mid) target args) =
  bind (eval_exprs cx args)
    (\vs es. ((case evaluate_type_builtin cx (AbiEncode ensure mid) target (MAP expr_type args) vs of
      INL w => INL (Value w) | INR err => INR (Error err)),es))
Proof
  strip_tac >> rewrite_tac[FUN_EQ_THM] >> gen_tac >>
  simp[Once evaluate_def, type_check_def, type_builtin_args_length_ok_def,
    assert_def, ignore_bind_def, bind_def, return_def] >>
  Cases_on `eval_exprs cx args x` >> Cases_on `q` >>
  simp[lift_sum_def, bind_def, return_def, raise_def] >>
  rename1 `eval_exprs cx args x = (INL vs,ee)` >>
  Cases_on `evaluate_type_builtin cx (AbiEncode ensure mid) target (MAP expr_type args) vs` >>
  simp[bind_def, return_def, raise_def]
QED

Theorem compile_abi_encode_tuple_vv_case:
  exprs_case nocalls ctx func ce cx args /\
  ~(LENGTH args = 1 /\ ~ensure) ==>
  expr_vv_case nocalls ctx func ce cx (TypeBuiltin ann (AbiEncode ensure mid) target args)
Proof
  strip_tac >> rewrite_tac[expr_vv_case_def] >> rpt strip_tac >>
  rewrite_tac[expr_vv_sim_def] >> rpt strip_tac >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  dep_rewrite.DEP_REWRITE_TAC [abi_encode_tuple_lowering_shape] >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[as_ptr_val_def] >> strip_tac >> gvs[] >>
  suspend "compose"
QED

Resume compile_abi_encode_tuple_vv_case[compose]:
  Cases_on `lower_abi_encode ensure (OPTION_MAP bytes_method_id_word mid) buf.buf_operand
    (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP expr_type args)))
    (abi_size_bound ce.ce_struct_fields (TupleT (MAP expr_type args))) staged` >>
  rename1 `lower_abi_encode _ _ _ _ _ staged = (out,final)` >>
  gvs[as_ptr_val_def] >>
  `ci_mono sa st` by metis_tac[abi_encode_args_ci_mono, SND] >>
  `cs_extends sa st /\ sa.cs_next_var <= st.cs_next_var /\ sa.cs_next_id <= st.cs_next_id` by
    fs[ci_mono_def] >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule_all abi_tuple_encode_stage_shape >> strip_tac >>
  `cs_extends st staged /\ cs_extends st allocated` by
    (conj_tac >- (irule cs_extends_same_block >> simp[]) >>
     `ci_mono st allocated` by metis_tac[ci_mono_compile_alloc_buffer, SND] >>
     fs[ci_mono_def]) >>
  `!l. buf.buf_operand <> Label l` by
    (qpat_x_assum `emit_op ALLOCA _ st = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
       fresh_id_def, emit_def, comp_return_def] >> strip_tac >> gvs[] >>
     Cases_on `buf.buf_operand` >> gvs[]) >>
  drule_all lower_abi_encode_frag_facts >> strip_tac >>
  `cs_extends allocated staged` by
    (`ci_mono allocated staged` by metis_tac[abi_encode_store_ci_mono, SND] >>
     fs[ci_mono_def]) >>
  `cs_extends st final` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa st func /\ fn_has_code st final func` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code st staged func /\ fn_has_code staged final func` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code st allocated func` by metis_tac[fn_has_code_split] >>
  `local_ptrs_reserved ce st` by metis_tac[local_ptrs_reserved_next_var] >>
  `LENGTH ops = LENGTH args` by metis_tac[compile_abi_encode_args_length, FST] >>
  `abi_tuple_bytes ce (ZIP (ops,MAP expr_type args)) =
    type_memory_bytes ce (TupleT (MAP expr_type args))` by
    (irule abi_tuple_encode_bytes_zip >> simp[]) >>
  `1 <= LENGTH args` by
    (fs[expr_body_pre_def, well_typed_expr_def, well_typed_type_builtin_args_def,
       type_builtin_args_length_ok_def] >> Cases_on `args` >> gvs[]) >>
  `!gs vs ee initial.
    eval_exprs cx args (es with gas_obs := gs) = (INL vs,ee) /\ ee.gas_obs = [] /\
    abi_args_post ctx func ce cx es sa st s0 ee args ops vs initial /\
    EVERY (abi_decoder_operand_live st.cs_next_var) ops /\ ~initial.vs_halted /\
    initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?marks. gas_summary_at F (ctx,func) marks
      (\ee. ((case evaluate_type_builtin cx (AbiEncode ensure mid) target (MAP expr_type args) vs of
        INL w => INL (Value w) | INR err => INR (Error err)),ee)) (ee,initial)
      (\res ee t. ?tv. res = INL tv /\
        vv_post ctx func ce cx (TypeBuiltin ann (AbiEncode ensure mid) target args)
          es sa final s0 ee tv (LocatedValue ann (mk_ptr out LocMemory)) t /\
        t.vs_current_bb = final.cs_current_bb /\ t.vs_inst_idx = LENGTH final.cs_current_insts)
      (\res ee r. expr_exit res r)` by (rpt strip_tac >> suspend "success") >>
  drule_all compile_abi_encode_args_case_gas_sim >>
  suspend "outcome"
QED

Resume compile_abi_encode_tuple_vv_case[outcome]:
  asm_simp_tac (srw_ss()) [eval_expr_abi_encode_tuple_action] >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >>
      gvs[]
      >- (`eval_exprs cx args (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
              (INL vs, es_end with gas_obs := [])` by
            (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
               (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
             strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
          `~t.vs_halted` by
            metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
          qpat_x_assum `!gs vs ee initial. _`
            (qspecl_then [`gas_explicit marks s0.vs_gas_readings`, `vs`,
                          `es_end with gas_obs := []`, `t`] mp_tac) >>
          (impl_tac >- simp[]) >> strip_tac >>
          rename1 `gas_summary_at F _ right _ _ _ _` >>
          qexists `marks ++ right` >> disj1_tac >>
          qpat_x_assum `gas_summary_at F _ right _ _ _ _`
            (mp_tac o REWRITE_RULE [gas_summary_at_def]) >>
          disch_then (qx_choosel_then [`fres`, `fin`, `fr`]
            (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
          rewrite_tac[gas_summary_at_def] >>
          qexistsl [`fres`, `fin`, `fr`] >>
          conj_tac >- (irule gas_marked_exec_bind_normal >>
            goal_assum (drule_at (Pat `gas_marked_exec _ _ (eval_exprs _ _) _ _ _ _ _`)) >> simp[]) >>
          asm_rewrite_tac[]) >>
      Cases_on `res` >> gvs[wb_args_exit_def] >>
      rename1 `expr_exit (INR exc) r` >>
      qexists `marks` >> disj1_tac >> rewrite_tac[gas_summary_at_def] >>
      qexistsl [`INR exc`, `es_end`, `r`] >>
      conj_tac >- (irule gas_marked_exec_bind_exception >> simp[]) >>
      Cases_on `exc` >> Cases_on `r` >> gvs[wb_args_exit_def, expr_exit_def] >>
      rename1 `Error err` >> Cases_on `err` >> gvs[expr_exit_def]) >>
  qexists `marks` >> disj2_tac >>
  metis_tac[gas_exempt_cert_error_values, ignore_bind_def, vyperStateTheory.bind_assoc]
QED

Resume compile_abi_encode_tuple_vv_case[success]:
  `expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) target args)
     (es with gas_obs := gs)` by simp[] >>
  drule_all abi_encode_body_args_runtime_typed >>
  simp_tac (srw_ss()) [exprs_runtime_typed_def] >> strip_tac >>
  `LIST_REL (\ty tv. evaluate_type (get_tenv cx) ty = SOME tv)
    (MAP expr_type args) tvs` by gvs[LIST_REL_MAP1, combinTheory.o_DEF] >>
  `values_have_types tvs vs` by simp[values_have_types_LIST_REL] >>
  drule_all (cj 2 vyper_to_abi_total) >> strip_tac >>
  `target = TupleT (MAP expr_type args)` by
    (qpat_assum `expr_body_pre _ _ _ _ es` mp_tac >>
     qpat_assum `LENGTH args = 1 ==> ensure` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[expr_body_pre_def, well_typed_expr_def, type_builtin_result_ok_def] >>
     strip_tac >> strip_tac >>
     Cases_on `args` >> gvs[expr_type_def] >>
     Cases_on `t` >> gvs[expr_type_def]) >>
  `evaluate_type_builtin cx (AbiEncode ensure mid) target (MAP expr_type args) vs =
     INL (BytesV (abi_encode_method_id_bytes mid ++
       enc (vyper_to_abi_type (get_tenv cx) target) (ListV avs)))` by
    (simp[evaluate_type_builtin_def, needs_external_call_wrap_def,
       evaluate_abi_encode_bytes_def, vyper_to_abi_def] >>
     Cases_on `args` >- (Cases_on `ensure` >> gvs[]) >>
     Cases_on `t` >> gvs[]) >>
  drule eval_exprs_preserves_scopes_dom >> simp[] >> strip_tac >>
  `abi_args_post ctx func ce cx (es with gas_obs := gs) sa st s0 ee args ops vs initial` by
    (qpat_assum `abi_args_post _ _ _ _ es _ _ _ _ _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[abi_args_post_def, loweringPostsTheory.wb_frame_def, loweringPostsTheory.locals_kept_def] >>
     rpt strip_tac >> metis_tac[]) >>
  `?actual. gas_marked_path F ctx func initial 0 (OK actual) /\
    ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    vv_post ctx func ce cx (TypeBuiltin ann (AbiEncode ensure mid) target args)
      (es with gas_obs := gs) sa final s0 ee
      (Value (BytesV (abi_encode_method_id_bytes mid ++
        enc (vyper_to_abi_type (get_tenv cx) target) (ListV avs))))
      (LocatedValue ann <|ptr_operand := out; ptr_location := LocMemory|>) actual` by
    (gvs[] >> irule (SRULE [expr_type_def] abi_encode_tuple_counted_success_fresh_free) >>
     simp[expr_type_def] >> conj_tac >- (qexists `env` >> simp[]) >>
     goal_assum (drule_at (Pat `abi_args_post _ _ _ _ (es with gas_obs := gs) _ _ _ _ _ _ _ _`)) >>
     qexistsl [`allocated`, `buf`, `staged`] >> simp[]) >>
  `ee with gas_obs := [] = ee` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  qexists `[]` >> simp[gas_summary_at_def] >>
  qexistsl [`INL (Value (BytesV (abi_encode_method_id_bytes mid ++
    enc (vyper_to_abi_type (get_tenv cx) target) (ListV avs))))`, `ee`, `OK actual`] >>
  simp[gas_marked_exec_def] >>
  mp_tac (GEN_ALL (Q.INST
    [`p` |-> `<|ptr_operand := out; ptr_location := LocMemory|>`,
     `q` |-> `mk_ptr out LocMemory`] abi_encode_vv_post_pointer_cong)) >>
  simp[contextTheory.mk_ptr_def] >>
  disch_then (fn th => rewrite_tac[GSYM th]) >>
  gvs[] >>
  qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[loweringPostsTheory.vv_post_def, loweringPostsTheory.locals_kept_def,
    contextTheory.mk_ptr_def] >> rpt strip_tac >> metis_tac[]
QED

Finalise compile_abi_encode_tuple_vv_case
