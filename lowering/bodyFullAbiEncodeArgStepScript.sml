(* The conditional head of compile_abi_encode_args, at one joint endpoint. *)
Theory bodyFullAbiEncodeArgStep
Ancestors
  bodyFullPreds bodyFullAbiEncodeCapture bodyFullAbiEncodeBorrowed
  bodyFullAbiEncodeRetention bodyFullOfVV abiEncodeArgsSim
  abiTupleProps exprSimHyps exprSimSource gasOutcomeFullCompose
  gasShadowCompile exprSimAbiEncodeFramedArrayBody
  exprLowering compileEnv bodySimFull gasOutcomeFullCompose gasOutcomeFull
  abiEncodeArgsCase exprOperandVar abiBuiltinEncodeWord
  exprSimAbiEncodeArgsMaterializePath fragExec exprSimMemorySource
  bodyMemBopRestWordPath contextRawReachable unitMemInv

Theorem abi_encode_arg_step_full:
  body_expr_full_ok cx e /\ body_inv tops ctx ce cx /\
  expr_body_pre ce cx env e es /\
  compile_expr ce (expr_type e) e sa = (vv,mid) /\
  (if ~is_word_type (expr_type e) /\ exprs_can_mutate ce rest
   then compile_materialize_vv ce (lowered_value_type ce e) vv mid
   else unwrap_value ce vv mid) = (op,sb) /\
  compile_expr ce (expr_type e) (gas_shadow_expr e) shadow_sa = (vv,shadow_mid) /\
  (if ~is_word_type (expr_type e) /\ exprs_can_mutate ce rest
   then compile_materialize_vv ce (lowered_value_type ce e) vv shadow_mid
   else unwrap_value ce vv shadow_mid) = (op,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state mid shadow_mid /\
  gas_shadow_state sb shadow_sb /\ gas_shadow_context ctx shadow_ctx /\
  ctx_inst_ids_distinct ctx /\ gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  return_buf_frame d ce sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d ce cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx))
    (es,s0,G0,tn0)
    (\H rr ee G tn t. ?v tv.
      rr = INL v /\
      evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
      value_has_type tv v /\
      expr_post H ctx func ce cx e es sa sb s0 ee v op t /\
      expr_val_rel cx (lowered_value_type ce e) v op t /\
      expr_val_at ce cx (lowered_value_type ce e) sa sb ee v op t /\
      type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
      type_memory_bytes ce (lowered_value_type ce e) < 2**64 /\
      ghost_inv_at (DF H) lo d ce cx ee G tn t /\
      ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (!x. op = Var x ==> not_fresh_at sb x) /\
      (~(~is_word_type (expr_type e) /\ exprs_can_mutate ce rest) ==>
        expr_store_bound cx (post_value_type ce e) v op t /\
        ptr_val_ok cx (post_value_type ce e) v op G tn t /\
        (~is_word_type (post_value_type ce e) ==> ptr_buf_ok ce e op G t) /\
        (~is_word_type (post_value_type ce e) ==> !w.
          eval_operand op t = SOME w ==>
          type_memory_size tv = 0 \/ w2n w + type_memory_size tv <= t.vs_alloca_next)) /\
      (~is_word_type (expr_type e) /\ exprs_can_mutate ce rest ==>
        ?x w. op = Var x /\ lookup_var x t = SOME w /\
          FLOOKUP t.vs_allocas mid.cs_next_id = SOME (w2n w,type_memory_size tv) /\
          FLOOKUP G x = SOME (w2n w,type_memory_size tv) /\
          ptr_buf_ok ce e op G t /\ lo <= w2n w /\
          ptr_covers G tn x t (type_memory_size tv) /\
          (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
            val_in_memory tv v (w2n w) mem) /\
          w2n w + type_memory_size tv < dimword(:256) /\
          w2n w + type_memory_size tv <= t.vs_alloca_next /\
          (!name b sz. local_region ce es.scopes s0 name b sz ==>
            b+sz <= w2n w \/ w2n w+type_memory_size tv <= b)))
    (\H rr ee gt r. expr_exit rr r /\ halt_exit H cx ee rr r)
Proof
  strip_tac >>
  `!fn inst s. frag_reachable ctx func s0 fn inst s ==>
    dalloca_no_wrap inst s` by
    (rpt strip_tac >> drule contextRawReachableTheory.frag_reachable_members >>
     disch_then drule >> strip_tac >>
     fs[ptrDisciplineTheory.ctx_has_dalloca_def, listTheory.EXISTS_MEM,
       unitMemInvTheory.dalloca_no_wrap_def] >> metis_tac[]) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp s0)` by simp[] >>
  Cases_on `~is_word_type (expr_type e) /\ exprs_can_mutate ce rest`
  >- suspend "capture" >>
  `unwrap_value ce vv mid = (op,sb) /\
   unwrap_value ce vv shadow_mid = (op,shadow_sb)` by metis_tac[] >>
  `lower_value compile_expr ce (expr_type e) e sa = (op,sb)` by
    simp[lower_value_def, comp_bind_def] >>
  `lower_value compile_expr ce (expr_type e) (gas_shadow_expr e) shadow_sa =
    (op,shadow_sb)` by simp[lower_value_def, comp_bind_def] >>
  `cs_extends sa mid /\ cs_extends shadow_sa shadow_mid` by
    metis_tac[exprSimUnwrapTheory.compile_expr_extends] >>
  `cs_extends mid sb /\ cs_extends shadow_mid shadow_sb` by
    metis_tac[exprSimUnwrapTheory.unwrap_value_extends] >>
  `fn_has_code sa mid func /\ fn_has_code mid sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `fn_has_code shadow_sa shadow_mid shadow_func` by metis_tac[fn_has_code_split] >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[forced_expr_admissible_raw] >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx (expr_type e) e es` by
    (qpat_x_assum `body_expr_full_ok _ _` mp_tac >>
     once_rewrite_tac[body_expr_full_ok_def] >> metis_tac[]) >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_vv_sim_full_def] >> disch_then drule_all >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
  irule gas_outcome_full_bind_all >> rpt conj_tac
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]
  >~ [`!v. storage_trace_frame (read_result cx v)`]
  >- simp[vyperStorageTraceTheory.storage_trace_frame_read_result]
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> drule gasExemptCertTheory.gas_exempt_cert_bind_result >> simp[] >>
      disch_then irule >> simp[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_result >>
      first_assum ACCEPT_TAC) >>
  qexists `\H res ee G tn t. childQ H res ee G tn t /\ ee.gas_obs = [] /\ ~t.vs_halted` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >> first_assum (irule_at Any) >>
      simp[Abbr `childR`, exprSimDefsTheory.halt_exit_def] >> rpt strip_tac >>
      qpat_x_assum `expr_exit res r` mp_tac >>
      Cases_on `res` >> simp[exprSimDefsTheory.expr_exit_def] >>
      Cases_on `r` >> Cases_on `y` >> simp[exprSimDefsTheory.expr_exit_def] >>
      gvs[] >> rename1 `Error err` >> Cases_on `err` >>
      simp[exprSimDefsTheory.expr_exit_def, exprSimDefsTheory.halt_exit_def]) >>
  suspend "uncaptured_read"
QED

Resume abi_encode_arg_step_full[capture]:
  `compile_materialize_vv ce (lowered_value_type ce e) vv mid = (op,sb) /\
   compile_materialize_vv ce (lowered_value_type ce e) vv shadow_mid = (op,shadow_sb)` by
    metis_tac[] >>
  `cs_extends sa mid /\ cs_extends shadow_sa shadow_mid` by
    metis_tac[exprSimUnwrapTheory.compile_expr_extends] >>
  `cs_extends mid sb /\ cs_extends shadow_mid shadow_sb` by
    metis_tac[materialize_extends] >>
  `fn_has_code sa mid func /\ fn_has_code mid sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `fn_has_code shadow_sa shadow_mid shadow_func` by
    metis_tac[fn_has_code_split] >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[forced_expr_admissible_raw] >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx (expr_type e) e es` by
    (qpat_x_assum `body_expr_full_ok _ _` mp_tac >>
     once_rewrite_tac[body_expr_full_ok_def] >> metis_tac[]) >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_vv_sim_full_def] >> disch_then drule_all >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
  irule gas_outcome_full_bind_all >> rpt conj_tac
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]
  >~ [`!v. storage_trace_frame (read_result cx v)`]
  >- simp[vyperStorageTraceTheory.storage_trace_frame_read_result]
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> drule gasExemptCertTheory.gas_exempt_cert_bind_result >> simp[] >>
      disch_then irule >> simp[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_result >>
      first_assum ACCEPT_TAC) >>
  qexists `\H res ee G tn t. childQ H res ee G tn t /\ ee.gas_obs = [] /\ ~t.vs_halted` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >> first_assum (irule_at Any) >>
      simp[Abbr `childR`, exprSimDefsTheory.halt_exit_def] >> rpt strip_tac >>
      qpat_x_assum `expr_exit res r` mp_tac >>
      Cases_on `res` >> simp[exprSimDefsTheory.expr_exit_def] >>
      Cases_on `r` >> Cases_on `y` >> simp[exprSimDefsTheory.expr_exit_def] >>
      gvs[] >> rename1 `Error err` >> Cases_on `err` >>
      simp[exprSimDefsTheory.expr_exit_def, exprSimDefsTheory.halt_exit_def]) >>
  suspend "capture_read"
QED

Resume abi_encode_arg_step_full[uncaptured_read]:
  qx_genl_tac [`marks`,`res`,`ee`,`G1`,`tn1`,`s`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qunabbrev_tac `childQ` >> disch_then (strip_assume_tac o BETA_RULE) >> gvs[] >>
  qpat_assum `!tail. eval_expr _ _ _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [listTheory.APPEND_NIL])) >>
  `ee with gas_obs := [] = ee` by
    simp[vyperStateTheory.evaluation_state_component_equality] >> gvs[] >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >> simp[]) >>
  `expr_body_pre ce cx env e (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  `?rty. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rty` by
    metis_tac[post_type_evaluates] >>
  `!rt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
    ~is_word_type (post_value_type ce e) ==>
    type_memory_bytes ce (post_value_type ce e) = type_memory_size rt /\
    type_memory_size rt < 2**64` by
    metis_tac[aggregateEvaluatedLayoutTheory.body_post_type_allocation_bound] >>
  `local_ptrs_reserved ce mid /\ sa.cs_next_var <= mid.cs_next_var /\
   sa.cs_next_id <= mid.cs_next_id` by
    (qpat_assum `compile_expr ce (expr_type e) e sa = _`
       (mp_tac o MATCH_MP exprSimUnwrapTheory.compile_expr_extends) >> strip_tac >>
     simp[] >> irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     goal_assum (drule_at Any) >> simp[]) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at mid x` by
    metis_tac[cj 1 exprOperandVarTheory.compiler_compile_var] >>
  `!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v` by
    (rpt strip_tac >>
     `value_runtime_typed env (post_value_type ce e) v` by
       (irule memory_rhs_read_post_typed >>
        qexistsl_tac [`cx`,`es with gas_obs := gas_explicit marks s0.vs_gas_readings`,`ee`] >>
        simp[vyperStateTheory.bind_def]) >>
     gvs[vyperTypeExprSoundnessTheory.value_runtime_typed_def,
       exprSimHypsDefsTheory.expr_body_pre_def,
       exprSimHypsDefsTheory.expr_sim_inv_def,
       vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def]) >>
  `is_word_type (post_value_type ce e) ==> is_word_type (expr_type e)` by
    metis_tac[exprSimIfExpWidenedPhysicalTypeTheory.post_value_type_nonword] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func ce cx e es sa mid s0 ee tv vv s /\
    ghost_inv_at (DF H) lo d ce cx ee G1 tn1 s` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  mp_tac (Q.INST [`sb` |-> `mid`, `sc` |-> `sb`, `G` |-> `G1`,
    `tn` |-> `tn1`, `Gi` |-> `G0`, `ti` |-> `tn0`,
    `sm` |-> `mid`, `cenv` |-> `ce`, `ty` |-> `expr_type e`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    (SPEC_ALL bodyFullUnwrapTheory.unwrap_value_origin_ptr)) >>
  (impl_tac >- (simp[] >> gvs[])) >> strip_tac >>
  suspend "uncaptured_unwrap"
QED
Resume abi_encode_arg_step_full[uncaptured_unwrap]:
  markerLib.RESUME_TAC >>
  irule gas_outcome_full_pure >> simp[] >>
  qexistsl_tac [`G'`,`ee`,`INL v`,`z`,`tn'`] >>
  conj_tac >- metis_tac[read_result_gas_obs] >>
  rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  simp[] >>
  `bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,ee)` by
    simp[vyperStateTheory.bind_def] >>
  `value_runtime_typed env (lowered_value_type ce e) v` by
    (irule memory_rhs_read_lowered_typed_unwidened >>
     goal_assum (drule_at Any) >> simp[SF ETA_ss] >> metis_tac[]) >>
  `env.type_defs = get_tenv cx` by
    (qpat_assum `expr_body_pre ce cx env e es` mp_tac >>
     simp[NoAsms, exprSimHypsDefsTheory.expr_body_pre_def,
       exprSimHypsDefsTheory.expr_sim_inv_def,
       vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >>
     rpt strip_tac >> first_assum ACCEPT_TAC) >>
  `?ltv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME ltv /\
    value_has_type ltv v` by
    gvs[vyperTypeExprSoundnessTheory.value_runtime_typed_def] >>
  `expr_sim_inv ce cx env es` by
    metis_tac[exprSimHypsDefsTheory.expr_body_pre_def] >>
  `type_memory_bytes ce (lowered_value_type ce e) = type_memory_size ltv` by
    metis_tac[expr_sim_inv_memory_size] >>
  `type_memory_bytes ce (lowered_value_type ce e) < 2**64` by
    (`type_memory_bytes ce (lowered_value_type ce e) <=
      type_memory_bytes ce (expr_type e)` by
       metis_tac[expr_body_pre_lowered_fits, abi_args_fits_memory_bytes] >>
     `type_memory_bytes ce (expr_type e) < 2**64` by
       (Cases_on `is_word_type (expr_type e)`
        >- simp[abi_builtin_encode_word_info] >>
        qpat_assum `expr_body_pre ce cx env e es` mp_tac >>
        simp[NoAsms, exprSimHypsDefsTheory.expr_body_pre_def] >> strip_tac >>
        drule alloc_limits_expr_type_alloc_ok >>
        simp[allocLimitsTheory.type_alloc_ok_def]) >> decide_tac) >>
  `expr_val_rel cx (lowered_value_type ce e) v op z /\
   expr_val_at ce cx (lowered_value_type ce e) sa sb ee v op z` by
    (conj_tac
     >- (irule abi_args_expr_post_lowered_rel >>
         conj_tac >- (simp[] >> metis_tac[valueEncodingTypingTheory.value_has_type_val_wf]) >>
         conj_tac >- (goal_assum (drule_at Any)) >> goal_assum (drule_at Any)) >>
     irule abi_args_expr_post_lowered_at >>
     conj_tac >- (simp[] >> metis_tac[valueEncodingTypingTheory.value_has_type_val_wf]) >>
     conj_tac >- (goal_assum (drule_at Any)) >> goal_assum (drule_at Any)) >>
  `!x. op = Var x ==> not_fresh_at sb x` by metis_tac[compile_lower_value_var] >>
  `~z.vs_halted` by
    (drule fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec >>
     simp[fragExecTheory.exit_result_def]) >>
  gvs[SF SFY_ss] >- simp[read_result_gas_obs] >> metis_tac[read_result_gas_obs]
QED
Resume abi_encode_arg_step_full[capture_read]:
  qx_genl_tac [`marks`,`res`,`ee`,`G1`,`tn1`,`s`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qunabbrev_tac `childQ` >> disch_then (strip_assume_tac o BETA_RULE) >> gvs[] >>
  qpat_assum `!tail. eval_expr _ _ _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [listTheory.APPEND_NIL])) >>
  `ee with gas_obs := [] = ee` by
    simp[vyperStateTheory.evaluation_state_component_equality] >> gvs[] >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >> simp[]) >>
  `?v. read_result cx tv ee = (INL v,ee)` by metis_tac[abi_args_vv_post_read] >>
  `expr_body_pre ce cx env e (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  `bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,ee)` by
    simp[vyperStateTheory.bind_def] >>
  `expr_sim_inv ce cx env ee /\
   ?ltv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME ltv /\
    value_has_type ltv v /\ val_wf ltv v /\
    type_memory_bytes ce (lowered_value_type ce e) = type_memory_size ltv /\
    type_memory_size ltv < 2**64 /\ type_memory_size ltv + 64 < dimword (:256)` by
    (drule_at (Pos last) (SRULE [SF ETA_ss] abi_args_success_ready) >>
     disch_then (qspecl_then [`env`,`ce`] mp_tac) >> simp[]) >>
  `?rty. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rty` by
    metis_tac[post_type_evaluates] >>
  `!rt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
    ~is_word_type (post_value_type ce e) ==>
    type_memory_bytes ce (post_value_type ce e) = type_memory_size rt /\
    type_memory_size rt < 2**64` by
    metis_tac[aggregateEvaluatedLayoutTheory.body_post_type_allocation_bound] >>
  `local_ptrs_reserved ce mid /\ sa.cs_next_var <= mid.cs_next_var /\
   sa.cs_next_id <= mid.cs_next_id` by
    (qpat_assum `compile_expr ce (expr_type e) e sa = _`
       (mp_tac o MATCH_MP exprSimUnwrapTheory.compile_expr_extends) >> strip_tac >>
     simp[] >> irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     goal_assum (drule_at Any) >> simp[]) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at mid x` by
    metis_tac[cj 1 exprOperandVarTheory.compiler_compile_var] >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by
    metis_tac[bodyPtrDefsTheory.ghost_inv_at_def] >>
  `!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_imm_base] >>
  `!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v` by
    (rpt strip_tac >>
     `value_runtime_typed env (post_value_type ce e) v` by
       metis_tac[memory_rhs_read_post_typed] >>
     gvs[vyperTypeExprSoundnessTheory.value_runtime_typed_def,
       exprSimHypsDefsTheory.expr_body_pre_def,
       exprSimHypsDefsTheory.expr_sim_inv_def,
       vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) es.storage_trace` by
    (drule_at (Pos (el 2)) vyperStorageFootprintTheory.valid_horizon_frame >>
     disch_then (qspecl_then [`st0`,`cx`,`storage_trace_horizon ee.storage_trace`] mp_tac) >>
     simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
       vyperStorageTraceTheory.storage_trace_frame_bind,
       vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx es s0` by
    metis_tac[] >>
  `ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?val. read_result cx tv ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
        eval_operand (vv_operand vv) s = SOME w ==>
        value_has_type rt val /\ w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn1.t_mem s.vs_memory mem ==>
          val_in_memory rt val (w2n w) mem)` by
    (strip_tac >> qpat_x_assum `ce.ce_is_ctor /\ _ ==> _`
       (drule_then strip_assume_tac) >>
     gvs[] >> qexists_tac `v` >> simp[] >> rpt strip_tac >> gvs[] >>
     first_x_assum drule >> simp[]) >>
  qpat_assum `ptr_vv_ok cx (post_value_type ce e) tv vv ee G1 tn1 s`
    (mp_then (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`) mp_tac
      abi_encode_capture_endpoint_origin) >>
  disch_then (drule_at (Pos hd)) >>
  disch_then (drule_at (Pos hd)) >>
  disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `storage_trace_domain _ _ _`)) >>
  disch_then (drule_at (Pat `read_result _ _ _ = _`)) >>
  disch_then (drule_at (Pat `expr_body_pre _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `val_wf _ _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ (post_value_type _ _) = _`)) >>
  disch_then (qspec_then `rty` mp_tac) >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`d`,`PG`,`DF`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  irule gas_outcome_full_pure >> simp[] >>
  qexistsl_tac [`Gt'`,`ee`,`INL v`,`t`,`tt`] >>
  conj_tac >- metis_tac[read_result_gas_obs] >>
  rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (drule_then assume_tac) >>
  gvs[] >>
  reverse conj_tac >- metis_tac[exprOperandVarTheory.compiler_materialize_vv_var] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  drule fragGasOriginPtrTheory.gas_origin_ptr_path_projections >> strip_tac >>
  drule fragGasOriginTheory.gas_origin_path_erase >> strip_tac >>
  drule fragGasModeTheory.gas_marked_path_exec >> strip_tac >>
  drule rest_word_path_frontier >> simp[]
QED
Finalise abi_encode_arg_step_full
