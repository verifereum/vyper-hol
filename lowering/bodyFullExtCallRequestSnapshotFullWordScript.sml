(* Immediate-read word snapshots on the joint judgment. *)
Theory bodyFullExtCallRequestSnapshotFullWord
Ancestors
  bodyFullExtCallRequestPositional bodyFullExtCallRequestSource
  bodyFullExtCallRequestSnapshotWord
  bodyFullPreds bodyFullOfVV gasOutcomeFullCompose bodySimFull
  exprSimMemDefs loweringPosts bodyPtrDefs gasShadowCompile compileEnv
  exprSimUnwrap exprSimMemorySource fragExec exprLowering exprSimDefs stmtSimProps
  exprLoweringProps exprOperandVar exprSimHyps exprSimSource

Theorem extcall_request_snapshot_word_full:
  body_expr_full_ok cx e /\ body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env e es /\ ~expr_has_effect e /\
  comp_bind (compile_expr cenv (expr_type e) e)
    (\vv. compile_snapshot_vv cenv F
      (ext_call_arg_value (lowered_value_type cenv e) vv)) sa = (sv,sb) /\
  comp_bind (compile_expr cenv (expr_type (gas_shadow_expr e)) (gas_shadow_expr e))
    (\vv. compile_snapshot_vv cenv F
      (ext_call_arg_value (lowered_value_type cenv (gas_shadow_expr e)) vv))
    shadow_sa = (sv,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!vv sm. compile_expr cenv (expr_type e) e sa = (vv,sm) ==>
    is_word_type (vv_type (ext_call_arg_value (lowered_value_type cenv e) vv))) ==>
  gas_outcome_full
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?v. res = INL v /\
      (?raw. read_result cx raw ee = (INL v,ee) /\
        vv_holds cenv cx (lowered_value_type cenv e) raw sv ee t /\
        ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G tn t /\
        vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee raw sv t) /\
      vv_storage_live H cx sv ee t /\
      (!tag op. sv = StackValue tag op /\ ~is_word_type (lowered_value_type cenv e) ==>
        ptr_buf_ok cenv e op G t) /\
      (!tag p. sv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
        ptr_buf_ok cenv e p.ptr_operand G t) /\
      (cenv.ce_is_ctor /\ vv_location sv = SOME LocCode ==>
        !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
          eval_operand (vv_operand sv) t = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
            val_in_memory rt v (w2n w) mem)) /\
      stmt_state_rel H ctx func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv sb t /\ ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      pure_frame cenv func es sa s0 t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      (ee with <|gas_obs := []; outcomes := NONE; storage_trace := []|>) =
      (es with <|gas_obs := []; outcomes := NONE; storage_trace := []|>))
    (\H res ee gt r. expr_exit res r)
Proof
  strip_tac >>
  Cases_on `compile_expr cenv (expr_type e) e sa` >>
  rename1 `compile_expr _ _ _ _ = (vv,sm)` >>
  `is_word_type (vv_type (ext_call_arg_value (lowered_value_type cenv e) vv))` by
    metis_tac[] >>
  gvs[comp_bind_def] >>
  Cases_on `compile_expr cenv (expr_type e) (gas_shadow_expr e) shadow_sa` >>
  rename1 `compile_expr _ _ (gas_shadow_expr _) _ = (shadow_vv,shadow_sm)` >>
  `shadow_vv = vv /\ gas_shadow_state sm shadow_sm` by
    (qspecl_then [`cenv`, `expr_type e`, `e`, `T`] mp_tac
       (cj 1 gas_shadow_compile_expr) >>
     simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >> simp[]) >>
  gvs[] >>
  `cs_extends sa sm /\ cs_extends shadow_sa shadow_sm` by
    metis_tac[compile_expr_extends] >>
  `cs_extends sm sb /\ cs_extends shadow_sm shadow_sb` by
    (gvs[compile_snapshot_vv_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
     metis_tac[unwrap_value_extends]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func /\
   fn_has_code shadow_sa shadow_sm shadow_func` by
    metis_tac[fn_has_code_split] >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by
    (qpat_x_assum `body_expr_full_ok cx e` mp_tac >>
     simp[Once body_expr_full_ok_def] >> metis_tac[]) >>
  drule forced_expr_admissible_raw >> strip_tac >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_vv_sim_full_def] >> disch_then drule_all >>
  strip_tac >> suspend "read"
QED

Resume extcall_request_snapshot_word_full[read]:
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
  irule gas_outcome_full_bind_all >>
  rpt conj_tac
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
  >- (irule gas_outcome_full_post_source >>
      first_assum (irule_at Any) >> simp[Abbr `childR`] >>
      rpt strip_tac >> Cases_on `res` >> gvs[expr_exit_def] >>
      metis_tac[expr_exit_INR_type]) >>
  suspend "normal"
QED

Resume extcall_request_snapshot_word_full[normal]:
  qx_genl_tac [`marks`,`res`,`ee`,`G1`,`tn1`,`t`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    gvs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. _ ==> childQ H _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  qunabbrev_tac `childQ` >> disch_then (strip_assume_tac o BETA_RULE) >> gvs[] >>
  qpat_assum `!tail. eval_expr _ _ _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  `ee with gas_obs := [] = ee` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  gvs[] >>
  `vv_holds cenv cx (post_value_type cenv e) tv shadow_vv ee t` by
    metis_tac[vv_post_def] >>
  drule_all extcall_request_word_snapshot_unwrap >> strip_tac >>
  gvs[comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` kall_tac >>
  `post_value_type cenv e = expr_type e` by
    (irule post_value_type_not_int_call >> rpt strip_tac >>
     Cases_on `e = Call ty (IntCall fid) args drv` >>
     gvs[expr_has_effect_thm]) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    (drule compile_expr_extends >> simp[]) >>
  `local_ptrs_reserved cenv sm` by
    (drule local_ptrs_reserved_next_var >> disch_then irule >> simp[]) >>
  `!x. vv_operand shadow_vv = Var x ==> not_fresh_at sm x` by
    metis_tac[cj 1 exprOperandVarTheory.compiler_compile_var] >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >> simp[]) >>
  suspend "unwrap"
QED

Resume extcall_request_snapshot_word_full[unwrap]:
  `expr_body_pre cenv cx env e
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  drule_all expr_body_pre_runtime_typed >> strip_tac >>
  drule_at (Pat `unwrap_value _ _ sm = _`) bodyFullUnwrapTheory.unwrap_value_origin_ptr >>
  disch_then (drule_at (Pat `compile_expr _ _ e sa = _`)) >>
  disch_then (drule_at (Pat `vv_store_bound _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `storage_trace_domain _ _ _`)) >>
  simp[] >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`d`,`ctx`,`PG`,`DF`] mp_tac) >>
  impl_tac >-
    (simp[] >> conj_tac
     >- (strip_tac >> drule_all expr_body_pre_copy_ok >> simp[]) >>
     qpat_x_assum `cenv.ce_is_ctor /\ _ ==> _` mp_tac >> simp[]) >>
  strip_tac >> suspend "package"
QED

Resume extcall_request_snapshot_word_full[package]:
  irule gas_outcome_full_pure >>
  reverse conj_tac >- simp[] >>
  qexistsl [`G'`,`ee`,`INL v`,`z`,`tn'`] >>
  simp[] >> conj_tac >- metis_tac[read_result_gas_obs] >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!H. _ ==> gas_origin_ptr_path _ _ _ _ /\ _` drule >>
  strip_tac >> simp[] >> suspend "post"
QED

Resume extcall_request_snapshot_word_full[post]:
  drule_all bodyIntCallJointPureSourceTheory.effect_free_eval_expr_frame >>
  strip_tac >>
  `arg_type_fits (lowered_value_type cenv e) (expr_type e)` by
    metis_tac[expr_body_pre_lowered_fits] >>
  `(is_word_type (lowered_value_type cenv e) <=> is_word_type (expr_type e))` by
    metis_tac[aggregateEvaluatedLayoutTheory.arg_type_fits_word_type] >>
  `~z.vs_halted` by
    metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_projections,
      fragGasSeqPtrTheory.gas_path_ptr_ok_not_halted] >>
  `sm.cs_next_var <= cs''.cs_next_var` by
    (mp_tac (Q.SPECL [`cenv`,`shadow_vv`,`sm`] ci_mono_unwrap_value) >>
     gvs[ci_mono_def]) >>
  `return_buf_frame d cenv cs'' z` by
    (match_mp_tac (Q.SPECL [`d`,`cenv`,`cenv`,`sa`,`cs''`,`s0`,`z`]
       bodyMemoryDefsTheory.return_buf_frame_frame) >>
     gvs[expr_post_def] >> decide_tac) >>
  suspend "representation"
QED

Resume extcall_request_snapshot_word_full[representation]:
  `expr_val_rel cx (lowered_value_type cenv e) v op z /\
   ptr_val_ok cx (lowered_value_type cenv e) v op G' tn' z` by
    (Cases_on `is_word_type (expr_type e)`
     >- (`lowered_value_type cenv e = expr_type e` by
           metis_tac[vyperTypeArgFitsTheory.arg_type_fits_prim_word,
             membership_element_word_boundary] >>
         gvs[expr_post_def]) >>
     `value_runtime_typed env (lowered_value_type cenv e) v` by
       (irule memory_rhs_read_lowered_typed_unwidened >>
        qexistsl_tac [`cx`,`es with gas_obs := gas_explicit marks s0.vs_gas_readings`,`ee`] >>
        simp[vyperStateTheory.bind_def]) >>
     `env.type_defs = get_tenv cx` by
       gvs[exprSimHypsDefsTheory.expr_body_pre_def,
           exprSimHypsDefsTheory.expr_sim_inv_def,
           vyperTypeInvariantsTheory.env_consistent_def,
           vyperTypeInvariantsTheory.env_context_consistent_def] >>
     `?dv. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME dv /\
           value_has_type dv v` by
       gvs[vyperTypeExprSoundnessTheory.value_runtime_typed_def] >>
     drule_all abiEncodeMaterializeTheory.materialize_post_lowered_classify >>
     strip_tac
     >- gvs[expr_post_def] >>
     conj_tac
     >- (gvs[expr_post_def, expr_val_rel_def] >>
         metis_tac[valueCopyBytesTheory.bytestring_val_in_memory_transfer]) >>
     gvs[ptr_val_ok_def] >>
     metis_tac[bodyPtrIfExpMemoryTransportTheory.ptr_mem_ok_bytestring_transport]) >>
  gvs[expr_post_def, contextTheory.vv_location_def] >>
  qexists_tac `tv` >> simp[vv_holds_def, ptr_vv_ok_def] >>
  gvs[vv_store_bound_def, expr_store_bound_def] >>
  metis_tac[]
QED

Finalise extcall_request_snapshot_word_full
