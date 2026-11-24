(* The immediate-read word branch of external-call positional snapshots. *)
Theory bodyFullExtCallPosWord
Ancestors
  bodyFullShadowBodyInv
  bodyFullPreds bodyFullUnwrap gasOutcomeFullCompose bodySimFull gasOutcomeFull
  exprSimMemDefs loweringPosts bodyPtrDefs gasShadowCompile compileEnv context
  exprSimMemorySource exprLowering exprSimDefs stmtSimProps exprLoweringProps
  exprOperandVar exprSimHyps exprSimSource contextRawReachable unitMemInv
  aggregateEvaluatedLayout valueCopyBytes targetPureSourceFrame exprSimWordArgs
  exprSafeOperand bodyMemoryDefs vyperState vyperStorageFootprint exprReasonOperand
  exprSimSend[qualified,ignore_grammar]
  list[qualified,ignore_grammar]
  ptrDiscipline[qualified,ignore_grammar]
  unitTransformDefs[qualified,ignore_grammar]

(* Retagging a word pointer changes no instruction emitted by unwrap_value. *)
Theorem word_snapshot_unwrap_copy:
  post_value_type ce e = expr_type e /\
  arg_type_fits (lowered_value_type ce e) (expr_type e) /\
  vv_holds ce cx (post_value_type ce e) raw vv ee t /\
  is_word_type (vv_type (ext_call_arg_value (lowered_value_type ce e) vv)) ==>
  compile_snapshot_vv ce copy (ext_call_arg_value (lowered_value_type ce e) vv) =
    comp_bind (unwrap_value ce vv) (\op. comp_return
      (StackValue (vv_type (ext_call_arg_value (lowered_value_type ce e) vv)) op))
Proof
  strip_tac >> Cases_on `vv`
  >- gvs[ext_call_arg_value_def, compile_snapshot_vv_def] >>
  `is_word_type (expr_type e)` by
    (gvs[ext_call_arg_value_def, vv_type_def] >> metis_tac[arg_type_fits_word_type]) >>
  `lowered_value_type ce e = expr_type e` by
    metis_tac[vyperTypeArgFitsTheory.arg_type_fits_prim_word, membership_element_word_boundary] >>
  gvs[vv_holds_def] >> imp_res_tac is_bytestring_word_type >>
  gvs[ext_call_arg_value_def, compile_snapshot_vv_def, vv_type_def]
QED

Theorem extcall_request_snapshot_word_owned_full:
  body_expr_full_ok cx e /\ body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env e es /\
  comp_bind (compile_expr cenv (expr_type e) e)
    (\vv. compile_snapshot_vv cenv F
      (ext_call_arg_value (lowered_value_type cenv e) vv)) sa = (sv,sb) /\
  comp_bind (compile_expr (gas_shadow_env T cenv) (expr_type (gas_shadow_expr e)) (gas_shadow_expr e))
    (\vv. compile_snapshot_vv cenv F
      (ext_call_arg_value (lowered_value_type cenv (gas_shadow_expr e)) vv))
    shadow_sa = (sv,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!fn inst z. frag_reachable ctx func s0 fn inst z ==> dalloca_fmp_headroom inst z) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
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
    (\H res ee G tn t. ?v tag op raw. res = INL v /\ sv = StackValue tag op /\
      read_result cx raw ee = (INL v,ee) /\
      vv_holds cenv cx (lowered_value_type cenv e) raw sv ee t /\
      vv_at cenv cx (lowered_value_type cenv e) sa sb ee raw sv t /\
      ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G tn t /\
      vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee raw sv t /\
      (~is_word_type (lowered_value_type cenv e) ==> ptr_buf_ok cenv e op G t) /\
      (is_word_type (expr_type e) ==> safe_operand sb op) /\
      stmt_state_rel H ctx func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv sb t /\ ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      wb_frame cenv es ee sa s0 t /\
      (~expr_has_effect e ==> pure_frame cenv func es sa s0 t) /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      (~expr_has_effect e ==>
        (ee with <|gas_obs := []; outcomes := NONE; requests := []; storage_trace := []|>) =
        (es with <|gas_obs := []; outcomes := NONE; requests := []; storage_trace := []|>)))
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  strip_tac >>
  irule gas_outcome_full_initial_domain >>
  simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
       cj 5 vyperStorageTraceTheory.evaluate_storage_trace_frame,
       vyperStorageTraceTheory.storage_trace_frame_read_result] >>
  strip_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s0` by
    (`valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
       fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H ctx func cenv cx es s0 /\ _`
       (qspec_then `storage_trace_horizon es.storage_trace` (drule_then strip_assume_tac)) >>
     qpat_assum `stmt_state_rel _ ctx func cenv cx es s0`
       (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  Cases_on `compile_expr cenv (expr_type e) e sa` >>
  rename1 `compile_expr _ _ _ _ = (vv,sm)` >>
  `is_word_type (vv_type (ext_call_arg_value (lowered_value_type cenv e) vv))` by
    metis_tac[] >>
  gvs[comp_bind_def] >>
  Cases_on `compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) shadow_sa` >>
  rename1 `compile_expr _ _ (gas_shadow_expr _) _ = (shadow_vv,shadow_sm)` >>
  `shadow_vv = vv /\ gas_shadow_state sm shadow_sm` by
    (`gas_shadow_compiles (compile_expr cenv (expr_type e) e)
       (compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e))` by
       irule (cj 1 gas_shadow_compile_expr_env |> SPEC_ALL |>
              Q.INST [`shadow` |-> `T`] |> REWRITE_RULE [COND_CLAUSES]) >>
     qpat_x_assum `gas_shadow_compiles _ _`
       (qspecl_then [`sa`, `shadow_sa`] mp_tac o
        REWRITE_RULE [gasShadowStateTheory.gas_shadow_compiles_def]) >> simp[]) >>
  gvs[] >>
  `cs_extends sa sm /\ cs_extends shadow_sa shadow_sm` by
    metis_tac[exprSimUnwrapTheory.compile_expr_extends] >>
  `cs_extends sm sb /\ cs_extends shadow_sm shadow_sb` by
    (gvs[compile_snapshot_vv_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
     metis_tac[exprSimUnwrapTheory.unwrap_value_extends]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func /\
   fn_has_code shadow_sa shadow_sm shadow_func` by metis_tac[fragExecTheory.fn_has_code_split] >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by
    (qpat_x_assum `body_expr_full_ok cx e` mp_tac >>
     simp[Once body_expr_full_ok_def] >> metis_tac[]) >>
  drule forced_expr_admissible_raw >> strip_tac >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_vv_sim_full_def] >> disch_then drule_all >>
  strip_tac >> suspend "read"
QED

Resume extcall_request_snapshot_word_owned_full[read]:
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
  irule gas_outcome_full_bind_all >>
  rpt conj_tac
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[cj 5 vyperStorageTraceTheory.evaluate_storage_trace_frame]
  >~ [`!v. storage_trace_frame (read_result cx v)`]
  >- simp[vyperStorageTraceTheory.storage_trace_frame_read_result]
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> drule gasExemptCertTheory.gas_exempt_cert_bind_result >> simp[] >>
      disch_then irule >> simp[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_result >>
      first_assum ACCEPT_TAC) >>
  qexists `\H res ee G tn t. childQ H res ee G tn t /\ ee.gas_obs = [] /\ ~t.vs_halted` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >>
      first_assum (irule_at Any) >> simp[Abbr `childR`] >>
      rpt strip_tac >> Cases_on `res` >>
      gvs[expr_exit_def, halt_exit_def, expr_exit_INR_type]) >>
  suspend "normal"
QED

Resume extcall_request_snapshot_word_owned_full[normal]:
  qx_genl_tac [`marks`,`res`,`ee`,`G1`,`tn1`,`t`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    gvs[storage_trace_domain_def] >>
  qpat_assum `!H. _ ==> childQ H _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  qunabbrev_tac `childQ` >> disch_then (strip_assume_tac o BETA_RULE) >> gvs[] >>
  qpat_assum `!tail. eval_expr _ _ _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  `ee with gas_obs := [] = ee` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  gvs[] >>
  `arg_type_fits (lowered_value_type cenv e) (expr_type e)` by
    metis_tac[expr_body_pre_lowered_fits] >>
  `reason_uniform_shape compile_expr cenv (expr_type e) e` by
    (irule compile_expr_reason_uniform >> qexists_tac `env` >>
     fs[exprSimHypsDefsTheory.expr_body_pre_def, exprSimHypsDefsTheory.expr_sim_inv_def]) >>
  `is_word_type (expr_type e)` by
    (qpat_assum `reason_uniform_shape _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [reason_uniform_shape_def]) >>
     qpat_x_assum `!sa vv sb. _ ==> reason_result_shape _ _ _`
       (drule_then assume_tac) >>
     qpat_assum `arg_type_fits (lowered_value_type cenv e) (expr_type e)`
       (mp_tac o MATCH_MP arg_type_fits_word_type) >>
     qpat_assum `reason_result_shape t' loc shadow_vv` mp_tac >>
     FIRST [qpat_assum `t' = expr_type e` mp_tac,
            qpat_assum `t' = lowered_value_type cenv e` mp_tac] >>
     qpat_assum `is_word_type (vv_type (ext_call_arg_value _ shadow_vv))` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `shadow_vv` >>
     simp[reason_result_shape_def, ext_call_arg_value_def, vv_type_def] >>
     metis_tac[]) >>
  `post_value_type cenv e = expr_type e` by
    (Cases_on `?ty fid args drv. e = Call ty (IntCall fid) args drv` >>
     gvs[post_value_type_def, vyperASTTheory.expr_type_def] >>
     irule post_value_type_not_int_call >> metis_tac[]) >>
  `vv_holds cenv cx (post_value_type cenv e) tv shadow_vv ee t` by
    metis_tac[vv_post_def] >>
  drule_all (Q.INST [`copy` |-> `F`] word_snapshot_unwrap_copy) >> strip_tac >>
  gvs[comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` kall_tac >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    (drule exprSimUnwrapTheory.compile_expr_extends >> simp[]) >>
  `local_ptrs_reserved cenv sm` by
    (drule local_ptrs_reserved_next_var >> disch_then irule >> simp[]) >>
  `!x. vv_operand shadow_vv = Var x ==> not_fresh_at sm x` by
    metis_tac[cj 1 compiler_compile_var] >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >> simp[]) >>
  suspend "unwrap"
QED

Resume extcall_request_snapshot_word_owned_full[unwrap]:
  `expr_body_pre cenv cx env e
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  drule_all expr_body_pre_runtime_typed >> strip_tac >>
  qpat_assum `is_word_type (expr_type e)`
    (fn th => drule_at (Pat `unwrap_value _ _ sm = _`)
      (SIMP_RULE (srw_ss()) [th]
        (Q.INST [`e` |-> `e`, `cenv` |-> `cenv`] unwrap_value_origin_ptr))) >>
  disch_then (drule_at (Pat `compile_expr _ _ e sa = _`)) >>
  disch_then (drule_at (Pat `vv_store_bound _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `storage_trace_domain _ _ _`)) >>
  simp[] >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`d`,`ctx`,`PG`,`DF`] mp_tac) >>
  impl_tac >-
    (simp[] >> qpat_x_assum `cenv.ce_is_ctor /\ _ ==> _` mp_tac >> simp[]) >>
  strip_tac >> suspend "package"
QED

Resume extcall_request_snapshot_word_owned_full[package]:
  irule gas_outcome_full_pure >>
  reverse conj_tac >- simp[] >>
  qexistsl [`G'`,`ee`,`INL v`,`z`,`tn'`] >>
  simp[] >> conj_tac >- metis_tac[read_result_gas_obs] >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!H. _ ==> gas_origin_ptr_path _ _ _ _ /\ _` drule >>
  strip_tac >> simp[] >> suspend "post"
QED

Resume extcall_request_snapshot_word_owned_full[post]:
  `~expr_has_effect e ==>
    (ee with <|gas_obs := []; outcomes := NONE; requests := []; storage_trace := []|>) =
    (es with <|gas_obs := []; outcomes := NONE; requests := []; storage_trace := []|>)` by
    (strip_tac >> drule_all effect_free_source_projection >> simp[]) >>
  `(is_word_type (lowered_value_type cenv e) <=> is_word_type (expr_type e))` by
    metis_tac[arg_type_fits_word_type] >>
  `~z.vs_halted` by
    metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_projections,
      fragGasSeqPtrTheory.gas_path_ptr_ok_not_halted] >>
  `sm.cs_next_var <= cs''.cs_next_var` by
    (mp_tac (Q.SPECL [`cenv`,`shadow_vv`,`sm`] ci_mono_unwrap_value) >>
     gvs[ci_mono_def]) >>
  `return_buf_frame d cenv cs'' z` by
    (irule return_buf_frame_frame >> qexistsl [`cenv`,`s0`,`sa`] >>
     gvs[expr_post_def]) >>
  suspend "representation"
QED

Resume extcall_request_snapshot_word_owned_full[representation]:
  `post_value_type cenv e = expr_type e` by simp[] >>
  `(is_word_type (expr_type e) ==> safe_operand cs'' op)` by
    (strip_tac >> irule unwrap_value_safe_operand >>
     first_assum (irule_at Any) >>
     `well_typed_expr env e` by
       fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
     `!id t. FLOOKUP env.var_types id = SOME t ==>
             well_formed_type env.type_defs t` by
       metis_tac[expr_body_pre_var_types_well_formed] >>
     drule_all (cj 1 exprWordOperandTheory.compile_expr_word_result) >> simp[]) >>
  `lowered_value_type cenv e = expr_type e` by
    metis_tac[vyperTypeArgFitsTheory.arg_type_fits_prim_word,
              membership_element_word_boundary] >>
  qpat_assum `post_value_type cenv e = expr_type e`
    (fn ty => qhdtm_assum `expr_post`
      (fn th => assume_tac (MATCH_MP expr_post_frame th) >>
        strip_assume_tac (REWRITE_RULE [expr_post_def, ty] th))) >>
  qexists_tac `Value v` >>
  fs[vv_holds_def, vv_at_def, ptr_vv_ok_def, read_result_def, return_def,
     vv_store_bound_def]
QED

Finalise extcall_request_snapshot_word_owned_full
