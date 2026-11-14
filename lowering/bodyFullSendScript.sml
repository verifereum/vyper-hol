(*
 * send over the finite-horizon joint judgment: the word arguments, the
 * CALL and the success ASSERT share one origin/memory/pointer witness.
 *
 * TOP-LEVEL:
 *   send_expr_sim_full    -- the value judgment of a send call
 *   send_expr_vv_sim_full -- its vv judgment
 *   body_send_case_full  -- the body induction case
 *)
Theory bodyFullSend
Ancestors
  bodyFullSendPost bodyFullExprGeneric bodyFullShared bodyFullPreds bodySimFull
  gasOutcomeFullCompose gasOutcomeFull fragGasSeqPtr fragGasEmitCtrl
  gasShadowCompile gasShadowState gasShadow
  exprSendPtr exprSimSend exprSimHypsDefs bodySim
  exprLowering vyperAST vyperInterpreter list

val _ = Parse.hide "body";

Theorem send_expr_sim_full:
  !DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx env ty ann
   has_gas args dflt es.
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Call ann (Send has_gas) args dflt) es /\
    body_exprs_full_ok cx args ==>
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Call ann (Send has_gas) args dflt) es
Proof
  rpt gen_tac >> strip_tac >> drule send_pre_types >> strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  rewrite_tac[expr_sim_full_def] >> rpt gen_tac >> strip_tac >>
  drule lower_value_send >> strip_tac >> gvs[] >>
  drule_all compile_expr_send >> strip_tac >>
  qpat_assum `lower_value _ _ _ (gas_shadow_expr _) _ = _`
    (mp_tac o REWRITE_RULE [gas_shadow_expr_def]) >>
  disch_then (strip_assume_tac o MATCH_MP lower_value_send) >>
  `MAP expr_type (MAP gas_shadow_expr args) = MAP expr_type args` by
    simp[MAP_MAP_o, combinTheory.o_DEF, gas_shadow_expr_type, ETA_AX] >>
  qpat_assum `compile_expr _ _ (Call _ _ (MAP _ _) _) shadow_sa = _`
    (mp_then Any mp_tac compile_expr_send) >>
  simp[] >> strip_tac >>
  `bind (eval_expr cx (Call NoneT (Send has_gas) args dflt)) (read_result cx) =
   bind (eval_exprs cx args) (\vs. bind (eval_send cx has_gas vs) (read_result cx))` by
    (pure_rewrite_tac[FUN_EQ_THM] >> gen_tac >>
     Cases_on `bind (eval_expr cx (Call NoneT (Send has_gas) args dflt))
       (read_result cx) x` >>
     drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) eval_expr_send_cases) >>
     strip_tac >> gvs[vyperStateTheory.bind_def]) >>
  suspend "operands"
QED

Resume send_expr_sim_full[operands]:
  Cases_on `has_gas` >> gvs[LENGTH_EQ_NUM_compute,
    exprSimWordArgsTheory.lower_word_args_cons,
    exprSimWordArgsTheory.lower_word_args_nil] >>
  suspend "arity"
QED

Resume send_expr_sim_full[arity]:
  markerLib.RESUME_TAC >> (rpt strip_tac >>
  rename1 `expr_type to_e = BaseT AddressT` >>
  `expr_body_pre cenv cx env to_e es` by
    (irule expr_body_pre_send_arg >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >> simp[]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type to_e) to_e es` by
    (gvs[body_exprs_full_ok_def, EVERY_DEF] >>
     qpat_x_assum `body_expr_full_ok cx to_e` mp_tac >>
     simp[Once body_expr_full_ok_def] >> metis_tac[]) >>
  `gas_shadow_compiles (lower_value compile_expr cenv (expr_type to_e) to_e)
     (lower_value compile_expr cenv (expr_type to_e) (gas_shadow_expr to_e))` by
    (irule (SRULE [] (Q.INST [`sh` |-> `T`]
       gasShadowCompileHelpersTheory.gas_shadow_compiles_lower_value)) >>
     simp[gas_shadow_compile_expr]) >>
  rename1 `lower_value compile_expr cenv (BaseT AddressT) to_e sa = (addr_op,s1)` >>
  `?shadow_s1. lower_value compile_expr cenv (expr_type to_e)
      (gas_shadow_expr to_e) shadow_sa = (addr_op,shadow_s1) /\
      gas_shadow_state s1 shadow_s1` by
    (qpat_x_assum `gas_shadow_compiles _ _`
       (mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
     disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >> simp[] >>
     Cases_on `lower_value compile_expr cenv (BaseT AddressT)
       (gas_shadow_expr to_e) shadow_sa` >> gvs[]) >>
  gvs[] >>
  `!ce ct e a op b. lower_value compile_expr ce ct e a = (op,b) ==>
     cs_extends a b` by
    metis_tac[exprLoweringPropsTheory.ci_mono_lower_value_compile_expr,
      exprLoweringPropsTheory.ci_mono_def, pairTheory.SND] >>
  imp_res_tac send_tail_shape >>
  qpat_assum `!ce ct e a op b. _` (fn th => imp_res_tac th) >>
  gvs[] >>
  rename1 `gas_shadow_state s1 shadow_s1` >>
  `fn_has_code sa s1 func /\ fn_has_code shadow_sa shadow_s1 shadow_func` by
    metis_tac[fragExecTheory.fn_has_code_split, compileEnvTheory.cs_extends_trans] >>
  `gas_admissible (bind (eval_expr cx to_e) (read_result cx)) expr_res_ok es` by
    metis_tac[exprSimSourceTheory.expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim_full _ _ _ _ to_e _` mp_tac >>
  rewrite_tac[expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`, `sa`, `s1`, `shadow_sa`, `shadow_s1`,
    `addr_op`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
  asm_rewrite_tac[] >>
  once_rewrite_tac[exprSimWordArgsTheory.eval_exprs_cons_action] >>
  once_rewrite_tac[vyperStateTheory.bind_assoc] >>
  irule gas_outcome_full_bind_all >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >>
      irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
      qexistsl [`mid`, `t`, `v`] >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >>
      irule gasExemptCertTheory.gas_exempt_cert_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
      simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
           vyperStorageTraceTheory.storage_trace_frame_read_result])
  >- (gen_tac >> BETA_TAC >>
      irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
      conj_tac
      >- (gen_tac >> BETA_TAC >>
          irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
          simp[vyperStorageTraceTheory.storage_trace_frame_send,
               vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
      irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
      simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
           vyperStorageTraceTheory.storage_trace_frame_return]) >>
  qexists `\H res ee G tn t. childQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac >~ [`storage_trace_domain _ _ _`] >- suspend "after_address" >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  conj_tac >- simp[] >>
  simp[Abbr `childR`] >> rpt strip_tac >>
  Cases_on `res` >> fs[exprSimDefsTheory.expr_exit_def])
QED

Resume send_expr_sim_full[after_address]:
  markerLib.RESUME_TAC >> (rpt gen_tac >> strip_tac >>
    `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
       mid.storage_trace` by
      fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
    `?v. res = INL v` by
      (qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
         (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
       simp[Abbr `childQ`] >> metis_tac[]) >>
    gvs[] >>
    `expr_sim_inv cenv cx env mid` by
      (qpat_assum `!tail. _ = _` (qspec_then `[]` mp_tac) >>
       strip_tac >>
       `expr_body_pre cenv cx env to_e
          (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ [])` by simp[] >>
       drule_all (CONV_RULE (DEPTH_CONV ETA_CONV)
         exprSimSourceTheory.expr_body_pre_eval) >>
       qpat_assum `!H. valid_horizon _ _ H _ ==> _`
         (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
    rename1 `lower_value compile_expr cenv (BaseT (UintT 256)) amount_e s1 =
      (amount_op,amount_end)` >>
    `expr_body_pre cenv cx env amount_e mid` by
      (irule expr_body_pre_send_arg >>
       qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >> simp[]) >>
    `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
       cenv cx (expr_type amount_e) amount_e mid` by
      (`?ss raw tt uu. eval_expr cx to_e ss = (INL raw,tt) /\
           read_result cx raw tt = (INL v,uu)` by
         (qexists `es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ []` >>
          qpat_assum `!tail. _ = _` (qspec_then `[]` mp_tac) >>
          simp[NoAsms, vyperStateTheory.bind_def, AllCaseEqs()] >>
          strip_tac >> goal_assum (drule_at Any) >> simp[]) >>
       gvs[body_exprs_full_ok_def, EVERY_DEF] >>
       `body_expr_full_ok cx amount_e` by
         metis_tac[] >>
       qpat_x_assum `body_expr_full_ok cx amount_e` mp_tac >>
       simp[Once body_expr_full_ok_def] >> metis_tac[]) >>
    `gas_shadow_compiles (lower_value compile_expr cenv (expr_type amount_e) amount_e)
       (lower_value compile_expr cenv (expr_type amount_e) (gas_shadow_expr amount_e))` by
      (irule (SRULE [] (Q.INST [`sh` |-> `T`]
         gasShadowCompileHelpersTheory.gas_shadow_compiles_lower_value)) >>
       simp[gas_shadow_compile_expr]) >>
    qpat_x_assum `gas_shadow_compiles _ _`
      (mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
    disch_then (qspecl_then [`s1`, `shadow_s1`] mp_tac) >> simp[] >> strip_tac >>
    gvs[] >>
    rename1 `lower_value compile_expr cenv (BaseT (UintT 256)) amount_e s1 =
       (amount_op,amount_end)` >>
    rename1 `lower_value compile_expr cenv (BaseT (UintT 256))
       (gas_shadow_expr amount_e) shadow_s1 = (amount_op,shadow_amount_end)` >>
    `fn_has_code s1 amount_end func /\
     fn_has_code shadow_s1 shadow_amount_end shadow_func` by
      metis_tac[fragExecTheory.fn_has_code_split, compileEnvTheory.cs_extends_trans] >>
    qpat_x_assum `expr_sim_full _ _ _ _ amount_e _` mp_tac >>
    rewrite_tac[expr_sim_full_def] >>
    disch_then (qspecl_then [`st0`, `s1`, `amount_end`, `shadow_s1`,
      `shadow_amount_end`, `amount_op`, `t`, `G1`, `tn1`] mp_tac) >>
    (impl_tac >-
      (qpat_assum `!H. valid_horizon _ _ H _ ==> _`
         (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
       simp[NoAsms, Abbr `childQ`] >> strip_tac >>
       qpat_x_assum `valid_horizon _ _ _ _ ==> _`
         (drule_then strip_assume_tac) >>
       simp[exprSimSourceTheory.expr_body_pre_gas_admissible] >>
       `sa.cs_next_var <= s1.cs_next_var` by
         metis_tac[exprSimSourceTheory.expr_body_pre_lower_value_word_shape] >>
       conj_tac >- metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
       conj_tac >- metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
       conj_tac >- metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
       conj_tac >- metis_tac[exprSimSourceTheory.expr_body_pre_gas_admissible] >>
       conj_tac >-
         (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
          qpat_assum `return_buf_frame d cenv sa s0` (irule_at Any) >>
          fs[loweringPostsTheory.expr_post_def]) >>
       rpt strip_tac >>
       qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ ~t.vs_halted /\ _`
         (qspec_then `H` mp_tac) >>
       metis_tac[loweringPostsTheory.expr_post_def])) >>
    strip_tac >>
    qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ amountQ amountR` >>
    once_rewrite_tac[vyperStateTheory.bind_assoc] >>
    simp[Once exprSimWordArgsTheory.eval_exprs_cons_action] >>
    once_rewrite_tac[vyperStateTheory.bind_assoc] >>
    irule gas_outcome_full_bind_all >>
    rpt conj_tac
    >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
    >- (rpt strip_tac >>
        irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
        qexistsl [`mid'`, `t'`, `v'`] >> fs[])
    >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
    >- (rpt strip_tac >>
        irule gasExemptCertTheory.gas_exempt_cert_error_value >> simp[])
    >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
    >- (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
        simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
             vyperStorageTraceTheory.storage_trace_frame_read_result])
    >- (gen_tac >> BETA_TAC >>
        irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
        conj_tac
        >- (gen_tac >> BETA_TAC >>
            irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
            conj_tac >-
              (gen_tac >> BETA_TAC >>
               irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
               simp[vyperStorageTraceTheory.storage_trace_frame_send,
                    vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
            simp[vyperStorageTraceTheory.storage_trace_frame_return]) >>
        irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
        simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
             vyperStorageTraceTheory.storage_trace_frame_return]) >>
    qexists `\H res ee G tn t. amountQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
    conj_tac >~ [`storage_trace_domain _ _ _`] >- suspend "after_amount" >>
    irule gas_outcome_full_post_source >>
    qpat_assum `gas_outcome_full _ _ _ _ _ _ amountQ amountR` (irule_at Any) >>
    conj_tac >- simp[] >>
    simp[Abbr `amountR`, Abbr `childR`] >> rpt strip_tac >>
    Cases_on `res` >> fs[exprSimDefsTheory.expr_exit_def])
QED

Resume send_expr_sim_full[after_amount]:
  markerLib.RESUME_TAC >> (rpt gen_tac >> strip_tac >>
    `valid_horizon cx st0 (storage_trace_horizon mid'.storage_trace)
       mid'.storage_trace` by
      fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
    `?value. res = INL value` by
      (qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
         (qspec_then `storage_trace_horizon mid'.storage_trace` mp_tac) >>
       simp[Abbr `amountQ`] >> metis_tac[]) >>
    gvs[] >>
    qpat_assum `!H. valid_horizon _ _ H mid'.storage_trace ==> _`
      (qspec_then `storage_trace_horizon mid'.storage_trace` mp_tac) >>
    simp[NoAsms, Abbr `amountQ`] >> strip_tac >>
    qpat_x_assum `valid_horizon _ _ _ _ ==> _`
      (drule_then strip_assume_tac) >>
    `!l. addr_op <> Label l` by
      metis_tac[exprSimSourceTheory.expr_body_pre_lower_value_word_shape] >>
    `!z. addr_op = Var z ==> not_fresh_at s1 z` by
      metis_tac[exprSimSourceTheory.expr_body_pre_lower_value_word_shape] >>
    qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
      (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
    simp[NoAsms, Abbr `childQ`] >> strip_tac >>
    qpat_x_assum `valid_horizon _ _ _ _ ==> _`
      (drule_then strip_assume_tac) >>
    `!w. eval_operand addr_op t = SOME w ==> eval_operand addr_op t' = SOME w` by
      (Cases_on `addr_op` >>
       fs[venomStateTheory.eval_operand_def,
          loweringPostsTheory.expr_post_def] >>
       metis_tac[]) >>
    `op_taint tn1' addr_op = op_taint tn1 addr_op` by
      (irule emittedSeqComposePtrTheory.old_operand_taint_frame >>
       metis_tac[bodyPtrDefsTheory.ghost_kept_at_def]) >>
    `storage_trace_frame (bind (eval_expr cx to_e) (read_result cx))` by
      (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
       simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
            vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
    `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) es.storage_trace` by
      (qpat_assum `!tail. bind (eval_expr cx to_e) _ _ = _`
         (qspec_then `[]` assume_tac) >>
       drule_all vyperStorageTraceTheory.storage_trace_frame_prefix >>
       simp[] >> strip_tac >>
       fs[vyperStorageFootprintTheory.valid_horizon_def]) >>
    `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx es s0` by
      (qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
         (qspec_then `storage_trace_horizon mid.storage_trace`
           (drule_then strip_assume_tac)) >> simp[]) >>
    `sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id` by
      metis_tac[exprSimSourceTheory.expr_body_pre_lower_value_word_shape] >>
    `wb_frame cenv es mid sa s0 t /\ wb_frame cenv mid mid' s1 t t'` by
      (conj_tac
       >- qpat_assum `expr_post _ _ _ _ _ to_e _ _ _ _ _ _ _ _`
         (ACCEPT_TAC o MATCH_MP (SPEC_ALL exprSimWordArgsTheory.expr_post_frame)) >>
       qpat_assum `expr_post _ _ _ _ _ amount_e _ _ _ _ _ _ _ _`
         (ACCEPT_TAC o MATCH_MP (SPEC_ALL exprSimWordArgsTheory.expr_post_frame))) >>
    `MAP finite_map$FDOM es.scopes = MAP finite_map$FDOM mid.scopes` by
      fs[loweringPostsTheory.wb_frame_def,loweringPostsTheory.locals_kept_def] >>
    `wb_frame cenv es mid' sa s0 t'` by
      (drule_all exprSimWordArgsTheory.wb_frame_trans >> simp[]) >>
    `ghost_kept_at lo cenv es sa G0 tn0 s0 G1' tn1'` by
      (qspecl_then [`lo`,`cenv`,`es`,`sa`,`G0`,`tn0`,`s0`,`G1`,`tn1`,`mid`,
         `s1`,`G1'`,`tn1'`,`t`,`storage_trace_horizon mid.storage_trace`,
         `ctx`,`func`,`cx`,`mid`] mp_tac wordArgsPtrTheory.ghost_kept_at_wb_trans >>
       simp[]) >>
    `expr_result_typed env to_e (Value v)` by
      (qpat_assum `!tail. bind (eval_expr cx to_e) _ _ = _`
         (qspec_then `[]` mp_tac) >> strip_tac >>
       `expr_body_pre cenv cx env to_e
          (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ [])` by simp[] >>
       drule_all (CONV_RULE (DEPTH_CONV ETA_CONV)
         exprSimSourceTheory.expr_body_pre_eval) >> simp[]) >>
    `expr_result_typed env amount_e (Value value)` by
      (qpat_assum `!tail. bind (eval_expr cx amount_e) _ _ = _`
         (qspec_then `[]` mp_tac) >> strip_tac >>
       `expr_body_pre cenv cx env amount_e
          (mid with gas_obs := gas_explicit marks' t.vs_gas_readings ++ [])` by simp[] >>
       drule_all (CONV_RULE (DEPTH_CONV ETA_CONV)
         exprSimSourceTheory.expr_body_pre_eval) >> simp[]) >>
    `expr_sim_inv cenv cx env mid'` by
      (qpat_assum `!tail. bind (eval_expr cx amount_e) _ _ = _`
         (qspec_then `[]` mp_tac) >> strip_tac >>
       `expr_body_pre cenv cx env amount_e
          (mid with gas_obs := gas_explicit marks' t.vs_gas_readings ++ [])` by simp[] >>
       drule_all (CONV_RULE (DEPTH_CONV ETA_CONV)
         exprSimSourceTheory.expr_body_pre_eval) >> simp[]) >>
    `value_has_type (BaseTV AddressT) v /\
     value_has_type (BaseTV (UintT 256)) value` by
      (fs[vyperTypeExprResultTheory.expr_result_typed_def,
         vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
         vyperTypeInvariantsTheory.value_result_typed_def] >>
       gvs[vyperValueTheory.evaluate_type_def]) >>
    `eval_operand addr_op t' = SOME (typed_val_to_w256 (BaseTV AddressT) v)` by
      (qpat_assum `!w. eval_operand addr_op t = SOME w ==>
          eval_operand addr_op t' = SOME w` irule >>
       qpat_assum `expr_post _ _ _ _ _ to_e _ _ _ _ _ _ _ _`
         (mp_tac o Q.INST [`tv` |-> `BaseTV AddressT`] o
          MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
           exprSimPrecompilesTheory.expr_post_typed_stack_operand)) >>
       simp[vyperValueTheory.evaluate_type_def]) >>
    `eval_operand amount_op t' =
       SOME (typed_val_to_w256 (BaseTV (UintT 256)) value)` by
      (qpat_assum `expr_post _ _ _ _ _ amount_e _ _ _ _ _ _ _ _`
         (mp_tac o Q.INST [`tv` |-> `BaseTV (UintT 256)`] o
          MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
           exprSimPrecompilesTheory.expr_post_typed_stack_operand)) >>
       simp[vyperValueTheory.evaluate_type_def]) >>
    suspend "ready_amount")
QED

Resume send_expr_sim_full[ready_amount]:
  markerLib.RESUME_TAC >>
  (`eval_exprs cx [] = return []` by
     simp[FUN_EQ_THM,exprSimWordArgsTheory.eval_exprs_nil,
          vyperStateTheory.return_def] >>
   simp[vyperStateTheory.bind_return] >>
   suspend "tail_no_gas")
QED

Resume send_expr_sim_full[tail_no_gas]:
  markerLib.RESUME_TAC >>
  (FIRST [
    (qmatch_goalsub_abbrev_tac `eval_exprs cx [gas_e]` >>
     suspend "gas_child"),
    suspend "call_tail"])
QED

Resume send_expr_sim_full[gas_child]:
  markerLib.RESUME_TAC >>
  `expr_body_pre cenv cx env gas_e mid'` by
    (irule expr_body_pre_send_arg >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >> simp[]) >>
  `gas_admissible (bind (eval_expr cx gas_e) (read_result cx)) expr_res_ok mid'` by
    qpat_assum `expr_body_pre cenv cx env gas_e mid'`
      (ACCEPT_TAC o MATCH_MP exprSimSourceTheory.expr_body_pre_gas_admissible) >>
  `body_expr_full_ok cx gas_e` by
    (`?ss raw tt uu. eval_expr cx to_e ss = (INL raw,tt) /\
       read_result cx raw tt = (INL v,uu)` by
       (qexists `es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ []` >>
        qpat_assum `!tail. bind (eval_expr cx to_e) _ _ = _`
          (qspec_then `[]` mp_tac) >>
        simp[NoAsms,vyperStateTheory.bind_def,AllCaseEqs()] >>
        strip_tac >> goal_assum (drule_at Any) >> simp[]) >>
     `?ss raw tt uu. eval_expr cx amount_e ss = (INL raw,tt) /\
       read_result cx raw tt = (INL value,uu)` by
       (qexists `mid with gas_obs := gas_explicit marks' t.vs_gas_readings ++ []` >>
        qpat_assum `!tail. bind (eval_expr cx amount_e) _ _ = _`
          (qspec_then `[]` mp_tac) >>
        simp[NoAsms,vyperStateTheory.bind_def,AllCaseEqs()] >>
        strip_tac >> goal_assum (drule_at Any) >> simp[]) >>
     qpat_assum `body_exprs_full_ok cx [to_e;amount_e;gas_e]` mp_tac >>
     qpat_assum `eval_expr cx to_e _ = (INL _,_)` mp_tac >>
     qpat_assum `read_result cx _ _ = (INL v,_)` mp_tac >>
     qpat_assum `eval_expr cx amount_e _ = (INL _,_)` mp_tac >>
     qpat_assum `read_result cx _ _ = (INL value,_)` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[body_exprs_full_ok_def] >> metis_tac[]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type gas_e) gas_e mid'` by
    (qpat_x_assum `body_expr_full_ok cx gas_e` mp_tac >>
     simp[Once body_expr_full_ok_def] >> metis_tac[]) >>
  `gas_shadow_compiles (lower_value compile_expr cenv (expr_type gas_e) gas_e)
    (lower_value compile_expr cenv (expr_type gas_e) (gas_shadow_expr gas_e))` by
    (irule (SRULE [] (Q.INST [`sh` |-> `T`]
       gasShadowCompileHelpersTheory.gas_shadow_compiles_lower_value)) >>
     simp[gas_shadow_compile_expr]) >>
  qpat_x_assum `gas_shadow_compiles _ _`
    (mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
  disch_then (qspecl_then [`amount_end`,`shadow_amount_end`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  `fn_has_code amount_end sm func /\ fn_has_code shadow_amount_end sm' shadow_func` by
    metis_tac[fragExecTheory.fn_has_code_split,compileEnvTheory.cs_extends_trans] >>
  `sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= amount_end.cs_next_var` by
    metis_tac[exprSimSourceTheory.expr_body_pre_lower_value_word_shape] >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace`
      (drule_then strip_assume_tac)) >>
  qpat_assum `!H. valid_horizon cx st0 H mid'.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid'.storage_trace`
      (drule_then strip_assume_tac)) >>
  `return_buf_frame d cenv s1 t` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qpat_assum `return_buf_frame d cenv sa s0` (irule_at Any) >>
     fs[loweringPostsTheory.expr_post_def]) >>
  `return_buf_frame d cenv amount_end t'` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qpat_assum `return_buf_frame d cenv s1 t` (irule_at Any) >>
     fs[loweringPostsTheory.expr_post_def]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ gas_e _` mp_tac >>
  rewrite_tac[expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`,`amount_end`,`sm`,`shadow_amount_end`,`sm'`,
    `gas_op`,`t'`,`G1'`,`tn1'`] mp_tac) >>
  (impl_tac >-
    (simp[exprSimSourceTheory.expr_body_pre_gas_admissible] >>
     conj_tac >- metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var,
                           arithmeticTheory.LESS_EQ_TRANS] >>
     conj_tac >- metis_tac[loweringShapeDefsTheory.not_fresh_at_mono,
                           arithmeticTheory.LESS_EQ_TRANS] >>
     conj_tac >- metis_tac[loweringShapeDefsTheory.not_fresh_at_mono,
                           arithmeticTheory.LESS_EQ_TRANS] >>
     rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid'.storage_trace ==> _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     fs[loweringPostsTheory.expr_post_def])) >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ gasQ gasR` >>
  once_rewrite_tac[vyperStateTheory.bind_assoc] >>
  simp[vyperStateTheory.bind_return] >>
  once_rewrite_tac[exprSimWordArgsTheory.eval_exprs_cons_action] >>
  once_rewrite_tac[vyperStateTheory.bind_assoc] >>
  simp[vyperStateTheory.bind_return] >>
  irule gas_outcome_full_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
      qexistsl_tac [`mid''`,`t''`,`v'`] >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_value >> simp[])
  >~ [`storage_trace_frame _`]
  >- (rpt gen_tac >> BETA_TAC >>
      irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
      simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
           vyperStorageTraceTheory.storage_trace_frame_send,
           vyperStorageTraceTheory.storage_trace_frame_read_result])
  >- (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
      simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
           vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
  qexists `\H res ee G tn z. gasQ H res ee G tn z /\ ~z.vs_halted /\ ee.gas_obs = []` >>
  conj_tac >~ [`storage_trace_domain _ _ _`] >- suspend "after_gas" >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ gasQ gasR` (irule_at Any) >>
  conj_tac >- simp[] >>
  simp[Abbr `gasR`,Abbr `amountR`] >> rpt strip_tac >>
  Cases_on `res` >> fs[exprSimDefsTheory.expr_exit_def]
QED

Resume send_expr_sim_full[call_tail]:
  markerLib.RESUME_TAC >>
  `sa.cs_next_var <= amount_end.cs_next_var /\
   sa.cs_next_id <= amount_end.cs_next_id` by
    metis_tac[exprSimSourceTheory.expr_body_pre_lower_value_word_shape,
              arithmeticTheory.LESS_EQ_TRANS] >>
  `local_ptrs_reserved cenv amount_end` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==>
      not_fresh_at amount_end p` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==>
      not_fresh_at amount_end p` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `fn_has_code amount_end sb func` by
    metis_tac[fragExecTheory.fn_has_code_split,compileEnvTheory.cs_extends_trans] >>
  `!H. valid_horizon cx st0 H mid'.storage_trace ==>
     stmt_state_rel H ctx func cenv cx mid' t' /\
     storage_well_formed_on cx mid' (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx mid' G1' tn1' t'` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid'.storage_trace ==> _`
       (qspec_then `H` (drule_then (mp_tac o BETA_RULE))) >>
     simp[NoAsms] >> strip_tac >>
     qpat_assum `expr_post H _ _ _ _ amount_e _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.expr_post_def]) >>
     simp[]) >>
  `op_taint tn1' addr_op = {} /\ op_taint tn1' amount_op = {}` by
    fs[bodyPtrDefsTheory.ptr_val_ok_def] >>
  `dest_AddressV v = SOME (w2w (typed_val_to_w256 (BaseTV AddressT) v))` by
    metis_tac[address_typed_dest] >>
  `dest_NumV value = SOME (w2n (typed_val_to_w256 (BaseTV (UintT 256)) value))` by
    metis_tac[uint256_typed_dest] >>
  `outcomes_accounts_typed mid'.outcomes /\
   accounts_runtime_well_typed mid'.accounts` by
    fs[expr_sim_inv_def,
       vyperTypeExtCallCoreTheory.accounts_runtime_well_typed_accounts_well_typed] >>
  `s0.vs_alloca_next <= t'.vs_alloca_next` by
    metis_tac[arithmeticTheory.LESS_EQ_TRANS] >>
  `MAP finite_map$FDOM es.scopes = MAP finite_map$FDOM mid'.scopes` by
    fs[loweringPostsTheory.wb_frame_def,loweringPostsTheory.locals_kept_def] >>
  qabbrev_tac `send_expr = Call NoneT (Send F) [to_e;amount_e] dflt` >>
  `expr_has_effect send_expr /\ post_value_type cenv send_expr = NoneT /\
   expr_type send_expr = NoneT` by
    simp[Abbr `send_expr`,loweringPostsTheory.expr_has_effect_thm,
         vyperASTTheory.expr_type_def] >>
  irule gas_outcome_full_post_mono >>
  irule_at Any (Q.INST [`e` |-> `send_expr`, `es` |-> `es`,
    `sa` |-> `sa`, `s0` |-> `s0`]
    (SPEC_ALL (CONV_RULE (DEPTH_CONV ETA_CONV)
      bodyFullSendPostTheory.send_tail_outcome_full))) >>
  simp[venomStateTheory.eval_operand_def,ptrDisciplineTheory.op_taint_def] >>
  suspend "suffix_post"
QED

Resume send_expr_sim_full[suffix_post]:
  qexistsl_tac [`amount_op`,`Var (STRING #"%" (toString amount_end.cs_next_var))`,
    `amount_end`,`send_expr`,`sb`,`sa`,`s3`,`s0`,`0w`,`Lit 0w`,`es`,`d`,`cenv`,
    `typed_val_to_w256 (BaseTV AddressT) v`,`addr_op`] >>
  simp[GSYM ptrDisciplineTheory.op_taint_def,Abbr `amountR`,
       exprSimMemDefsTheory.expr_store_bound_none,
       callStepPtrTheory.ptr_val_ok_none] >>
  suspend "suffix_finish"
QED

Resume send_expr_sim_full[suffix_finish]:
  simp[venomStateTheory.eval_operand_def] >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- (strip_tac >> irule callStepPtrTheory.ptr_buf_ok_zero_type >>
      simp[Abbr `send_expr`,callStepPtrTheory.send_none_buffer_size]) >>
  qspecl_then [`lo`,`cenv`,`es`,`sa`,`G0`,`tn0`,`s0`,
    `G1'`,`tn1'`,`mid'`,`amount_end`,`G'`,`tn'`,`t'`,
    `storage_trace_horizon mid.storage_trace`,`ctx`,`func`,`cx`,`mid'`]
    mp_tac wordArgsPtrTheory.ghost_kept_at_wb_trans >> simp[]
QED

Resume send_expr_sim_full[after_gas]:
  map_every qx_gen_tac [`gas_marks`,`gas_res`,`gas_end`,`gas_G`,`gas_tn`,`gas_s`] >>
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon gas_end.storage_trace)
     gas_end.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `?gas_v. gas_res = INL gas_v` by
    (qpat_assum `!H. valid_horizon _ _ H gas_end.storage_trace ==> _`
       (qspec_then `storage_trace_horizon gas_end.storage_trace` mp_tac) >>
     simp[Abbr `gasQ`] >> metis_tac[]) >>
  gvs[] >>
  qpat_assum `!H. valid_horizon _ _ H gas_end.storage_trace ==> _`
    (qspec_then `storage_trace_horizon gas_end.storage_trace` mp_tac) >>
  simp[NoAsms,Abbr `gasQ`] >> strip_tac >>
  qpat_x_assum `valid_horizon _ _ _ _ ==> _`
    (drule_then strip_assume_tac) >>
  `expr_result_typed env gas_e (Value gas_v) /\
   expr_sim_inv cenv cx env gas_end` by
    (qpat_assum `!tail. bind (eval_expr cx gas_e) _ _ = _`
       (qspec_then `[]` mp_tac) >> strip_tac >>
     `expr_body_pre cenv cx env gas_e
        (mid' with gas_obs := gas_explicit gas_marks t'.vs_gas_readings ++ [])` by
       simp[] >>
     drule_all (CONV_RULE (DEPTH_CONV ETA_CONV)
       exprSimSourceTheory.expr_body_pre_eval) >> simp[]) >>
  `value_has_type (BaseTV (UintT 256)) gas_v` by
    (fs[vyperTypeExprResultTheory.expr_result_typed_def,
       vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
       vyperTypeInvariantsTheory.value_result_typed_def] >>
     gvs[vyperValueTheory.evaluate_type_def]) >>
  `eval_operand gas_op gas_s =
     SOME (typed_val_to_w256 (BaseTV (UintT 256)) gas_v)` by
    (qpat_assum `expr_post _ _ _ _ _ gas_e _ _ _ _ _ _ _ _`
       (mp_tac o Q.INST [`tv` |-> `BaseTV (UintT 256)`] o
        MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
          exprSimPrecompilesTheory.expr_post_typed_stack_operand)) >>
     simp[vyperValueTheory.evaluate_type_def]) >>
  suspend "gas_frame"
QED

Resume send_expr_sim_full[gas_frame]:
  `!x. addr_op = Var x ==> not_fresh_at amount_end x` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `!x. amount_op = Var x ==> not_fresh_at amount_end x` by
    metis_tac[exprSimSourceTheory.expr_body_pre_lower_value_word_shape] >>
  `(!l. addr_op <> Label l) /\ (!l. amount_op <> Label l)` by
    metis_tac[exprSimSourceTheory.expr_body_pre_lower_value_word_shape] >>
  `!x w. not_fresh_at amount_end x /\ lookup_var x t' = SOME w ==>
     lookup_var x gas_s = SOME w` by
    (qpat_assum `expr_post _ _ _ _ _ gas_e _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.expr_post_def]) >>
     first_assum ACCEPT_TAC) >>
  `(!w. eval_operand addr_op t' = SOME w ==>
      eval_operand addr_op gas_s = SOME w) /\
   (!w. eval_operand amount_op t' = SOME w ==>
      eval_operand amount_op gas_s = SOME w)` by
    (qpat_assum `!x w. not_fresh_at amount_end x /\ lookup_var x t' = SOME w ==>
       lookup_var x gas_s = SOME w` mp_tac >>
     qpat_assum `!x. addr_op = Var x ==> not_fresh_at amount_end x` mp_tac >>
     qpat_assum `!x. amount_op = Var x ==> not_fresh_at amount_end x` mp_tac >>
     qpat_assum `!l. addr_op <> Label l` mp_tac >>
     qpat_assum `!l. amount_op <> Label l` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `addr_op` >> Cases_on `amount_op` >>
     simp[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  `!x. not_fresh_at amount_end x ==>
     op_taint gas_tn (Var x) = op_taint tn1' (Var x)` by
    (qpat_assum `ghost_kept_at lo cenv mid' amount_end G1' tn1' t' gas_G gas_tn`
       mp_tac >> rpt (pop_assum kall_tac) >>
     simp[bodyPtrDefsTheory.ghost_kept_at_def] >> metis_tac[]) >>
  `op_taint gas_tn addr_op = op_taint tn1' addr_op /\
   op_taint gas_tn amount_op = op_taint tn1' amount_op` by
    (conj_tac >> irule emittedSeqComposePtrTheory.old_operand_taint_frame >>
     qexists_tac `amount_end` >> simp[]) >>
  `sa.cs_next_var <= amount_end.cs_next_var /\
   sa.cs_next_id <= amount_end.cs_next_id` by
    metis_tac[exprSimSourceTheory.expr_body_pre_lower_value_word_shape,
              arithmeticTheory.LESS_EQ_TRANS] >>
  `wb_frame cenv mid' gas_end amount_end t' gas_s` by
    qpat_assum `expr_post _ _ _ _ _ gas_e _ _ _ _ _ _ _ _`
      (ACCEPT_TAC o MATCH_MP (SPEC_ALL exprSimWordArgsTheory.expr_post_frame)) >>
  `MAP finite_map$FDOM es.scopes = MAP finite_map$FDOM mid'.scopes` by
    fs[loweringPostsTheory.wb_frame_def,loweringPostsTheory.locals_kept_def] >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx es s0` by
    (qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
       (qspec_then `storage_trace_horizon mid.storage_trace`
         (drule_then strip_assume_tac)) >> simp[]) >>
  `wb_frame cenv es gas_end sa s0 gas_s` by
    (qpat_assum `wb_frame cenv es mid' sa s0 t'` mp_tac >>
     qpat_assum `wb_frame cenv mid' gas_end amount_end t' gas_s` mp_tac >>
     qpat_assum `stmt_state_rel (storage_trace_horizon mid.storage_trace)
       ctx func cenv cx es s0` mp_tac >>
     qpat_assum `local_ptrs_reserved cenv sa` mp_tac >>
     qpat_assum `MAP finite_map$FDOM es.scopes = MAP finite_map$FDOM mid'.scopes` mp_tac >>
     qpat_assum `sa.cs_next_var <= amount_end.cs_next_var` mp_tac >>
     qpat_assum `sa.cs_next_id <= amount_end.cs_next_id` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     drule_all exprSimWordArgsTheory.wb_frame_trans >> simp[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 gas_G gas_tn` by
    (qspecl_then [`lo`,`cenv`,`es`,`sa`,`G0`,`tn0`,`s0`,`G1'`,`tn1'`,`mid'`,
      `amount_end`,`gas_G`,`gas_tn`,`t'`,
      `storage_trace_horizon mid.storage_trace`,`ctx`,`func`,`cx`,`mid'`]
      mp_tac wordArgsPtrTheory.ghost_kept_at_wb_trans >> simp[]) >>
  suspend "gas_call_tail"
QED

Resume send_expr_sim_full[gas_call_tail]:
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    metis_tac[exprSimSourceTheory.expr_body_pre_lower_value_word_shape,
              arithmeticTheory.LESS_EQ_TRANS] >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `fn_has_code sm sb func` by
    metis_tac[fragExecTheory.fn_has_code_split,compileEnvTheory.cs_extends_trans] >>
  `!H. valid_horizon cx st0 H gas_end.storage_trace ==>
    stmt_state_rel H ctx func cenv cx gas_end gas_s /\
    storage_well_formed_on cx gas_end (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx gas_end gas_G gas_tn gas_s` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H gas_end.storage_trace ==> _`
       (qspec_then `H` (drule_then (mp_tac o BETA_RULE))) >>
     simp[NoAsms] >> strip_tac >>
     qpat_assum `expr_post H _ _ _ _ gas_e _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.expr_post_def]) >>
     simp[]) >>
  `op_taint gas_tn gas_op = {} /\ op_taint gas_tn addr_op = {} /\
   op_taint gas_tn amount_op = {}` by
    fs[bodyPtrDefsTheory.ptr_val_ok_def] >>
  `eval_operand addr_op gas_s = SOME (typed_val_to_w256 (BaseTV AddressT) v)` by
    (qpat_assum `!w. eval_operand addr_op t' = SOME w ==> _` irule >> simp[]) >>
  `eval_operand amount_op gas_s =
    SOME (typed_val_to_w256 (BaseTV (UintT 256)) value)` by
    (qpat_assum `!w. eval_operand amount_op t' = SOME w ==> _` irule >> simp[]) >>
  `dest_AddressV v = SOME (w2w (typed_val_to_w256 (BaseTV AddressT) v))` by
    metis_tac[address_typed_dest] >>
  `dest_NumV value = SOME (w2n (typed_val_to_w256 (BaseTV (UintT 256)) value))` by
    metis_tac[uint256_typed_dest] >>
  `outcomes_accounts_typed gas_end.outcomes /\
   accounts_runtime_well_typed gas_end.accounts` by
    fs[expr_sim_inv_def,
       vyperTypeExtCallCoreTheory.accounts_runtime_well_typed_accounts_well_typed] >>
  `s0.vs_alloca_next <= gas_s.vs_alloca_next` by
    metis_tac[arithmeticTheory.LESS_EQ_TRANS] >>
  `MAP finite_map$FDOM es.scopes = MAP finite_map$FDOM gas_end.scopes` by
    fs[loweringPostsTheory.wb_frame_def,loweringPostsTheory.locals_kept_def] >>
  qabbrev_tac `send_expr = Call NoneT (Send T) [to_e;amount_e;gas_e] dflt` >>
  `expr_has_effect send_expr /\ post_value_type cenv send_expr = NoneT /\
   expr_type send_expr = NoneT` by
    simp[Abbr `send_expr`,loweringPostsTheory.expr_has_effect_thm,
         vyperASTTheory.expr_type_def] >>
  irule gas_outcome_full_post_mono >>
  irule_at Any (Q.INST [`e` |-> `send_expr`, `es` |-> `es`,
    `sa` |-> `sa`, `s0` |-> `s0`]
    (SPEC_ALL (CONV_RULE (DEPTH_CONV ETA_CONV)
      bodyFullSendPostTheory.send_tail_outcome_full))) >>
  simp[venomStateTheory.eval_operand_def,ptrDisciplineTheory.op_taint_def] >>
  suspend "gas_suffix_post"
QED

Resume send_expr_sim_full[gas_suffix_post]:
  qexistsl_tac [`amount_op`,`Var (STRING #"%" (toString sm.cs_next_var))`,
    `sm`,`send_expr`,`sb`,`sa`,`s3`,`s0`,
    `typed_val_to_w256 (BaseTV (UintT 256)) gas_v`,`gas_op`,`es`,`d`,`cenv`,
    `typed_val_to_w256 (BaseTV AddressT) v`,`addr_op`] >>
  simp[GSYM ptrDisciplineTheory.op_taint_def,Abbr `amountR`,
       exprSimMemDefsTheory.expr_store_bound_none,
       callStepPtrTheory.ptr_val_ok_none] >>
  suspend "gas_suffix_finish"
QED

Resume send_expr_sim_full[gas_suffix_finish]:
  rpt gen_tac >> strip_tac >> conj_tac
  >- (strip_tac >> irule callStepPtrTheory.ptr_buf_ok_zero_type >>
      simp[Abbr `send_expr`,callStepPtrTheory.send_none_buffer_size]) >>
  qspecl_then [`lo`,`cenv`,`es`,`sa`,`G0`,`tn0`,`s0`,
    `gas_G`,`gas_tn`,`gas_end`,`sm`,`G'`,`tn'`,`gas_s`,
    `storage_trace_horizon mid.storage_trace`,`ctx`,`func`,`cx`,`gas_end`]
    mp_tac wordArgsPtrTheory.ghost_kept_at_wb_trans >> simp[]
QED

Finalise send_expr_sim_full

Theorem send_expr_vv_sim_full:
  !DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx env ty ann
   has_gas args dflt es.
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Call ann (Send has_gas) args dflt) es /\
    body_exprs_full_ok cx args ==>
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Call ann (Send has_gas) args dflt) es
Proof
  rpt gen_tac >> strip_tac >>
  drule send_pre_types >> strip_tac >> gvs[] >>
  irule expr_vv_sim_stack_full >> rpt conj_tac
  >~ [`!sa. ?t op sb. compile_expr cenv ty
        (Call NoneT (Send has_gas) args dflt) sa = (StackValue t op,sb)`]
  >- (gen_tac >>
      Cases_on `compile_expr cenv ty (Call NoneT (Send has_gas) args dflt) sa` >>
      drule compile_expr_send_stack >> simp[])
  >~ [`expr_sim_full _ _ _ _ _ _`]
  >- (irule send_expr_sim_full >> metis_tac[])
  >~ [`eval_expr _ _ _ = (INL _,_)`]
  >- metis_tac[eval_expr_send_value] >>
  simp[loweringPostsTheory.post_value_type_def, expr_type_def, lowered_value_type_def,
       vyperValueTheory.evaluate_type_def, valueEncodingTheory.type_memory_size_def]
QED

(* The send operands and CALL/ASSERT suffix share the joint witness. *)
Theorem body_send_case_full:
  !cx v12 has_gas es v13.
    (!s'' x t.
       type_check (LENGTH es = if has_gas then 3 else 2) "Send args" s'' =
       (INL x,t) ==>
       body_exprs_full_ok cx es) ==>
    body_expr_full_ok cx (Call v12 (Send has_gas) es v13)
Proof
  rpt gen_tac >> disch_tac >> rewrite_tac[body_expr_full_ok_def] >>
  reverse conj_tac >- simp[] >> rpt gen_tac >> strip_tac >>
  drule send_pre_types >> strip_tac >>
  `body_exprs_full_ok cx es` by
    (first_x_assum irule >>
     simp[vyperStateTheory.type_check_def,vyperStateTheory.check_def,
          vyperStateTheory.assert_def] >> metis_tac[]) >>
  conj_tac
  >- (irule send_expr_sim_full >> metis_tac[]) >>
  irule send_expr_vv_sim_full >> metis_tac[]
QED
