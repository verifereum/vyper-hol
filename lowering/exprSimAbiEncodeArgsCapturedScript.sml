(*
 * Expression simulation: one captured abi_encode argument, counted.
 *
 * A composite argument that a later argument may mutate is compiled and
 * then materialized into a fresh buffer at its lowered type; followed by
 * the counted run of the remaining arguments, the whole list runs as
 * eval_exprs on an actual counted path.
 *)

Theory exprSimAbiEncodeArgsCaptured
Ancestors
  loweringStateRelDefs
  abiEncodeArgsSim exprSimHypsDefs exprSimWordArgs abiDecoderReentry
  exprSimAbiGasBridge exprSimAbiEncodeArgsMaterializePath
  vyperStorageTrace vyperStorageFootprint gasStorage

Theorem captured_owned_cons_post:
  materialize_owned_post H ctx func ce cx e es sa mid sm s0 es1 v op tv t /\
  abi_args_post H ctx func ce cx es1 sm sb t es' args ops vs u /\
  stmt_state_rel H ctx func ce cx es s0 /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  MAP FDOM es'.scopes = MAP FDOM es1.scopes /\
  ci_mono sa sm /\ ci_mono sm sb /\
  (!x. op = Var x ==> not_fresh_at sm x) /\ (!l. op <> Label l) /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\ val_wf tv v ==>
  abi_args_post H ctx func ce cx es sa sb s0 es' (e::args) (op::ops) (v::vs) u
Proof
  strip_tac >>
  qpat_x_assum `materialize_owned_post H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [materialize_owned_post_def]) >>
  `wb_frame ce es1 es' sm t u` by metis_tac[abi_args_post_def] >>
  `expr_val_rel cx (lowered_value_type ce e) v op u` by
    (Cases_on `is_word_type (lowered_value_type ce e)`
     >- (gvs[loweringPostsTheory.expr_val_rel_def] >>
         metis_tac[abi_args_operand_kept]) >>
     irule abi_args_captured_value_kept >>
     qpat_assum `wb_frame ce es1 es' sm t u` (irule_at Any) >>
     simp[] >>
     qexistsl_tac [`type_memory_size tv`, `w2n w`, `mid.cs_next_id`] >>
     simp[] >> conj_tac
     >- metis_tac[arithmeticTheory.ADD_COMM] >>
     simp[exprSimPropsTheory.val_footprint_le]) >>
  `expr_val_at ce cx (lowered_value_type ce e) sa sb es' v op u` by
    (irule abi_args_location_end_mono >> qexists_tac `sm` >>
     conj_tac >- gvs[exprLoweringPropsTheory.ci_mono_def] >>
     irule abi_args_location_kept >> metis_tac[]) >>
  `wb_frame ce es es' sa s0 u` by
    (irule (INST_TYPE [alpha |-> ``:256``] wb_frame_trans) >> simp[] >> conj_tac
     >- (qexistsl_tac [`es1`, `sm`, `t`] >>
         gvs[exprLoweringPropsTheory.ci_mono_def]) >>
     qexistsl_tac [`H`, `ctx`, `cx`, `func`] >> simp[]) >>
  rewrite_tac[abi_args_post_cons] >> simp[] >>
  qpat_x_assum `abi_args_post H _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[abi_args_post_def] >> strip_tac >> simp[] >>
  irule listTheory.LIST_REL_mono >> goal_assum (drule_at Any) >>
  simp[] >> rpt strip_tac >>
  irule exprSimPropsTheory.expr_val_at_start_mono >>
  gvs[exprLoweringPropsTheory.ci_mono_def] >> metis_tac[]
QED

Theorem abi_args_captured_cons_sim:
  expr_vv_sim ctx func ce cx (expr_type e) e es /\
  gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
  expr_body_pre ce cx env e es /\
  compile_expr ce (expr_type e) e sa = (vv,mid) /\
  compile_materialize_vv ce (lowered_value_type ce e) vv mid = (op,sm) /\
  fn_has_code sa mid func /\ fn_has_code mid sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce mid /\ local_ptrs_reserved ce sm /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func ce cx es s0 /\
     storage_well_formed_on cx es (FST H)) /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!gs v es1.
     bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,es1) ==>
     MAP FDOM es.scopes = MAP FDOM es1.scopes /\
     ?tv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
          value_has_type tv v /\ val_wf tv v /\
          type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
          type_memory_size tv < 2 ** 64 /\
          type_memory_size tv + 64 < dimword (:256)) /\
  (!gs v es1 gs' rr ee.
     bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,es1) /\
     eval_exprs cx args (es1 with gas_obs := gs') = (rr,ee) ==>
     MAP FDOM ee.scopes = MAP FDOM es1.scopes) /\
  ci_mono sa mid /\ ci_mono mid sm /\ ci_mono sm sb /\
  (!x. vv_operand vv = Var x ==> not_fresh_at mid x) /\
  (!x. op = Var x ==> not_fresh_at sm x) /\ (!l. op <> Label l) /\
  ~is_word_type (expr_type e) /\
  (!gs v es1 t.
     bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,es1) /\
     (!H. valid_horizon cx st0 H es1.storage_trace ==>
        stmt_state_rel H ctx func ce cx es1 t /\
        storage_well_formed_on cx es1 (FST H)) /\ ~t.vs_halted /\
     t.vs_current_bb = sm.cs_current_bb /\
     t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
     gas_outcome F (cx_tops cx) (ctx,func) cx st0 (eval_exprs cx args) (es1,t)
       (\H rr ee u. ?vs. rr = INL vs /\
          abi_args_post H ctx func ce cx es1 sm sb t ee args ops vs u /\
          (~EXISTS expr_has_effect args ==> pure_frame ce func es1 sm t u) /\
          u.vs_current_bb = sb.cs_current_bb /\
          u.vs_inst_idx = LENGTH sb.cs_current_insts)
       (\H rr ee r. wb_args_exit rr r)) ==>
  gas_outcome F (cx_tops cx) (ctx,func) cx st0 (eval_exprs cx (e::args)) (es,s0)
    (\H rr ee u. ?vs. rr = INL vs /\
       abi_args_post H ctx func ce cx es sa sb s0 ee (e::args) (op::ops) vs u /\
       (~EXISTS expr_has_effect (e::args) ==> pure_frame ce func es sa s0 u) /\
       u.vs_current_bb = sb.cs_current_bb /\
       u.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\H rr ee r. wb_args_exit rr r)
Proof
  strip_tac >> drule_all abi_args_vv_error_prefix >>
  `storage_trace_frame (eval_expr cx e) /\
   storage_trace_frame (eval_exprs cx args)` by
    simp[evaluate_storage_trace_frame] >>
  `!v. storage_trace_frame (bind (eval_exprs cx args) (\vs. return (v::vs)))` by
    (gen_tac >> irule storage_trace_frame_bind_all >>
     simp[evaluate_storage_trace_frame, storage_trace_frame_return]) >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      rewrite_tac[eval_exprs_cons_action] >>
      irule gas_bad_storage_at_bind_left >> simp[] >>
      irule gas_bad_storage_at_bind_left >>
      simp[storage_trace_frame_read_result])
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gasSummaryTheory.gas_summary_at_def]) >>
      (reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
       >- (qexists_tac `marks` >> disj1_tac >>
           rewrite_tac[eval_exprs_cons_action] >>
           irule gas_bad_storage_at_bind_left >> simp[] >>
           irule gas_bad_storage_at_bind_left >>
           simp[storage_trace_frame_read_result] >>
           irule gas_bad_storage_at_counted_prefix >> metis_tac[])) >>
      `valid_horizon cx st0 (storage_trace_horizon es_end.storage_trace)
         es_end.storage_trace` by fs[storage_trace_domain_def]
      >- suspend "head_normal"
      >> suspend "head_exit") >>
  suspend "head_exempt"
QED

Resume abi_args_captured_cons_sim[head_normal]:
  qpat_x_assum `(\res ee t. _) _ _ _` (assume_tac o SIMP_RULE (srw_ss()) []) >>
  qpat_assum `!H. valid_horizon _ _ H es_end.storage_trace ==> ?tv v. _`
    (drule_then (qx_choosel_then [`tv`, `v`] strip_assume_tac)) >>
  qpat_x_assum `res = INL tv` SUBST_ALL_TAC >>
  qpat_x_assum `r = OK t` SUBST_ALL_TAC >>
  qpat_x_assum `!H. valid_horizon _ _ H es_end.storage_trace ==> ?tv v. _`
    (assume_tac o SIMP_RULE (srw_ss()) []) >>
  `?obs. es_end.storage_trace = es.storage_trace ++ obs` by
    (qpat_assum `gas_marked_exec _ _ (eval_expr cx e) (es, s0) _ _ _ _`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [gasSummaryTheory.gas_marked_exec_def]) >>
     disch_then (qspec_then `[]` assume_tac) >>
     qpat_assum `storage_trace_frame (eval_expr cx e)`
       (fn th => drule (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                                   storage_trace_frame_prefix) th)) >>
     simp[]) >>
  `!H. valid_horizon cx st0 H es_end.storage_trace ==>
       valid_horizon cx st0 H es.storage_trace` by
    simp[valid_horizon_def] >>
  qpat_x_assum `es_end.storage_trace = _` kall_tac >>
  `!H. valid_horizon cx st0 H es_end.storage_trace ==>
     vv_post H ctx func ce cx e es sa mid s0 (es_end with gas_obs := []) tv vv t` by
    metis_tac[] >>
  `stmt_state_rel (storage_trace_horizon es_end.storage_trace)
     ctx func ce cx es s0` by metis_tac[] >>
  `!tail. read_result cx tv (es_end with gas_obs := tail) =
      (INL v,es_end with gas_obs := tail)` by
    (drule exprSimMemorySourceTheory.read_result_gas_obs >> simp[]) >>
  `gas_marked_exec F (ctx,func)
     (bind (eval_expr cx e) (read_result cx)) (es,s0) marks (INL v) es_end (OK t)` by
    (irule exprSimBopRestWordComposeTheory.rest_word_marked_read >> metis_tac[]) >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v,es_end with gas_obs := [])` by
    (qpat_assum `gas_marked_exec _ _ (bind _ _) _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gasSummaryTheory.gas_marked_exec_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  qpat_assum `!gs v es1. _ ==> MAP FDOM _ = MAP FDOM _ /\ _` drule >> strip_tac >>
  `~t.vs_halted` by
    metis_tac[gasSummaryTheory.gas_marked_exec_def,
      fragGasModeTheory.gas_marked_path_exec, fragGasPathTheory.gas_path_normal] >>
  `sa.cs_next_var <= mid.cs_next_var /\ sa.cs_next_id <= mid.cs_next_id` by
    gvs[exprLoweringPropsTheory.ci_mono_def] >>
  `type_memory_size tv' < 2 ** 64` by simp[] >>
  `!tvt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tvt /\
          ~is_word_type (post_value_type ce e) ==>
       type_memory_bytes ce (post_value_type ce e) = type_memory_size tvt /\
       type_memory_size tvt < 2 ** 64` by
    metis_tac[materialize_captured_post_copy_ok] >>
  drule_all (Q.INST [`HP` |-> `\H. valid_horizon cx st0 H es_end.storage_trace`]
               compile_materialize_vv_owned_path |> BETA_RULE) >>
  strip_tac >>
  `gas_marked_exec F (ctx,func)
     (bind (eval_expr cx e) (read_result cx)) (es,s0) marks (INL v) es_end (OK t')` by
    (qpat_assum `gas_marked_exec _ _ (bind _ _) _ _ _ _ _` mp_tac >>
     rewrite_tac[gasSummaryTheory.gas_marked_exec_def] >> strip_tac >> simp[] >>
     qpat_assum `gas_marked_path _ _ _ s0 _ _`
       (mp_then Any mp_tac fragGasModeTheory.gas_marked_path_then) >>
     disch_then drule >> simp[]) >>
  `!H. valid_horizon cx st0 H es_end.storage_trace ==>
     stmt_state_rel H ctx func ce cx (es_end with gas_obs := []) t' /\
     storage_well_formed_on cx (es_end with gas_obs := []) (FST H)` by
    (rpt strip_tac >>
     qpat_x_assum `!H. valid_horizon _ _ H _ ==> materialize_owned_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (drule_then mp_tac) >>
     qpat_x_assum `!H. valid_horizon _ _ H _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (drule_then mp_tac) >>
     simp[materialize_owned_post_def, loweringPostsTheory.vv_post_def]) >>
  qpat_x_assum `!gs v es1 t. _`
    (qspecl_then [`gas_explicit marks s0.vs_gas_readings`, `v`,
                  `es_end with gas_obs := []`, `t'`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks ++ marks'` >> disj1_tac >>
      rewrite_tac[eval_exprs_cons_action] >>
      irule gas_bad_storage_at_bind_right >>
      qpat_assum `gas_marked_exec _ _ (bind _ _) (es, s0) _ _ _ (OK t')`
        (irule_at Any) >>
      simp[] >> irule gas_bad_storage_at_bind_left >>
      simp[storage_trace_frame_return])
  >- (qpat_x_assum `gas_summary_at _ _ _ (eval_exprs _ _) _ _ _`
        (strip_assume_tac o REWRITE_RULE [gasSummaryTheory.gas_summary_at_def]) >>
      (reverse (Cases_on `storage_trace_domain cx st0 es_end'.storage_trace`)
       >- (qexists_tac `marks ++ marks'` >> disj1_tac >>
           rewrite_tac[eval_exprs_cons_action] >>
           irule gas_bad_storage_at_bind_right >>
           qpat_assum `gas_marked_exec _ _ (bind _ _) (es, s0) _ _ _ (OK t')`
             (irule_at Any) >>
           simp[] >> irule gas_bad_storage_at_bind_left >>
           simp[storage_trace_frame_return] >>
           irule gas_bad_storage_at_counted_prefix >> metis_tac[])) >>
      `valid_horizon cx st0 (storage_trace_horizon es_end'.storage_trace)
         es_end'.storage_trace` by fs[storage_trace_domain_def]
      >- suspend "tail_normal"
      >> suspend "tail_exit") >>
  suspend "tail_exempt"
QED
Resume abi_args_captured_cons_sim[head_exit]:
  qpat_x_assum `(\res ee r. _) _ _ _` (assume_tac o SIMP_RULE (srw_ss()) []) >>
  `expr_exit res r` by metis_tac[] >>
  Cases_on `res` >- gvs[] >>
  rename1 `gas_marked_exec _ _ _ _ _ (INR exc) _ _` >>
  qexists_tac `marks` >> disj2_tac >> disj1_tac >>
  simp[gasSummaryTheory.gas_summary_at_def] >>
  qexistsl_tac [`INR exc`, `es_end`, `r`] >> conj_tac
  >- (rewrite_tac[eval_exprs_cons_action] >>
      irule gasSummaryComposeTheory.gas_marked_exec_bind_exception >>
      irule gasSummaryComposeTheory.gas_marked_exec_bind_exception >>
      first_assum ACCEPT_TAC) >>
  disj2_tac >> simp[wb_args_exit_def] >>
  qpat_x_assum `expr_exit _ _` mp_tac >>
  simp[stmtSimPropsTheory.expr_exit_INR_type]
QED
Resume abi_args_captured_cons_sim[head_exempt]:
  qexists_tac `marks` >> disj2_tac >> disj2_tac >>
  rewrite_tac[eval_exprs_cons_ignore_action, vyperStateTheory.bind_assoc] >>
  irule_at Any gasExemptCertTheory.gas_exempt_cert_error_result >>
  goal_assum (drule_at Any)
QED
Resume abi_args_captured_cons_sim[tail_normal]:
  qpat_x_assum `(\res ee t. _) _ _ _` (assume_tac o SIMP_RULE (srw_ss()) []) >>
  qpat_assum `!H. valid_horizon _ _ H es_end'.storage_trace ==> ?vs. _`
    (drule_then (qx_choose_then `vs` strip_assume_tac)) >>
  qpat_x_assum `res = INL vs` SUBST_ALL_TAC >>
  qpat_x_assum `!H. valid_horizon _ _ H es_end'.storage_trace ==> ?vs. _`
    (assume_tac o SIMP_RULE (srw_ss()) []) >>
  `?obs'. es_end'.storage_trace = es_end.storage_trace ++ obs'` by
    (qpat_assum `gas_marked_exec _ _ (eval_exprs _ _) _ _ _ _ _`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [gasSummaryTheory.gas_marked_exec_def]) >>
     disch_then (qspec_then `[]` assume_tac) >>
     qpat_assum `storage_trace_frame (eval_exprs _ _)`
       (fn th => drule (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                                   storage_trace_frame_prefix) th)) >>
     simp[]) >>
  `!H. valid_horizon cx st0 H es_end'.storage_trace ==>
       valid_horizon cx st0 H es_end.storage_trace` by
    simp[valid_horizon_def] >>
  qpat_x_assum `es_end'.storage_trace = _` kall_tac >>
  qexists_tac `marks ++ marks'` >> disj2_tac >> disj1_tac >>
  simp[gasSummaryTheory.gas_summary_at_def] >>
  qexistsl_tac [`INL (v::vs)`, `es_end'`, `OK t''`] >> conj_tac
  >- (rewrite_tac[eval_exprs_cons_action] >>
      irule gasSummaryComposeTheory.gas_marked_exec_bind_normal >>
      qpat_assum `gas_marked_exec _ _ (bind _ _) _ _ (INL v) _ (OK t')` (irule_at Any) >>
      BETA_TAC >>
      qpat_assum `gas_marked_exec _ _ _ _ _ (INL vs) _ _`
        (mp_tac o MATCH_MP gas_marked_exec_cons_values) >> simp[]) >>
  disj1_tac >> simp[] >> gen_tac >> strip_tac >>
  `valid_horizon cx st0 H es_end.storage_trace` by metis_tac[] >>
  `valid_horizon cx st0 H es.storage_trace` by metis_tac[] >>
  qpat_assum `!H. valid_horizon _ _ H es_end'.storage_trace ==>
                  abi_args_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> materialize_owned_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (drule_then assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  conj_tac
  >- suspend "post" >>
  suspend "frame"
QED
Resume abi_args_captured_cons_sim[post]:
  irule captured_owned_cons_post >>
  qpat_assum `materialize_owned_post H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `abi_args_post H _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> reverse conj_tac
  >- (gvs[exprLoweringPropsTheory.ci_mono_def] >> metis_tac[compileEnvTheory.cs_extends_trans]) >>
  qpat_x_assum `gas_marked_exec _ _ (eval_exprs cx args) _ _ _ _ _`
    (mp_tac o REWRITE_RULE [gasSummaryTheory.gas_marked_exec_def]) >>
  strip_tac >> first_x_assum (qspec_then `[]` assume_tac) >>
  qpat_x_assum `!gs v es1 gs' rr ee. _` drule >>
  simp[] >> strip_tac >> gvs[] >>
  first_x_assum drule >> simp[]
QED
Resume abi_args_captured_cons_sim[tail_exit]:
  qpat_x_assum `(\res ee r. _) _ _ _` (assume_tac o SIMP_RULE (srw_ss()) []) >>
  `wb_args_exit res r` by metis_tac[] >>
  Cases_on `res` >- gvs[wb_args_exit_def] >>
  rename1 `gas_marked_exec _ _ _ _ _ (INR exc) _ _` >>
  qexists_tac `marks ++ marks'` >> disj2_tac >> disj1_tac >>
  simp[gasSummaryTheory.gas_summary_at_def] >>
  qexistsl_tac [`INR exc`, `es_end'`, `r`] >> conj_tac
  >- (rewrite_tac[eval_exprs_cons_action] >>
      irule gasSummaryComposeTheory.gas_marked_exec_bind_normal >>
      qpat_assum `gas_marked_exec _ _ (bind _ _) _ _ (INL v) _ (OK t')` (irule_at Any) >>
      BETA_TAC >> irule gasSummaryComposeTheory.gas_marked_exec_bind_exception >> first_assum ACCEPT_TAC) >>
  disj2_tac >> gvs[wb_args_exit_def]
QED
Resume abi_args_captured_cons_sim[tail_exempt]:
  qexists_tac `marks ++ marks'` >> disj2_tac >> disj2_tac >>
  irule_at Any wb_args_tail_exempt_cert >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any)
QED
Resume abi_args_captured_cons_sim[frame]:
  rpt strip_tac >>
  qpat_assum `materialize_owned_post H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [materialize_owned_post_def]) >>
  `pure_frame ce func es_end sm t' t''` by
    (qpat_x_assum `EVERY _ args ==> pure_frame _ _ _ _ _ _` irule >>
     first_assum ACCEPT_TAC) >>
  match_mp_tac (Q.SPECL [`ce`, `func`, `es`, `es_end`, `sa`, `sm`, `s0`, `t'`, `t''`]
    exprSimPropsTheory.pure_frame_trans) >>
  rpt conj_tac
  >- (qpat_x_assum `~expr_has_effect e ==> _` irule >> first_assum ACCEPT_TAC)
  >- first_assum ACCEPT_TAC
  >- (fs[exprLoweringPropsTheory.ci_mono_def] >> decide_tac)
  >- fs[abi_args_post_def, loweringPostsTheory.wb_frame_def]
  >- first_assum ACCEPT_TAC
  >- fs[]
  >> fs[loweringPostsTheory.wb_frame_def]
QED
Finalise abi_args_captured_cons_sim

Theorem abi_args_captured_cons_sim_live:
  expr_vv_sim ctx func ce cx (expr_type e) e es /\
  gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
  expr_body_pre ce cx env e es /\
  compile_expr ce (expr_type e) e sa = (vv,mid) /\
  compile_materialize_vv ce (lowered_value_type ce e) vv mid = (op,sm) /\
  fn_has_code sa mid func /\ fn_has_code mid sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce mid /\ local_ptrs_reserved ce sm /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func ce cx es s0 /\
     storage_well_formed_on cx es (FST H)) /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!gs v es1.
     bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,es1) ==>
     MAP FDOM es.scopes = MAP FDOM es1.scopes /\
     ?tv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
          value_has_type tv v /\ val_wf tv v /\
          type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
          type_memory_size tv < 2 ** 64 /\
          type_memory_size tv + 64 < dimword (:256)) /\
  (!gs v es1 gs' rr ee.
     bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,es1) /\
     eval_exprs cx args (es1 with gas_obs := gs') = (rr,ee) ==>
     MAP FDOM ee.scopes = MAP FDOM es1.scopes) /\
  ci_mono sa mid /\ ci_mono mid sm /\ ci_mono sm sb /\
  (!x. vv_operand vv = Var x ==> not_fresh_at mid x) /\
  (!x. op = Var x ==> not_fresh_at sm x) /\ (!l. op <> Label l) /\
  ~is_word_type (expr_type e) /\
  (!gs v es1 t.
     bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,es1) /\
     (!H. valid_horizon cx st0 H es1.storage_trace ==>
        stmt_state_rel H ctx func ce cx es1 t /\
        storage_well_formed_on cx es1 (FST H)) /\ ~t.vs_halted /\
     t.vs_current_bb = sm.cs_current_bb /\
     t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
     gas_outcome F (cx_tops cx) (ctx,func) cx st0 (eval_exprs cx args) (es1,t)
       (\H rr ee u. ?vs. rr = INL vs /\
          abi_args_post H ctx func ce cx es1 sm sb t ee args ops vs u /\
          (~EXISTS expr_has_effect args ==> pure_frame ce func es1 sm t u) /\
          EVERY (abi_decoder_operand_live sb.cs_next_var) ops /\
          u.vs_current_bb = sb.cs_current_bb /\
          u.vs_inst_idx = LENGTH sb.cs_current_insts)
       (\H rr ee r. wb_args_exit rr r)) ==>
  gas_outcome F (cx_tops cx) (ctx,func) cx st0 (eval_exprs cx (e::args)) (es,s0)
    (\H rr ee u. ?vs. rr = INL vs /\
       abi_args_post H ctx func ce cx es sa sb s0 ee (e::args) (op::ops) vs u /\
       (~EXISTS expr_has_effect (e::args) ==> pure_frame ce func es sa s0 u) /\
       EVERY (abi_decoder_operand_live sb.cs_next_var) (op::ops) /\
       u.vs_current_bb = sb.cs_current_bb /\
       u.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\H rr ee r. wb_args_exit rr r)
Proof
  strip_tac >> drule_all abi_args_vv_error_prefix >>
  `storage_trace_frame (eval_expr cx e) /\
   storage_trace_frame (eval_exprs cx args)` by
    simp[evaluate_storage_trace_frame] >>
  `!v. storage_trace_frame (bind (eval_exprs cx args) (\vs. return (v::vs)))` by
    (gen_tac >> irule storage_trace_frame_bind_all >>
     simp[evaluate_storage_trace_frame, storage_trace_frame_return]) >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      rewrite_tac[eval_exprs_cons_action] >>
      irule gas_bad_storage_at_bind_left >> simp[] >>
      irule gas_bad_storage_at_bind_left >>
      simp[storage_trace_frame_read_result])
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gasSummaryTheory.gas_summary_at_def]) >>
      (reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
       >- (qexists_tac `marks` >> disj1_tac >>
           rewrite_tac[eval_exprs_cons_action] >>
           irule gas_bad_storage_at_bind_left >> simp[] >>
           irule gas_bad_storage_at_bind_left >>
           simp[storage_trace_frame_read_result] >>
           irule gas_bad_storage_at_counted_prefix >> metis_tac[])) >>
      `valid_horizon cx st0 (storage_trace_horizon es_end.storage_trace)
         es_end.storage_trace` by fs[storage_trace_domain_def]
      >- suspend "head_normal"
      >> suspend "head_exit") >>
  suspend "head_exempt"
QED

Resume abi_args_captured_cons_sim_live[head_normal]:
  qpat_x_assum `(\res ee t. _) _ _ _` (assume_tac o SIMP_RULE (srw_ss()) []) >>
  qpat_assum `!H. valid_horizon _ _ H es_end.storage_trace ==> ?tv v. _`
    (drule_then (qx_choosel_then [`tv`, `v`] strip_assume_tac)) >>
  qpat_x_assum `res = INL tv` SUBST_ALL_TAC >>
  qpat_x_assum `r = OK t` SUBST_ALL_TAC >>
  qpat_x_assum `!H. valid_horizon _ _ H es_end.storage_trace ==> ?tv v. _`
    (assume_tac o SIMP_RULE (srw_ss()) []) >>
  `?obs. es_end.storage_trace = es.storage_trace ++ obs` by
    (qpat_assum `gas_marked_exec _ _ (eval_expr cx e) (es, s0) _ _ _ _`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [gasSummaryTheory.gas_marked_exec_def]) >>
     disch_then (qspec_then `[]` assume_tac) >>
     qpat_assum `storage_trace_frame (eval_expr cx e)`
       (fn th => drule (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                                   storage_trace_frame_prefix) th)) >>
     simp[]) >>
  `!H. valid_horizon cx st0 H es_end.storage_trace ==>
       valid_horizon cx st0 H es.storage_trace` by
    simp[valid_horizon_def] >>
  qpat_x_assum `es_end.storage_trace = _` kall_tac >>
  `!H. valid_horizon cx st0 H es_end.storage_trace ==>
     vv_post H ctx func ce cx e es sa mid s0 (es_end with gas_obs := []) tv vv t` by
    metis_tac[] >>
  `stmt_state_rel (storage_trace_horizon es_end.storage_trace)
     ctx func ce cx es s0` by metis_tac[] >>
  `!tail. read_result cx tv (es_end with gas_obs := tail) =
      (INL v,es_end with gas_obs := tail)` by
    (drule exprSimMemorySourceTheory.read_result_gas_obs >> simp[]) >>
  `gas_marked_exec F (ctx,func)
     (bind (eval_expr cx e) (read_result cx)) (es,s0) marks (INL v) es_end (OK t)` by
    (irule exprSimBopRestWordComposeTheory.rest_word_marked_read >> metis_tac[]) >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v,es_end with gas_obs := [])` by
    (qpat_assum `gas_marked_exec _ _ (bind _ _) _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gasSummaryTheory.gas_marked_exec_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  qpat_assum `!gs v es1. _ ==> MAP FDOM _ = MAP FDOM _ /\ _` drule >> strip_tac >>
  `~t.vs_halted` by
    metis_tac[gasSummaryTheory.gas_marked_exec_def,
      fragGasModeTheory.gas_marked_path_exec, fragGasPathTheory.gas_path_normal] >>
  `sa.cs_next_var <= mid.cs_next_var /\ sa.cs_next_id <= mid.cs_next_id` by
    gvs[exprLoweringPropsTheory.ci_mono_def] >>
  `type_memory_size tv' < 2 ** 64` by simp[] >>
  `!tvt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tvt /\
          ~is_word_type (post_value_type ce e) ==>
       type_memory_bytes ce (post_value_type ce e) = type_memory_size tvt /\
       type_memory_size tvt < 2 ** 64` by
    metis_tac[materialize_captured_post_copy_ok] >>
  drule_all (Q.INST [`HP` |-> `\H. valid_horizon cx st0 H es_end.storage_trace`]
               compile_materialize_vv_owned_path |> BETA_RULE) >>
  strip_tac >>
  `gas_marked_exec F (ctx,func)
     (bind (eval_expr cx e) (read_result cx)) (es,s0) marks (INL v) es_end (OK t')` by
    (qpat_assum `gas_marked_exec _ _ (bind _ _) _ _ _ _ _` mp_tac >>
     rewrite_tac[gasSummaryTheory.gas_marked_exec_def] >> strip_tac >> simp[] >>
     qpat_assum `gas_marked_path _ _ _ s0 _ _`
       (mp_then Any mp_tac fragGasModeTheory.gas_marked_path_then) >>
     disch_then drule >> simp[]) >>
  `!H. valid_horizon cx st0 H es_end.storage_trace ==>
     stmt_state_rel H ctx func ce cx (es_end with gas_obs := []) t' /\
     storage_well_formed_on cx (es_end with gas_obs := []) (FST H)` by
    (rpt strip_tac >>
     qpat_x_assum `!H. valid_horizon _ _ H _ ==> materialize_owned_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (drule_then mp_tac) >>
     qpat_x_assum `!H. valid_horizon _ _ H _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (drule_then mp_tac) >>
     simp[materialize_owned_post_def, loweringPostsTheory.vv_post_def]) >>
  qpat_x_assum `!gs v es1 t. _`
    (qspecl_then [`gas_explicit marks s0.vs_gas_readings`, `v`,
                  `es_end with gas_obs := []`, `t'`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks ++ marks'` >> disj1_tac >>
      rewrite_tac[eval_exprs_cons_action] >>
      irule gas_bad_storage_at_bind_right >>
      qpat_assum `gas_marked_exec _ _ (bind _ _) (es, s0) _ _ _ (OK t')`
        (irule_at Any) >>
      simp[] >> irule gas_bad_storage_at_bind_left >>
      simp[storage_trace_frame_return])
  >- (qpat_x_assum `gas_summary_at _ _ _ (eval_exprs _ _) _ _ _`
        (strip_assume_tac o REWRITE_RULE [gasSummaryTheory.gas_summary_at_def]) >>
      (reverse (Cases_on `storage_trace_domain cx st0 es_end'.storage_trace`)
       >- (qexists_tac `marks ++ marks'` >> disj1_tac >>
           rewrite_tac[eval_exprs_cons_action] >>
           irule gas_bad_storage_at_bind_right >>
           qpat_assum `gas_marked_exec _ _ (bind _ _) (es, s0) _ _ _ (OK t')`
             (irule_at Any) >>
           simp[] >> irule gas_bad_storage_at_bind_left >>
           simp[storage_trace_frame_return] >>
           irule gas_bad_storage_at_counted_prefix >> metis_tac[])) >>
      `valid_horizon cx st0 (storage_trace_horizon es_end'.storage_trace)
         es_end'.storage_trace` by fs[storage_trace_domain_def]
      >- suspend "tail_normal"
      >> suspend "tail_exit") >>
  suspend "tail_exempt"
QED
Resume abi_args_captured_cons_sim_live[head_exit]:
  qpat_x_assum `(\res ee r. _) _ _ _` (assume_tac o SIMP_RULE (srw_ss()) []) >>
  `expr_exit res r` by metis_tac[] >>
  Cases_on `res` >- gvs[] >>
  rename1 `gas_marked_exec _ _ _ _ _ (INR exc) _ _` >>
  qexists_tac `marks` >> disj2_tac >> disj1_tac >>
  simp[gasSummaryTheory.gas_summary_at_def] >>
  qexistsl_tac [`INR exc`, `es_end`, `r`] >> conj_tac
  >- (rewrite_tac[eval_exprs_cons_action] >>
      irule gasSummaryComposeTheory.gas_marked_exec_bind_exception >>
      irule gasSummaryComposeTheory.gas_marked_exec_bind_exception >>
      first_assum ACCEPT_TAC) >>
  disj2_tac >> simp[wb_args_exit_def] >>
  qpat_x_assum `expr_exit _ _` mp_tac >>
  simp[stmtSimPropsTheory.expr_exit_INR_type]
QED
Resume abi_args_captured_cons_sim_live[head_exempt]:
  qexists_tac `marks` >> disj2_tac >> disj2_tac >>
  rewrite_tac[eval_exprs_cons_ignore_action, vyperStateTheory.bind_assoc] >>
  irule_at Any gasExemptCertTheory.gas_exempt_cert_error_result >>
  goal_assum (drule_at Any)
QED
Resume abi_args_captured_cons_sim_live[tail_normal]:
  qpat_x_assum `(\res ee t. _) _ _ _` (assume_tac o SIMP_RULE (srw_ss()) []) >>
  qpat_assum `!H. valid_horizon _ _ H es_end'.storage_trace ==> ?vs. _`
    (drule_then (qx_choose_then `vs` strip_assume_tac)) >>
  qpat_x_assum `res = INL vs` SUBST_ALL_TAC >>
  qpat_x_assum `!H. valid_horizon _ _ H es_end'.storage_trace ==> ?vs. _`
    (assume_tac o SIMP_RULE (srw_ss()) []) >>
  `?obs'. es_end'.storage_trace = es_end.storage_trace ++ obs'` by
    (qpat_assum `gas_marked_exec _ _ (eval_exprs _ _) _ _ _ _ _`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [gasSummaryTheory.gas_marked_exec_def]) >>
     disch_then (qspec_then `[]` assume_tac) >>
     qpat_assum `storage_trace_frame (eval_exprs _ _)`
       (fn th => drule (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                                   storage_trace_frame_prefix) th)) >>
     simp[]) >>
  `!H. valid_horizon cx st0 H es_end'.storage_trace ==>
       valid_horizon cx st0 H es_end.storage_trace` by
    simp[valid_horizon_def] >>
  qpat_x_assum `es_end'.storage_trace = _` kall_tac >>
  qexists_tac `marks ++ marks'` >> disj2_tac >> disj1_tac >>
  simp[gasSummaryTheory.gas_summary_at_def] >>
  qexistsl_tac [`INL (v::vs)`, `es_end'`, `OK t''`] >> conj_tac
  >- (rewrite_tac[eval_exprs_cons_action] >>
      irule gasSummaryComposeTheory.gas_marked_exec_bind_normal >>
      qpat_assum `gas_marked_exec _ _ (bind _ _) _ _ (INL v) _ (OK t')` (irule_at Any) >>
      BETA_TAC >>
      qpat_assum `gas_marked_exec _ _ _ _ _ (INL vs) _ _`
        (mp_tac o MATCH_MP gas_marked_exec_cons_values) >> simp[]) >>
  disj1_tac >> simp[] >> gen_tac >> strip_tac >>
  `valid_horizon cx st0 H es_end.storage_trace` by metis_tac[] >>
  `valid_horizon cx st0 H es.storage_trace` by metis_tac[] >>
  qpat_assum `!H. valid_horizon _ _ H es_end'.storage_trace ==>
                  abi_args_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> materialize_owned_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (drule_then assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  conj_tac
  >- suspend "post" >>
  conj_tac >- suspend "frame" >>
  irule abi_decoder_operand_live_mono >> qexists_tac `sm.cs_next_var` >>
  conj_tac >- gvs[exprLoweringPropsTheory.ci_mono_def] >>
  Cases_on `op` >>
  gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
      loweringStateRelDefsTheory.not_fresh_at_def]
QED
Resume abi_args_captured_cons_sim_live[post]:
  irule captured_owned_cons_post >>
  qpat_assum `materialize_owned_post H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `abi_args_post H _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> reverse conj_tac
  >- (gvs[exprLoweringPropsTheory.ci_mono_def] >> metis_tac[compileEnvTheory.cs_extends_trans]) >>
  qpat_x_assum `gas_marked_exec _ _ (eval_exprs cx args) _ _ _ _ _`
    (mp_tac o REWRITE_RULE [gasSummaryTheory.gas_marked_exec_def]) >>
  strip_tac >> first_x_assum (qspec_then `[]` assume_tac) >>
  qpat_x_assum `!gs v es1 gs' rr ee. _` drule >>
  simp[] >> strip_tac >> gvs[] >>
  first_x_assum drule >> simp[]
QED
Resume abi_args_captured_cons_sim_live[tail_exit]:
  qpat_x_assum `(\res ee r. _) _ _ _` (assume_tac o SIMP_RULE (srw_ss()) []) >>
  `wb_args_exit res r` by metis_tac[] >>
  Cases_on `res` >- gvs[wb_args_exit_def] >>
  rename1 `gas_marked_exec _ _ _ _ _ (INR exc) _ _` >>
  qexists_tac `marks ++ marks'` >> disj2_tac >> disj1_tac >>
  simp[gasSummaryTheory.gas_summary_at_def] >>
  qexistsl_tac [`INR exc`, `es_end'`, `r`] >> conj_tac
  >- (rewrite_tac[eval_exprs_cons_action] >>
      irule gasSummaryComposeTheory.gas_marked_exec_bind_normal >>
      qpat_assum `gas_marked_exec _ _ (bind _ _) _ _ (INL v) _ (OK t')` (irule_at Any) >>
      BETA_TAC >> irule gasSummaryComposeTheory.gas_marked_exec_bind_exception >> first_assum ACCEPT_TAC) >>
  disj2_tac >> gvs[wb_args_exit_def]
QED
Resume abi_args_captured_cons_sim_live[tail_exempt]:
  qexists_tac `marks ++ marks'` >> disj2_tac >> disj2_tac >>
  irule_at Any wb_args_tail_exempt_cert >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any)
QED
Resume abi_args_captured_cons_sim_live[frame]:
  rpt strip_tac >>
  qpat_assum `materialize_owned_post H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [materialize_owned_post_def]) >>
  `pure_frame ce func es_end sm t' t''` by
    (qpat_x_assum `EVERY _ args ==> pure_frame _ _ _ _ _ _` irule >>
     first_assum ACCEPT_TAC) >>
  match_mp_tac (Q.SPECL [`ce`, `func`, `es`, `es_end`, `sa`, `sm`, `s0`, `t'`, `t''`]
    exprSimPropsTheory.pure_frame_trans) >>
  rpt conj_tac
  >- (qpat_x_assum `~expr_has_effect e ==> _` irule >> first_assum ACCEPT_TAC)
  >- first_assum ACCEPT_TAC
  >- (fs[exprLoweringPropsTheory.ci_mono_def] >> decide_tac)
  >- fs[abi_args_post_def, loweringPostsTheory.wb_frame_def]
  >- first_assum ACCEPT_TAC
  >- fs[]
  >> fs[loweringPostsTheory.wb_frame_def]
QED
Finalise abi_args_captured_cons_sim_live
