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

Theorem captured_owned_cons_post:
  materialize_owned_post ctx func ce cx e es sa mid sm s0 es1 v op tv t /\
  abi_args_post ctx func ce cx es1 sm sb t es' args ops vs u /\
  stmt_state_rel ctx func ce cx es s0 /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  MAP FDOM es'.scopes = MAP FDOM es1.scopes /\
  ci_mono sa sm /\ ci_mono sm sb /\
  (!x. op = Var x ==> not_fresh_at sm x) /\ (!l. op <> Label l) /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\ val_wf tv v ==>
  abi_args_post ctx func ce cx es sa sb s0 es' (e::args) (op::ops) (v::vs) u
Proof
  strip_tac >>
  qpat_x_assum `materialize_owned_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
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
    (irule wb_frame_trans >> simp[] >> conj_tac
     >- (qexistsl_tac [`ctx`, `cx`, `func`] >> simp[]) >>
     qexistsl_tac [`es1`, `sm`, `t`] >>
     gvs[exprLoweringPropsTheory.ci_mono_def]) >>
  rewrite_tac[abi_args_post_cons] >> simp[] >>
  qpat_x_assum `abi_args_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
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
  stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
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
     stmt_state_rel ctx func ce cx es1 t /\ ~t.vs_halted /\
     t.vs_current_bb = sm.cs_current_bb /\
     t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
     gas_outcome F (cx_tops cx) (ctx,func) (eval_exprs cx args) (es1,t)
       (\rr ee u. ?vs. rr = INL vs /\
          abi_args_post ctx func ce cx es1 sm sb t ee args ops vs u /\
          u.vs_current_bb = sb.cs_current_bb /\
          u.vs_inst_idx = LENGTH sb.cs_current_insts)
       (\rr ee r. wb_args_exit rr r)) ==>
  gas_outcome F (cx_tops cx) (ctx,func) (eval_exprs cx (e::args)) (es,s0)
    (\rr ee u. ?vs. rr = INL vs /\
       abi_args_post ctx func ce cx es sa sb s0 ee (e::args) (op::ops) vs u /\
       u.vs_current_bb = sb.cs_current_bb /\
       u.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\rr ee r. wb_args_exit rr r)
Proof
  strip_tac >> drule_all abi_args_vv_error_prefix >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >> strip_tac
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gasSummaryTheory.gas_summary_at_def])
      >- suspend "head_normal"
      >> suspend "head_exit") >>
  suspend "head_exempt"
QED

Resume abi_args_captured_cons_sim[head_normal]:
  qpat_x_assum `(\rr ee t. _) _ _ _` (strip_assume_tac o BETA_RULE) >>
  gnvs[] >>
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
  drule_all compile_materialize_vv_owned_path >> strip_tac >>
  `gas_marked_exec F (ctx,func)
     (bind (eval_expr cx e) (read_result cx)) (es,s0) marks (INL v) es_end (OK t')` by
    (qpat_assum `gas_marked_exec _ _ (bind _ _) _ _ _ _ _` mp_tac >>
     rewrite_tac[gasSummaryTheory.gas_marked_exec_def] >> strip_tac >> simp[] >>
     qpat_assum `gas_marked_path _ _ _ s0 _ _`
       (mp_then Any mp_tac fragGasModeTheory.gas_marked_path_then) >>
     disch_then drule >> simp[]) >>
  `stmt_state_rel ctx func ce cx (es_end with gas_obs := []) t'` by
    gvs[materialize_owned_post_def] >>
  qpat_x_assum `!gs v es1 t. _` (drule_all_then mp_tac) >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >> strip_tac
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gasSummaryTheory.gas_summary_at_def])
      >- suspend "tail_normal"
      >> suspend "tail_exit") >>
  suspend "tail_exempt"
QED
Resume abi_args_captured_cons_sim[head_exit]:
  BETA_TAC >> Cases_on `res` >- gvs[] >>
  rename1 `gas_marked_exec _ _ _ _ _ (INR exc) _ _` >>
  qexists_tac `marks` >> disj1_tac >>
  simp[gasSummaryTheory.gas_summary_at_def] >>
  qexistsl_tac [`INR exc`, `es_end`, `r`] >> conj_tac
  >- (rewrite_tac[eval_exprs_cons_action] >>
      irule gasSummaryComposeTheory.gas_marked_exec_bind_exception >>
      irule gasSummaryComposeTheory.gas_marked_exec_bind_exception >>
      first_assum ACCEPT_TAC) >>
  disj2_tac >> simp[wb_args_exit_def] >>
  qpat_x_assum `(\rr ee r. _) _ _ _` (mp_tac o BETA_RULE) >>
  simp[stmtSimPropsTheory.expr_exit_INR_type]
QED
Resume abi_args_captured_cons_sim[head_exempt]:
  qexists_tac `marks` >> disj2_tac >>
  rewrite_tac[eval_exprs_cons_ignore_action, vyperStateTheory.bind_assoc] >>
  irule_at Any gasExemptCertTheory.gas_exempt_cert_error_result >>
  goal_assum (drule_at Any)
QED
Resume abi_args_captured_cons_sim[tail_normal]:
  qpat_x_assum `(\rr ee t. _) _ _ _` (strip_assume_tac o BETA_RULE) >>
  gnvs[] >>
  qexists_tac `marks ++ marks'` >> disj1_tac >>
  simp[gasSummaryTheory.gas_summary_at_def] >>
  qexistsl_tac [`INL (v::vs)`, `es_end'`, `OK t''`] >> conj_tac
  >- (rewrite_tac[eval_exprs_cons_action] >>
      irule gasSummaryComposeTheory.gas_marked_exec_bind_normal >>
      qpat_assum `gas_marked_exec _ _ (bind _ _) _ _ (INL v) _ (OK t')` (irule_at Any) >>
      BETA_TAC >>
      qpat_assum `gas_marked_exec _ _ _ _ _ (INL vs) _ _`
        (mp_tac o MATCH_MP gas_marked_exec_cons_values) >> simp[]) >>
  disj1_tac >> simp[] >>
  irule captured_owned_cons_post >>
  qpat_assum `materialize_owned_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `abi_args_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
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
  Cases_on `res` >- gvs[wb_args_exit_def] >>
  rename1 `gas_marked_exec _ _ _ _ _ (INR exc) _ _` >>
  qexists_tac `marks ++ marks'` >> disj1_tac >>
  simp[gasSummaryTheory.gas_summary_at_def] >>
  qexistsl_tac [`INR exc`, `es_end'`, `r`] >> conj_tac
  >- (rewrite_tac[eval_exprs_cons_action] >>
      irule gasSummaryComposeTheory.gas_marked_exec_bind_normal >>
      qpat_assum `gas_marked_exec _ _ (bind _ _) _ _ (INL v) _ (OK t')` (irule_at Any) >>
      BETA_TAC >> irule gasSummaryComposeTheory.gas_marked_exec_bind_exception >> first_assum ACCEPT_TAC) >>
  disj2_tac >> gvs[wb_args_exit_def]
QED
Resume abi_args_captured_cons_sim[tail_exempt]:
  qexists_tac `marks ++ marks'` >> disj2_tac >>
  irule_at Any wb_args_tail_exempt_cert >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any)
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
  stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
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
     stmt_state_rel ctx func ce cx es1 t /\ ~t.vs_halted /\
     t.vs_current_bb = sm.cs_current_bb /\
     t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
     gas_outcome F (cx_tops cx) (ctx,func) (eval_exprs cx args) (es1,t)
       (\rr ee u. ?vs. rr = INL vs /\
          abi_args_post ctx func ce cx es1 sm sb t ee args ops vs u /\
          EVERY (abi_decoder_operand_live sb.cs_next_var) ops /\
          u.vs_current_bb = sb.cs_current_bb /\
          u.vs_inst_idx = LENGTH sb.cs_current_insts)
       (\rr ee r. wb_args_exit rr r)) ==>
  gas_outcome F (cx_tops cx) (ctx,func) (eval_exprs cx (e::args)) (es,s0)
    (\rr ee u. ?vs. rr = INL vs /\
       abi_args_post ctx func ce cx es sa sb s0 ee (e::args) (op::ops) vs u /\
       EVERY (abi_decoder_operand_live sb.cs_next_var) (op::ops) /\
       u.vs_current_bb = sb.cs_current_bb /\
       u.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\rr ee r. wb_args_exit rr r)
Proof
  strip_tac >> drule_all abi_args_vv_error_prefix >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >> strip_tac
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gasSummaryTheory.gas_summary_at_def])
      >- suspend "head_normal"
      >> suspend "head_exit") >>
  suspend "head_exempt"
QED

Resume abi_args_captured_cons_sim_live[head_normal]:
  qpat_x_assum `(\rr ee t. _) _ _ _` (strip_assume_tac o BETA_RULE) >>
  gnvs[] >>
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
  drule_all compile_materialize_vv_owned_path >> strip_tac >>
  `gas_marked_exec F (ctx,func)
     (bind (eval_expr cx e) (read_result cx)) (es,s0) marks (INL v) es_end (OK t')` by
    (qpat_assum `gas_marked_exec _ _ (bind _ _) _ _ _ _ _` mp_tac >>
     rewrite_tac[gasSummaryTheory.gas_marked_exec_def] >> strip_tac >> simp[] >>
     qpat_assum `gas_marked_path _ _ _ s0 _ _`
       (mp_then Any mp_tac fragGasModeTheory.gas_marked_path_then) >>
     disch_then drule >> simp[]) >>
  `stmt_state_rel ctx func ce cx (es_end with gas_obs := []) t'` by
    gvs[materialize_owned_post_def] >>
  qpat_x_assum `!gs v es1 t. _` (drule_all_then mp_tac) >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >> strip_tac
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gasSummaryTheory.gas_summary_at_def])
      >- suspend "tail_normal"
      >> suspend "tail_exit") >>
  suspend "tail_exempt"
QED
Resume abi_args_captured_cons_sim_live[head_exit]:
  BETA_TAC >> Cases_on `res` >- gvs[] >>
  rename1 `gas_marked_exec _ _ _ _ _ (INR exc) _ _` >>
  qexists_tac `marks` >> disj1_tac >>
  simp[gasSummaryTheory.gas_summary_at_def] >>
  qexistsl_tac [`INR exc`, `es_end`, `r`] >> conj_tac
  >- (rewrite_tac[eval_exprs_cons_action] >>
      irule gasSummaryComposeTheory.gas_marked_exec_bind_exception >>
      irule gasSummaryComposeTheory.gas_marked_exec_bind_exception >>
      first_assum ACCEPT_TAC) >>
  disj2_tac >> simp[wb_args_exit_def] >>
  qpat_x_assum `(\rr ee r. _) _ _ _` (mp_tac o BETA_RULE) >>
  simp[stmtSimPropsTheory.expr_exit_INR_type]
QED
Resume abi_args_captured_cons_sim_live[head_exempt]:
  qexists_tac `marks` >> disj2_tac >>
  rewrite_tac[eval_exprs_cons_ignore_action, vyperStateTheory.bind_assoc] >>
  irule_at Any gasExemptCertTheory.gas_exempt_cert_error_result >>
  goal_assum (drule_at Any)
QED
Resume abi_args_captured_cons_sim_live[tail_normal]:
  qpat_x_assum `(\rr ee t. _) _ _ _` (strip_assume_tac o BETA_RULE) >>
  gnvs[] >>
  qexists_tac `marks ++ marks'` >> disj1_tac >>
  simp[gasSummaryTheory.gas_summary_at_def] >>
  qexistsl_tac [`INL (v::vs)`, `es_end'`, `OK t''`] >> conj_tac
  >- (rewrite_tac[eval_exprs_cons_action] >>
      irule gasSummaryComposeTheory.gas_marked_exec_bind_normal >>
      qpat_assum `gas_marked_exec _ _ (bind _ _) _ _ (INL v) _ (OK t')` (irule_at Any) >>
      BETA_TAC >>
      qpat_assum `gas_marked_exec _ _ _ _ _ (INL vs) _ _`
        (mp_tac o MATCH_MP gas_marked_exec_cons_values) >> simp[]) >>
  disj1_tac >> simp[] >> conj_tac
  >- (irule captured_owned_cons_post >>
      qpat_assum `materialize_owned_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
      qpat_assum `abi_args_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
      simp[] >> reverse conj_tac
      >- (gvs[exprLoweringPropsTheory.ci_mono_def] >> metis_tac[compileEnvTheory.cs_extends_trans]) >>
      qpat_x_assum `gas_marked_exec _ _ (eval_exprs cx args) _ _ _ _ _`
        (mp_tac o REWRITE_RULE [gasSummaryTheory.gas_marked_exec_def]) >>
      strip_tac >> first_x_assum (qspec_then `[]` assume_tac) >>
      qpat_x_assum `!gs v es1 gs' rr ee. _` drule >>
      simp[] >> strip_tac >> gvs[] >> first_x_assum drule >> simp[]) >>
  irule abi_decoder_operand_live_mono >> qexists_tac `sm.cs_next_var` >>
  conj_tac >- gvs[exprLoweringPropsTheory.ci_mono_def] >>
  Cases_on `op` >>
  gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
      loweringStateRelDefsTheory.not_fresh_at_def]
QED
Resume abi_args_captured_cons_sim_live[tail_exit]:
  Cases_on `res` >- gvs[wb_args_exit_def] >>
  rename1 `gas_marked_exec _ _ _ _ _ (INR exc) _ _` >>
  qexists_tac `marks ++ marks'` >> disj1_tac >>
  simp[gasSummaryTheory.gas_summary_at_def] >>
  qexistsl_tac [`INR exc`, `es_end'`, `r`] >> conj_tac
  >- (rewrite_tac[eval_exprs_cons_action] >>
      irule gasSummaryComposeTheory.gas_marked_exec_bind_normal >>
      qpat_assum `gas_marked_exec _ _ (bind _ _) _ _ (INL v) _ (OK t')` (irule_at Any) >>
      BETA_TAC >> irule gasSummaryComposeTheory.gas_marked_exec_bind_exception >> first_assum ACCEPT_TAC) >>
  disj2_tac >> gvs[wb_args_exit_def]
QED
Resume abi_args_captured_cons_sim_live[tail_exempt]:
  qexists_tac `marks ++ marks'` >> disj2_tac >>
  irule_at Any wb_args_tail_exempt_cert >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any)
QED
Finalise abi_args_captured_cons_sim_live
