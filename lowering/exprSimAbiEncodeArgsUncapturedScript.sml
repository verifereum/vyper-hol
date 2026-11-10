(*
 * Expression simulation: one uncaptured abi_encode argument, counted.
 *
 * An argument compile_abi_encode_args leaves in place (a word, or a
 * composite no later argument can mutate) runs as lower_value; followed
 * by the counted run of the remaining arguments, the whole list runs as
 * eval_exprs on an actual counted path.
 *)

Theory exprSimAbiEncodeArgsUncaptured
Ancestors
  abiEncodeArgsSim exprSimHypsDefs exprSimWordArgs abiDecoderReentry
  exprSimAbiGasBridge exprSimExtract32Post stmtSimAugAssignAttr
  gasOutcome gasSummary gasSummaryCompose gasContext fragGasMode fragGasPath
  exprSimDefs exprSimSource exprLoweringProps vyperState loweringPosts compileEnv

(* Share the counted composition without requiring liveness from a non-live tail. *)
Theorem abi_args_uncaptured_cons_sim_counted[local]:
  expr_sim ctx func ce cx (expr_type e) e es /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  expr_body_pre ce cx env e es /\
  lower_value compile_expr ce (expr_type e) e sa = (op,sm) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!gs v es1.
     bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,es1) ==>
     expr_sim_inv ce cx env es1 /\
     (~is_word_type (expr_type e) ==>
      ?tv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
            value_has_type tv v /\ val_wf tv v /\
            type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
            type_memory_size tv < 2 ** 64 /\
            type_memory_size tv + 64 < dimword (:256))) /\
  (!gs v es1 gs' rr ee.
     bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,es1) /\
     eval_exprs cx args (es1 with gas_obs := gs') = (rr,ee) ==>
     MAP FDOM ee.scopes = MAP FDOM es1.scopes /\
     (~is_word_type (lowered_value_type ce e) ==> ee.scopes = es1.scopes)) /\
  ci_mono sa sm /\ ci_mono sm sb /\
  (!x. op = Var x ==> not_fresh_at sm x) /\
  (!gs v es1 t.
     bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,es1) /\
     stmt_state_rel ctx func ce cx es1 t /\ ~t.vs_halted /\
     t.vs_current_bb = sm.cs_current_bb /\
     t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
     gas_outcome F (cx_tops cx) (ctx,func) (eval_exprs cx args) (es1,t)
       (\rr ee u. ?vs. rr = INL vs /\
          abi_args_post ctx func ce cx es1 sm sb t ee args ops vs u /\
          (live ==> EVERY (abi_decoder_operand_live sb.cs_next_var) ops) /\
          u.vs_current_bb = sb.cs_current_bb /\
          u.vs_inst_idx = LENGTH sb.cs_current_insts)
       (\rr ee r. wb_args_exit rr r)) ==>
  gas_outcome F (cx_tops cx) (ctx,func) (eval_exprs cx (e::args)) (es,s0)
    (\rr ee u. ?vs. rr = INL vs /\
       abi_args_post ctx func ce cx es sa sb s0 ee (e::args) (op::ops) vs u /\
       (live ==> EVERY (abi_decoder_operand_live sb.cs_next_var) (op::ops)) /\
       u.vs_current_bb = sb.cs_current_bb /\
       u.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\rr ee r. wb_args_exit rr r)
Proof
  strip_tac >> drule_all expr_sim_apply >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def])
      >- suspend "head_normal"
      >> suspend "head_exit") >>
  suspend "head_exempt"
QED

Resume abi_args_uncaptured_cons_sim_counted[head_normal]:
  qpat_x_assum `(\rr ee t. _) _ _ _` (strip_assume_tac o BETA_RULE) >>
  gnvs[] >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v, es_end with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `stmt_state_rel ctx func ce cx (es_end with gas_obs := []) t` by
    metis_tac[expr_post_state] >>
  `~t.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  qpat_x_assum `!gs v es1 t. _` (drule_all_then mp_tac) >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def])
      >- suspend "tail_normal"
      >> suspend "tail_exit") >>
  suspend "tail_exempt"
QED
Resume abi_args_uncaptured_cons_sim_counted[head_exit]:
  Cases_on `res` >- gvs[expr_exit_def] >>
  qexists_tac `marks` >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INR y`, `es_end`, `r`] >> conj_tac
  >- (rewrite_tac[eval_exprs_cons_action] >>
      irule gas_marked_exec_bind_exception >> first_assum ACCEPT_TAC) >>
  disj2_tac >> gvs[wb_args_exit_def]
QED
Resume abi_args_uncaptured_cons_sim_counted[head_exempt]:
  qexists_tac `marks` >> disj2_tac >>
  irule_at Any wb_args_head_exempt_cert >> goal_assum (drule_at Any)
QED
Resume abi_args_uncaptured_cons_sim_counted[tail_normal]:
  qpat_x_assum `(\rr ee t. _) _ _ _` (strip_assume_tac o BETA_RULE) >>
  gnvs[] >>
  qexists_tac `marks ++ marks'` >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INL (v::vs)`, `es_end'`, `OK t'`] >> conj_tac
  >- (rewrite_tac[eval_exprs_cons_action] >>
      irule gas_marked_exec_bind_normal >>
      qpat_assum `gas_marked_exec _ _ _ _ _ (INL v) _ _` (irule_at Any) >>
      BETA_TAC >>
      qpat_assum `gas_marked_exec _ _ _ _ _ (INL vs) _ _`
        (mp_tac o MATCH_MP gas_marked_exec_cons_values) >> simp[]) >>
  disj1_tac >> simp[] >>
  conj_tac >- suspend "post" >>
  metis_tac[abi_args_operand_live]
QED
Resume abi_args_uncaptured_cons_sim_counted[tail_exit]:
  Cases_on `res` >- gvs[wb_args_exit_def] >>
  rename1 `gas_marked_exec _ _ _ _ _ (INR exc) _ _` >>
  qexists_tac `marks ++ marks'` >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INR exc`, `es_end'`, `r`] >> conj_tac
  >- (rewrite_tac[eval_exprs_cons_action] >>
      irule gas_marked_exec_bind_normal >>
      qpat_assum `gas_marked_exec _ _ _ _ _ (INL v) _ _` (irule_at Any) >>
      BETA_TAC >> irule gas_marked_exec_bind_exception >> first_assum ACCEPT_TAC) >>
  disj2_tac >> gvs[wb_args_exit_def]
QED
Resume abi_args_uncaptured_cons_sim_counted[tail_exempt]:
  qexists_tac `marks ++ marks'` >> disj2_tac >>
  irule_at Any wb_args_tail_exempt_cert >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any)
QED
Resume abi_args_uncaptured_cons_sim_counted[post]:
  qpat_assum `!gs v es1. _ ==> expr_sim_inv _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `(~is_word_type (expr_type e) ==>
    ?tv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
         value_has_type tv v /\ val_wf tv v)` by metis_tac[] >>
  `expr_val_rel cx (lowered_value_type ce e) v op t` by
    (irule abi_args_expr_post_lowered_rel >> metis_tac[]) >>
  `expr_val_at ce cx (lowered_value_type ce e) sa sm
     (es_end with gas_obs := []) v op t` by
    (irule abi_args_expr_post_lowered_at >> metis_tac[]) >>
  `eval_exprs cx args
     ((es_end with gas_obs := []) with gas_obs :=
       gas_explicit marks' t.vs_gas_readings) =
     (INL vs, es_end' with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ (eval_exprs _ _) _ _ _ _ _` mp_tac >>
     rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  qpat_x_assum `!gs v es1 gs' rr ee. _` (drule_all_then strip_assume_tac) >>
  `MAP FDOM es.scopes = MAP FDOM (es_end with gas_obs := []).scopes` by
    (drule (CONV_RULE (DEPTH_CONV ETA_CONV)
       forced_eval_expr_preserves_scopes_dom) >> simp[]) >>
  `expr_sim ctx func ce cx (expr_type e) e
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
    metis_tac[expr_sim_start_gas_obs] >>
  qsuff_tac `abi_args_post ctx func ce cx
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)
     sa sb s0 (es_end' with gas_obs := []) (e::args) (op::ops) (v::vs) t'`
  >- (simp[NoAsms, abi_args_post_def, wb_frame_def, locals_kept_def, popped_kept_def] >>
      metis_tac[]) >>
  irule (CONV_RULE (DEPTH_CONV ETA_CONV)
    abi_args_post_cons_uncaptured_labels) >>
  simp[ETA_THM, extract32_expr_post_start_gas_obs] >>
  qexistsl_tac [`env`, `t`] >>
  simp[extract32_expr_post_start_gas_obs, ci_mono_def] >>
  gvs[ci_mono_def]
QED
Finalise abi_args_uncaptured_cons_sim_counted

Theorem abi_args_uncaptured_cons_sim:
  expr_sim ctx func ce cx (expr_type e) e es /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  expr_body_pre ce cx env e es /\
  lower_value compile_expr ce (expr_type e) e sa = (op,sm) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!gs v es1.
     bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,es1) ==>
     expr_sim_inv ce cx env es1 /\
     (~is_word_type (expr_type e) ==>
      ?tv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
            value_has_type tv v /\ val_wf tv v /\
            type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
            type_memory_size tv < 2 ** 64 /\
            type_memory_size tv + 64 < dimword (:256))) /\
  (!gs v es1 gs' rr ee.
     bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,es1) /\
     eval_exprs cx args (es1 with gas_obs := gs') = (rr,ee) ==>
     MAP FDOM ee.scopes = MAP FDOM es1.scopes /\
     (~is_word_type (lowered_value_type ce e) ==> ee.scopes = es1.scopes)) /\
  ci_mono sa sm /\ ci_mono sm sb /\
  (!x. op = Var x ==> not_fresh_at sm x) /\
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
  mp_tac (Q.INST [`live` |-> `F`] abi_args_uncaptured_cons_sim_counted) >>
  simp[]
QED

Theorem abi_args_uncaptured_cons_sim_live:
  expr_sim ctx func ce cx (expr_type e) e es /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  expr_body_pre ce cx env e es /\
  lower_value compile_expr ce (expr_type e) e sa = (op,sm) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!gs v es1.
     bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,es1) ==>
     expr_sim_inv ce cx env es1 /\
     (~is_word_type (expr_type e) ==>
      ?tv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
            value_has_type tv v /\ val_wf tv v /\
            type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
            type_memory_size tv < 2 ** 64 /\
            type_memory_size tv + 64 < dimword (:256))) /\
  (!gs v es1 gs' rr ee.
     bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,es1) /\
     eval_exprs cx args (es1 with gas_obs := gs') = (rr,ee) ==>
     MAP FDOM ee.scopes = MAP FDOM es1.scopes /\
     (~is_word_type (lowered_value_type ce e) ==> ee.scopes = es1.scopes)) /\
  ci_mono sa sm /\ ci_mono sm sb /\
  (!x. op = Var x ==> not_fresh_at sm x) /\
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
  mp_tac (Q.INST [`live` |-> `T`] abi_args_uncaptured_cons_sim_counted) >>
  simp[]
QED
