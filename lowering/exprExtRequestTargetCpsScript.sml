Theory exprExtRequestTargetCps
Ancestors
  exprExtRequestGasBind exprSimHyps exprSimSource gasExemptCert gasSummary
  gasOutcome fragGasPath fragGasMode stmtSimProps exprSimDefs loweringPosts vyperInterpreter vyperState
  exprSimWordArgs exprExtRequestHistory vyperTypeExprSoundness valueEncoding
  valueEncodingTyping exprLoweringProps vyperValue vyperTyping compileEnv
  venomMemProps exprSafeOperand

Theorem extrequest_value_outcome_bind[local]:
  gas_outcome memory tops (ctx,func)
    (a : evaluation_state -> value evaluation_result) (es,s0) P E /\
  (!marks rr mid t.
    gas_marked_exec memory (ctx,func) a (es,s0) marks rr mid (OK t) /\
    P rr (mid with gas_obs := []) t ==>
    ?v. rr = INL v /\ gas_outcome memory tops (ctx,func) (k v)
      (mid with gas_obs := [],t) Q R) /\
  (!rr mid r. E rr mid r ==> ?exc. rr = INR exc /\ R (INR exc) mid r) ==>
  gas_outcome memory tops (ctx,func) (vyperState$bind a k) (es,s0) Q R
Proof
  strip_tac >> irule extrequest_outcome_bind_core >>
  conj_tac
  >- (simp[ignore_bind_def, bind_assoc] >> rpt strip_tac >>
      irule gas_exempt_cert_bind_value >> goal_assum (drule_at Any) >> simp[]) >>
  conj_tac
  >- (simp[ignore_bind_def, bind_assoc] >> rpt strip_tac >>
      irule gas_exempt_cert_error_value >> simp[ignore_bind_def]) >>
  qexistsl_tac [`E`, `P`] >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem extrequest_target_counted_cps:
  expr_sim_case nocalls ctx func cenv cx e /\
  expr_body_pre cenv cx env e es /\
  (nocalls ==> int_calls_expr e = []) /\
  lower_value compile_expr cenv (BaseT AddressT) e sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_admissible (vyperState$bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!v ee t.
    expr_post ctx func cenv cx e es sa sb s0 ee v op t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ee.gas_obs = [] /\
    (?used. !tail. bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := used ++ tail) = (INL v,ee with gas_obs := tail)) ==>
    gas_outcome F (cx_tops cx) (ctx,func) (kont v) (ee,t) Q
      (\res ee r. expr_exit res r)) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (vyperState$bind (vyperState$bind (eval_expr cx e) (read_result cx)) kont) (es,s0) Q
      (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `expr_sim ctx func cenv cx (BaseT AddressT) e es` by
    (drule_all expr_sim_case_apply >> simp[]) >>
  `gas_outcome F (cx_tops cx) (ctx,func)
    (vyperState$bind (eval_expr cx e) (read_result cx)) (es,s0)
    (\res ee t. ?v. res = INL v /\
      expr_post ctx func cenv cx e es sa sb s0 ee v op t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res ee r. expr_exit res r)` by
    (gvs[expr_sim_def] >> first_x_assum irule >> simp[]) >>
  irule extrequest_value_outcome_bind >> goal_assum (drule_at Any) >>
  reverse conj_tac
  >- (rpt gen_tac >> Cases_on `rr` >> simp[expr_exit_INR_type]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  `~t.vs_halted` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[NoAsms, gas_marked_exec_def, gas_marked_path_def] >>
     metis_tac[gas_path_normal]) >>
  first_x_assum irule >> simp[] >>
  qexists `gas_explicit marks s0.vs_gas_readings` >>
  gvs[gas_marked_exec_def]
QED

Theorem extrequest_target_address:
  expr_body_pre cenv cx env e es /\ expr_type e = BaseT AddressT /\
  expr_post ctx func cenv cx e es sa sb s0 ee v op t /\
  (!tail. vyperState$bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := used ++ tail) = (INL v,ee with gas_obs := tail)) ==>
  ?addr. v = AddressV addr /\ eval_operand op t = SOME (w2w addr)
Proof
  strip_tac >>
  `vyperState$bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := used) = (INL v,ee with gas_obs := [])` by
    (first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_body_pre cenv cx env e (es with gas_obs := used)` by simp[] >>
  `value_runtime_typed env (expr_type e) v` by
    (irule memory_rhs_read_annotation_typed >>
     qexistsl_tac [`cenv`, `cx`, `es with gas_obs := used`, `ee with gas_obs := []`] >>
     gvs[vyperStateTheory.bind_def, AllCaseEqs()]) >>
  gvs[value_runtime_typed_def, evaluate_type_def] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  gvs[expr_post_def, expr_val_rel_def, is_word_type_def,
      evaluate_type_def, typed_val_to_w256_def] >>
  qexists_tac `word_of_bytes_be l` >>
  `word_to_bytes (word_of_bytes_be l : address) T = l` by
    (simp[byteTheory.word_of_bytes_be_def] >>
     irule word_bytes_roundtrip >>
     simp[byteTheory.word_of_bytes_be_def, dividesTheory.divides_def,
       fcpLib.INDEX_CONV ``dimindex(:160)``]) >>
  simp[] >>
  qspec_then `l` mp_tac
    (w2w_word_of_bytes_be_pad_left
      |> INST_TYPE [alpha |-> ``:160``, beta |-> ``:256``]) >>
  simp[dividesTheory.compute_divides,
    fcpLib.INDEX_CONV ``dimindex(:160)``, EQ_SYM_EQ]
QED

Theorem extrequest_target_cps:
  expr_sim_case nocalls ctx func cenv cx e /\
  expr_body_pre cenv cx env e es /\ expr_type e = BaseT AddressT /\
  (nocalls ==> int_calls_expr e = []) /\
  lower_value compile_expr cenv (BaseT AddressT) e sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_admissible (vyperState$bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!v ee t target.
    expr_post ctx func cenv cx e es sa sb s0 ee v op t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ee.gas_obs = [] /\
    (?used. !tail. vyperState$bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := used ++ tail) = (INL v,ee with gas_obs := tail)) /\
    v = AddressV target /\ dest_AddressV v = SOME target /\
    eval_operand op t = SOME (w2w target) /\ safe_operand sb op /\
    stmt_state_rel ctx func cenv cx ee t /\ wb_frame cenv es ee sa s0 t /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
    local_ptrs_reserved cenv sb /\
    extrequest_history_frame cenv cx ee sb t ee sb t ==>
    gas_outcome F (cx_tops cx) (ctx,func) (kont v) (ee,t) Q
      (\res ee r. expr_exit res r)) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (vyperState$bind (vyperState$bind (eval_expr cx e) (read_result cx)) kont)
    (es,s0) Q (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `is_word_type (expr_type e)` by simp[is_word_type_def] >>
  drule_all expr_body_pre_lower_value_word_shape >> strip_tac >>
  `local_ptrs_reserved cenv sb` by metis_tac[local_ptrs_reserved_next_var] >>
  irule extrequest_target_counted_cps >>
  first_assum (irule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  first_assum (irule_at (Pat `expr_body_pre _ _ _ _ _`)) >>
  first_assum (irule_at (Pat `expr_sim_case _ _ _ _ _ _`)) >> simp[] >>
  rpt gen_tac >> strip_tac >>
  drule_all extrequest_target_address >> strip_tac >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (first_x_assum (qspec_then `[]` mp_tac) >> simp[] >>
     strip_tac >>
     `MAP FDOM (es with gas_obs := used).scopes =
      MAP FDOM (ee with gas_obs := []).scopes` suffices_by simp[] >>
     irule forced_eval_expr_preserves_scopes_dom >>
     qexistsl_tac [`cx`, `e`, `INL v`] >>
     gvs[vyperStateTheory.bind_def]) >>
  first_x_assum irule >> goal_assum (drule_at Any) >>
  simp[extrequest_history_frame_refl] >>
  rpt conj_tac
  >- (qexists_tac `used` >> gvs[])
  >- (simp[dest_AddressV_def, byteTheory.word_of_bytes_be_def,
       byteTheory.word_of_bytes_word_to_bytes, dividesTheory.compute_divides,
       fcpLib.INDEX_CONV ``dimindex(:160)``])
  >- (gvs[safe_operand_def] >> metis_tac[]) >>
  metis_tac[expr_post_frame, expr_post_state]
QED
