(* Word forcing keeps its memory resources at the semantic endpoint. *)
Theory extcallProtFrameTarget
Ancestors
  bodyIntCallForcingReadOnly exprSimUnwrapProps exprSimUnwrap
  exprExtRequestTargetCps exprExtRequestGasBind exprSimHyps
  exprLoweringProps loweringPosts fragGasMode vyperInterpreter vyperState
  compileEnv venomState finite_map exprLowering gasSummary exprSimMemorySource
  exprExtRequestKwargSuffix exprSimAggregateSource gasOutcome exprSimSource
  exprSimWordArgs valueEncodingTyping valueEncoding vyperValue vyperTyping
  pair exprSimHypsDefs exprSimDefs fragExec exprOperandVar stmtSimProps
  exprExtRequestHistory exprSafeOperand

Theorem word_unwrap_readonly_post:
  post_value_type ce e = expr_type e /\ is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  unwrap_value ce vv sm = (op,sb) /\
  read_result cx raw ee = (INL v,ee) /\
  vv_post ctx func ce cx e es sa sm s0 ee raw vv s /\
  local_ptrs_reserved ce sm /\ sa.cs_next_var <= sm.cs_next_var /\
  fn_has_code sm sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u. gas_marked_exec F (ctx,func) (read_result cx raw) (ee,s)
        [] (INL v) ee (OK u) /\
    expr_post ctx func ce cx e es sa sb s0 ee v op u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    u.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `vv_post ctx func ce cx e es sa sm s0 ee (Value v) vv s` by
    metis_tac[vv_post_read_result] >>
  Cases_on `vv`
  >- (gvs[unwrap_value_def, comp_return_def] >> qexists `s` >>
      simp[] >> conj_tac
      >- (simp[gas_marked_exec_def, gas_marked_path_def] >>
          metis_tac[read_result_gas_obs, fragGasPathTheory.gas_path_rules]) >>
      gvs[vv_post_def, vv_holds_def, vv_at_def, expr_post_def,
          read_result_def, return_def] >> metis_tac[]) >>
  rename1 `LocatedValue ann p` >>
  `vv_holds ce cx (expr_type e) (Value v) (LocatedValue ann p) ee s /\
   stmt_state_rel ctx func ce cx ee s` by gvs[vv_post_def] >>
  drule protected_word_value_forcing >>
  disch_then (drule_at (Pat `vv_holds _ _ _ _ _ _ _`)) >> simp[] >>
  disch_then (qspecl_then [`ee.scopes`, `\q. ?x. q = Var x /\ not_fresh_at sm x`, `func`, `ctx`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  `u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
   u.vs_alloca_next = s.vs_alloca_next` by
    (rpt conj_tac >> qpat_assum `u = _` (fn th => simp[Once th])) >>
  qexists `u` >> simp[] >> conj_tac
  >- (simp[gas_marked_exec_def] >> metis_tac[read_result_gas_obs]) >>
  irule expr_post_of_vv_post_load >>
  goal_assum (drule_at Any) >> simp[] >>
  conj_tac >- gvs[expr_val_rel_def] >>
  qexistsl [`p`, `s`, `sm`, `ann`] >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!q. _ ==> eval_operand q u = eval_operand q s`
    (qspec_then `Var x` mp_tac) >> simp[eval_operand_def]
QED

(* H is any resource property stable under the read-only forcing suffix.
   Its raw-step premise is discharged before the vv witness is forgotten. *)
Theorem extrequest_target_resource_counted_cps:
  expr_vv_case nocalls ctx func ce cx e /\
  expr_body_pre ce cx env e es /\ expr_type e = BaseT AddressT /\
  (nocalls ==> int_calls_expr e = []) /\
  lower_value compile_expr ce (BaseT AddressT) e sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!r vv sm ee t n.
    vv_post ctx func ce cx e es sa sm s0 ee r vv t /\
    gas_marked_path F ctx func s0 n (OK t) ==> H t) /\
  (!t u. H t /\ u.vs_memory = t.vs_memory /\
    u.vs_allocas = t.vs_allocas /\ u.vs_alloca_next = t.vs_alloca_next ==> H u) /\
  (!v ee t.
    expr_post ctx func ce cx e es sa sb s0 ee v op t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ee.gas_obs = [] /\
    (?used. !tail. bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := used ++ tail) = (INL v,ee with gas_obs := tail)) /\ H t ==>
    gas_outcome F (cx_tops cx) (ctx,func) (kont v) (ee,t) Q
      (\res ee r. expr_exit res r)) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (bind (eval_expr cx e) (read_result cx)) kont) (es,s0) Q
      (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `post_value_type ce e = expr_type e` by
    (irule post_value_type_word >> simp[is_word_type_def]) >>
  `?vv sm. compile_expr ce (expr_type e) e sa = (vv,sm) /\
    unwrap_value ce vv sm = (op,sb)` by
    (qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
     simp[lower_value_def, comp_bind_def] >>
     pairarg_tac >> simp[] >> metis_tac[pairTheory.PAIR]) >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[forced_expr_admissible_raw] >>
  `ci_mono sa sm` by
    (mp_tac (Q.SPECL [`ce`, `expr_type e`, `e`, `sa`]
      (cj 1 compile_expr_ci_mono)) >> simp[]) >>
  `ci_mono sm sb` by metis_tac[ci_mono_unwrap_value, SND] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (irule fn_has_code_split >> gvs[ci_mono_def]) >>
  `local_ptrs_reserved ce sm` by
    (drule_all compiler_ci_mono_reserved >> simp[]) >>
  `expr_vv_sim ctx func ce cx (expr_type e) e es` by
    (gvs[expr_vv_case_def] >> first_x_assum irule >> qexists `env` >> simp[]) >>
  `gas_outcome F (cx_tops cx) (ctx,func) (eval_expr cx e) (es,s0)
    (\res ee t. ?r. res = INL r /\
      vv_post ctx func ce cx e es sa sm s0 ee r vv t /\
      t.vs_current_bb = sm.cs_current_bb /\
      t.vs_inst_idx = LENGTH sm.cs_current_insts)
    (\res ee r. expr_exit res r)` by
    (gvs[expr_vv_sim_def] >> first_x_assum irule >> simp[]) >>
  rewrite_tac[bind_assoc] >>
  drule extrequest_outcome_bind_result >>
  disch_then (qspecl_then [`\r. bind (read_result cx r) kont`,
    `\res ee r. expr_exit res r`, `Q`] mp_tac) >> disch_then irule >>
  reverse conj_tac
  >- (rpt gen_tac >> Cases_on `rr` >> simp[expr_exit_INR_type]) >>
  rpt gen_tac >> strip_tac >> gvs[] >> suspend "raw_landing"
QED

Resume extrequest_target_resource_counted_cps[raw_landing]:
  `H t` by
    (qpat_x_assum `!r vv sm ee t n. _` irule >> conj_tac
     >- (qexists `LENGTH marks` >> gvs[gas_marked_exec_def]) >>
     goal_assum (drule_at Any)) >>
  `~t.vs_halted` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [gas_marked_exec_def, gas_marked_path_def]) >>
     drule fragGasPathTheory.gas_path_normal >> simp[]) >>
  drule vv_post_materialises >> strip_tac >>
  `?u. gas_marked_exec F (ctx,func) (read_result cx r)
      (mid with gas_obs := [],t) [] (INL v) (mid with gas_obs := []) (OK u) /\
    expr_post ctx func ce cx e es sa sb s0 (mid with gas_obs := []) v op u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    u.vs_memory = t.vs_memory /\ u.vs_allocas = t.vs_allocas /\
    u.vs_alloca_next = t.vs_alloca_next` by
    (irule word_unwrap_readonly_post >> simp[is_word_type_def, evaluate_type_def] >>
     qexistsl [`sm`, `vv`] >> gvs[ci_mono_def]) >>
  `H u` by metis_tac[] >>
  `?used. !tail. bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := used ++ tail) = (INL v,mid with gas_obs := tail)` by
    (qexists `gas_explicit marks s0.vs_gas_readings` >>
     gvs[gas_marked_exec_def] >> rpt gen_tac >>
     simp[vyperStateTheory.bind_def] >> metis_tac[]) >>
  irule extrequest_kwarg_suffix_cps >> simp[] >>
  qexistsl [`v`, `u`] >> simp[] >> first_x_assum irule >> simp[] >>
  qexists `used` >> simp[]
QED
Finalise extrequest_target_resource_counted_cps

Theorem extrequest_target_resource_cps:
  exprs_case nocalls ctx func ce cx [e] /\
  expr_body_pre ce cx env e es /\ expr_type e = BaseT AddressT /\
  (nocalls ==> int_calls_expr e = []) /\
  lower_value compile_expr ce (BaseT AddressT) e sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!r vv sm ee t n.
    vv_post ctx func ce cx e es sa sm s0 ee r vv t /\
    gas_marked_path F ctx func s0 n (OK t) ==> H t) /\
  (!t u. H t /\ u.vs_memory = t.vs_memory /\
    u.vs_allocas = t.vs_allocas /\ u.vs_alloca_next = t.vs_alloca_next ==> H u) /\
  (!v ee t target.
    expr_post ctx func ce cx e es sa sb s0 ee v op t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ee.gas_obs = [] /\
    (?used. !tail. bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := used ++ tail) = (INL v,ee with gas_obs := tail)) /\
    v = AddressV target /\ dest_AddressV v = SOME target /\
    eval_operand op t = SOME (w2w target) /\ safe_operand sb op /\
    stmt_state_rel ctx func ce cx ee t /\ wb_frame ce es sa s0 t /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
    local_ptrs_reserved ce sb /\
    extrequest_history_frame ce cx ee sb t ee sb t /\ H t ==>
    gas_outcome F (cx_tops cx) (ctx,func) (kont v) (ee,t) Q
      (\res ee r. expr_exit res r)) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (bind (eval_expr cx e) (read_result cx)) kont) (es,s0) Q
      (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `is_word_type (expr_type e)` by simp[is_word_type_def] >>
  drule_all expr_body_pre_lower_value_word_shape >> strip_tac >>
  `local_ptrs_reserved ce sb` by metis_tac[local_ptrs_reserved_next_var] >>
  irule extrequest_target_resource_counted_cps >>
  first_assum (irule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  first_assum (irule_at (Pat `expr_body_pre _ _ _ _ _`)) >>
  qexistsl [`nocalls`, `H`] >> simp[exprs_case_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac >- (conj_tac >- first_assum ACCEPT_TAC >> gvs[exprs_case_def]) >>
  rpt gen_tac >> strip_tac >>
  drule_all extrequest_target_address >> strip_tac >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     simp[] >> strip_tac >>
     `MAP FDOM (es with gas_obs := used).scopes =
      MAP FDOM (ee with gas_obs := []).scopes` suffices_by simp[] >>
     irule forced_eval_expr_preserves_scopes_dom >>
     qexistsl [`cx`, `e`, `INL v`] >> gvs[vyperStateTheory.bind_def]) >>
  first_x_assum irule >> goal_assum (drule_at Any) >>
  simp[extrequest_history_frame_refl] >> rpt conj_tac
  >- (qexists `used` >> gvs[])
  >- simp[dest_AddressV_def, byteTheory.word_of_bytes_be_def,
       byteTheory.word_of_bytes_word_to_bytes, dividesTheory.compute_divides,
       fcpLib.INDEX_CONV ``dimindex(:160)``]
  >- (gvs[safe_operand_def] >> metis_tac[]) >>
  metis_tac[expr_post_frame, expr_post_state]
QED
