(* A common-endpoint accumulator for evaluated internal-call arguments. *)
Theory bodyIntCallHeldArgs
Ancestors
  bodyIntCallHeldFrame bodyIntCallSourceFrame bodyIntCallProducerInterface
  bodyIntCallArgType exprOperandVar exprSimSource loweringPosts pair
  exprSimCalldataSlice valueEncodingTyping list vyperState venomState
  compileEnv exprLoweringProps exprSimHypsDefs freshWrites context

Definition intcall_held_args_def:
  intcall_held_args ce cx a sm es s H <=>
    EVERY (\(ty,raw,vv).
      vv_holds ce cx ty raw vv es s /\
      vv_at ce cx ty a sm es raw vv s /\
      intcall_vv_provenance ce cx ty a sm es raw vv s /\
      vv_storage_live cx vv es s /\
      (!v tv. read_result cx raw es = (INL v,es) /\
              evaluate_type (get_tenv cx) ty = SOME tv ==>
              val_wf tv v /\ value_has_type tv v) /\
      (!x. vv_operand vv = Var x ==> not_fresh_at sm x)) H
End

Theorem intcall_held_args_nil[simp]:
  intcall_held_args ce cx a sm es s []
Proof
  simp[intcall_held_args_def]
QED

Theorem intcall_held_args_append[simp]:
  intcall_held_args ce cx a sm es s (H ++ hs) <=>
  intcall_held_args ce cx a sm es s H /\
  intcall_held_args ce cx a sm es s hs
Proof
  simp[intcall_held_args_def]
QED

Theorem intcall_held_args_member:
  intcall_held_args ce cx a sm es s H /\ MEM (ty,raw,vv) H ==>
  vv_holds ce cx ty raw vv es s /\
  vv_at ce cx ty a sm es raw vv s /\
  intcall_vv_provenance ce cx ty a sm es raw vv s /\
  vv_storage_live cx vv es s /\
  (!v tv. read_result cx raw es = (INL v,es) /\
          evaluate_type (get_tenv cx) ty = SOME tv ==>
          val_wf tv v /\ value_has_type tv v) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x)
Proof
  simp[intcall_held_args_def, EVERY_MEM] >> strip_tac >>
  first_x_assum (qspec_then `(ty,raw,vv)` mp_tac) >> simp[]
QED

Theorem intcall_held_args_outcomes[simp]:
  intcall_held_args ce cx a sm
    (es with <|outcomes := os; gas_obs := gs|>) s H <=>
  intcall_held_args ce cx a sm es s H
Proof
  simp[intcall_held_args_def, EVERY_MEM, FORALL_PROD,
       intcall_held_source_outcomes, read_result_outcomes_iff]
QED

Theorem intcall_held_args_singleton:
  expr_body_pre ce cx env e es /\ ~expr_has_effect e /\
  eval_expr cx e es = (INL raw,ee) /\
  compile_expr ce (expr_type e) e sm = (vv,sn) /\
  local_ptrs_reserved ce sm /\
  vv_post ctx func ce cx e es sm sn s ee raw vv t /\
  intcall_vv_provenance ce cx (expr_type e) sm sn ee raw vv t ==>
  intcall_held_args ce cx sm sn ee t [(expr_type e,raw,vv)]
Proof
  strip_tac >>
  drule_all exprSimSourceTheory.expr_body_pre_runtime_typed >> strip_tac >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sn x` by
    metis_tac[CONJUNCT1 compiler_compile_var] >>
  drule effect_free_post_value_type >> strip_tac >>
  gvs[intcall_held_args_def, vv_post_def] >>
  metis_tac[cj 1 value_has_type_val_wf]
QED

Theorem intcall_vv_provenance_start_mono:
  a.cs_next_id <= sm.cs_next_id /\
  intcall_vv_provenance ce cx ty sm sn es raw vv s ==>
  intcall_vv_provenance ce cx ty a sn es raw vv s
Proof
  simp[intcall_vv_provenance_def] >> strip_tac >>
  qx_gen_tac `op` >> disch_tac >>
  qpat_x_assum `!op. _` (qspec_then `op` mp_tac) >>
  simp[] >> disch_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac `w` >> simp[]
  >- (disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >>
      first_assum ACCEPT_TAC)
  >- (disj2_tac >> disj2_tac >> disj1_tac >>
      qexistsl_tac [`n`, `b`, `sz`] >> simp[]) >>
  disj2_tac >> disj2_tac >> disj2_tac >>
  rename1 `lookup_var rootp s = SOME rootw` >>
  qexistsl_tac [`n`, `sz`, `entry`, `rootp`, `rootw`, `k`] >> simp[]
QED

Theorem intcall_held_args_start_mono:
  a.cs_next_id <= sm.cs_next_id /\
  intcall_held_args ce cx sm sn es s H ==>
  intcall_held_args ce cx a sn es s H
Proof
  simp[intcall_held_args_def, EVERY_MEM, FORALL_PROD] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  simp[] >> metis_tac[vv_at_start_mono, intcall_vv_provenance_start_mono]
QED

Theorem intcall_held_args_gas_obs[simp]:
  intcall_held_args ce cx a sm (es with gas_obs := gs) s H <=>
  intcall_held_args ce cx a sm es s H
Proof
  qspec_then `es.outcomes` mp_tac
    (Q.GEN `os` intcall_held_args_outcomes) >>
  Cases_on `es` >>
  simp[Excl "intcall_held_args_outcomes",
       recordtype_evaluation_state_seldef_outcomes_fupd_def,
       recordtype_evaluation_state_seldef_gas_obs_fupd_def]
QED

Theorem intcall_held_operand_defined:
  vv_holds ce cx ty raw vv es s ==>
  ?w. eval_operand (vv_operand vv) s = SOME w
Proof
  Cases_on `vv` >>
  simp[vv_holds_def, vv_operand_def, expr_val_rel_def] >> metis_tac[]
QED

Theorem intcall_held_operand_frame:
  vv_holds ce cx ty raw vv es s /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  vv_post ctx func ce cx e es sm sn s ee r ev t /\
  t.vs_labels = s.vs_labels ==>
  eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s
Proof
  strip_tac >> drule intcall_held_operand_defined >> strip_tac >>
  Cases_on `vv_operand vv` >>
  gvs[venomStateTheory.eval_operand_def, vv_post_def] >> metis_tac[]
QED

Theorem intcall_held_args_transport:
  intcall_held_args ce cx a sm es s H /\
  expr_sim_inv ce cx env es /\ local_ptrs_reserved ce sm /\
  local_ptrs_rel func ce es.scopes s /\
  vv_post ctx func ce cx e es sm sn s ee r ev t /\
  ee = es with <|outcomes := ee.outcomes; gas_obs := ee.gas_obs|> /\
  ee.scopes = es.scopes /\ wb_frame ce es sm s t /\
  sm.cs_next_id <= sn.cs_next_id /\ sm.cs_next_var <= sn.cs_next_var /\
  t.vs_labels = s.vs_labels ==>
  intcall_held_args ce cx a sn ee t H
Proof
  strip_tac >>
  `stmt_state_rel ctx func ce cx ee t` by gvs[vv_post_def] >>
  simp[intcall_held_args_def, EVERY_MEM, FORALL_PROD] >>
  rpt gen_tac >> disch_tac >> rename1 `MEM (ty,raw,vv) H` >>
  drule_all intcall_held_args_member >> strip_tac >>
  `eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s` by
    (irule intcall_held_operand_frame >> metis_tac[]) >>
  drule_all intcall_held_updated_endpoint_outcomes >>
  disch_then (qspecl_then [`ee.outcomes`, `ee.gas_obs`] mp_tac) >>
  qpat_assum `ee = _` (fn th => once_rewrite_tac[GSYM th]) >>
  strip_tac >> simp[] >> conj_tac
  >- (qpat_x_assum `ee = _` SUBST1_TAC >>
      simp[read_result_outcomes_iff]) >>
  metis_tac[not_fresh_at_mono]
QED

Theorem intcall_held_args_extend:
  intcall_held_args ce cx a sm es s H /\
  a.cs_next_id <= sm.cs_next_id /\
  expr_body_pre ce cx env e es /\ ~expr_has_effect e /\
  eval_expr cx e es = (INL raw,ee) /\
  compile_expr ce (expr_type e) e sm = (vv,sn) /\
  local_ptrs_reserved ce sm /\ stmt_state_rel ctx func ce cx es s /\
  vv_post ctx func ce cx e es sm sn s ee raw vv t /\
  intcall_vv_provenance ce cx (expr_type e) sm sn ee raw vv t /\
  t.vs_labels = s.vs_labels ==>
  intcall_held_args ce cx a sn (ee with gas_obs := []) t
    (H ++ [(expr_type e,raw,vv)])
Proof
  strip_tac >> simp[] >> conj_tac
  >- (`ee = es with <|outcomes := ee.outcomes; gas_obs := ee.gas_obs|>` by
        metis_tac[effect_free_eval_expr_outcomes] >>
      `ee.scopes = es.scopes` by
        (qpat_x_assum `ee = _` SUBST1_TAC >> simp[]) >>
      `expr_sim_inv ce cx env es` by gvs[expr_body_pre_def] >>
      `local_ptrs_rel func ce es.scopes s` by
        gvs[stmt_state_rel_def, state_rel_def] >>
      `wb_frame ce es sm s t` by
        (gvs[wb_frame_def, vv_post_def] >> metis_tac[]) >>
      drule (CONJUNCT1 compile_expr_grows) >> strip_tac >>
      irule intcall_held_args_transport >> metis_tac[]) >>
  irule intcall_held_args_start_mono >>
  goal_assum (drule_at Any) >>
  irule intcall_held_args_singleton >> metis_tac[]
QED
