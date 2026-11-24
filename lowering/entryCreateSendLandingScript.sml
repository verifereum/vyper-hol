(* Read the Send transfer inputs from the selected normal argument landing. *)
Theory entryCreateSendLanding
Ancestors
  exprSimSend exprSimPrecompiles exprSimWordArgs exprSimHypsDefs
  bodyPtrDefs allocaHistory vyperStorageFootprint vyperTypeExtCallCore
  vyperValue vyperInterpreter vyperState venomExecSemantics venomState list

Theorem send_args_source_inv[local]:
  !args es vs ee.
    (!e s. MEM e args /\ expr_sim_inv cenv cx env s ==>
      expr_body_pre cenv cx env e s /\ is_word_type (expr_type e)) /\
    expr_sim_inv cenv cx env es /\ eval_exprs cx args es = (INL vs,ee) ==>
    expr_sim_inv cenv cx env ee
Proof
  Induct >- simp[eval_exprs_nil] >> rpt gen_tac >> strip_tac >>
  drule eval_exprs_cons_cases >> strip_tac >> gvs[AllCaseEqs()] >>
  `expr_body_pre cenv cx env h es /\ is_word_type (expr_type h)` by
    (first_x_assum irule >> simp[]) >>
  drule_all expr_body_pre_stack_result >> strip_tac >>
  metis_tac[]
QED

Theorem send_landing_gas_obs[local]:
  (storage_well_formed_on cx (mid with gas_obs := gs) R <=>
    storage_well_formed_on cx mid R) /\
  (ghost_inv_at D lo d cenv cx (mid with gas_obs := gs) G tn t <=>
    ghost_inv_at D lo d cenv cx mid G tn t)
Proof
  conj_tac >- (irule storage_well_formed_on_backends >> simp[]) >>
  simp[ghost_inv_at_def]
QED

Theorem send_typed_args_tail_ready:
  expr_body_pre cenv cx env (Call ann (Send has_gas) args dflt) es /\
  (~has_gas ==> gas = Lit 0w) /\
  (!tail. eval_exprs cx args (es with gas_obs := readings ++ tail) =
      (INL vs,mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\ ~t.vs_halted /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    typed_args_post H ctx func cenv cx es sa s0 mid args
      ([addr;value] ++ (if has_gas then [gas] else [])) vs t /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx mid G tn t /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
    EVERY (\x. op_taint tn x = {}) ([addr;value] ++ (if has_gas then [gas] else []))) ==>
  let es1 = mid with gas_obs := [] in
    outcomes_accounts_typed es1.outcomes /\ accounts_runtime_well_typed es1.accounts /\
    wb_frame cenv es es1 sa s0 t /\ ~t.vs_halted /\
    t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
    (!H. valid_horizon cx st0 H es1.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es1 t /\
      storage_well_formed_on cx es1 (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx es1 G tn t) /\
    ?to_v amount_v gas_vs gw aw vw.
      vs = to_v::amount_v::gas_vs /\
      LENGTH gas_vs = (if has_gas then 1 else 0) /\
      op_taint tn gas = {} /\ op_taint tn addr = {} /\ op_taint tn value = {} /\
      eval_operand gas t = SOME gw /\
      w2n gw = (case OPTION_BIND (ext_call_kwarg EKGas [EKGas] gas_vs) dest_NumV of
                 NONE => 0 | SOME g => g) /\
      eval_operand addr t = SOME aw /\ dest_AddressV to_v = SOME (w2w aw) /\
      eval_operand value t = SOME vw /\ dest_NumV amount_v = SOME (w2n vw)
Proof
  simp[] >> strip_tac >> drule send_pre_types >> strip_tac >>
  `!e s. MEM e args /\ expr_sim_inv cenv cx env s ==>
     expr_body_pre cenv cx env e s /\ is_word_type (expr_type e)` by
    (rpt strip_tac >- metis_tac[expr_body_pre_send_arg] >> fs[EVERY_MEM]) >>
  `expr_sim_inv cenv cx env (es with gas_obs := readings)` by fs[expr_body_pre_def] >>
  qpat_assum `!tail. eval_exprs _ _ _ = _`
    (qspec_then `[]` (assume_tac o REWRITE_RULE[APPEND_NIL])) >>
  `expr_sim_inv cenv cx env (mid with gas_obs := [])` by
    (irule send_args_source_inv >> goal_assum (drule_at Any) >> simp[] >>
     rpt strip_tac >>
     qpat_assum `!e s. MEM e _ /\ _ ==> _` (drule_all_then strip_assume_tac) >> simp[]) >>
  `LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                         value_has_type tv v) args vs` by
    (irule stack_args_values_typed_body >>
     qpat_assum `eval_exprs _ _ _ = _` (irule_at Any) >>
     qpat_assum `expr_sim_inv _ _ _ (es with gas_obs := readings)` (irule_at Any) >>
     first_assum ACCEPT_TAC) >>
  `outcomes_accounts_typed mid.outcomes /\ accounts_runtime_well_typed mid.accounts` by
    (qpat_assum `expr_sim_inv _ _ _ (mid with gas_obs := [])` mp_tac >>
     simp[NoAsms,expr_sim_inv_def,accounts_runtime_well_typed_accounts_well_typed]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx (mid with gas_obs := []) t /\
    storage_well_formed_on cx (mid with gas_obs := []) (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx (mid with gas_obs := []) G tn t` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> typed_args_post _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_x_assum `typed_args_post _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE[typed_args_post_def]) >>
     simp[send_landing_gas_obs]) >>
  fs[storage_trace_domain_def] >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> typed_args_post _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `typed_args_post _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[typed_args_post_def]) >>
  simp[wb_frame_gas_obs,send_landing_gas_obs] >>
  Cases_on `has_gas` >>
  gvs[LENGTH_EQ_NUM_compute, evaluate_type_def, ext_call_kwarg_def,
      eval_operand_def, ptrDisciplineTheory.op_taint_def] >>
  imp_res_tac address_typed_dest >> imp_res_tac uint256_typed_dest >> simp[]
QED
