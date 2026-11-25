(* The normal SelfDestruct operand carries the original source run and the
   very same landing and ghosts at every valid storage horizon. *)
Theory entryCreateSelfdestructOperand
Ancestors
  exprSimSend selfdestructHalt
  gasNormalPrefix fragGasSeqPtr fragGasOriginPtr vyperStorageFootprint
  vyperStorageTrace vyperTyping loweringStateRelDefs gasContext vyperState
  vyperValue exprSimDefs exprLoweringProps loweringPosts bodyPtrDefs s1PrefixDefs
  exprSimFullBundleProps gasSummary fragGasOrigin gasExplicitSites compileEnv

Theorem selfdestruct_child_address[local]:
  gas_admissible
    (bind (bind (bind (eval_expr cx e) (read_result cx)) (selfdestruct_tail cx))
      (read_result cx)) expr_res_ok es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := readings) =
    (INL v, ee with gas_obs := []) ==>
  value_has_type (BaseTV AddressT) v
Proof
  strip_tac >>
  `?a. dest_AddressV v = SOME a` by
    (Cases_on `dest_AddressV v` >> simp[] >>
     qpat_x_assum `gas_admissible _ _ _`
       (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
     disch_then (qspecl_then [`readings`,
       `INR (Error (TypeError "selfdestruct target"))`,
       `ee with gas_obs := []`] mp_tac) >>
     once_rewrite_tac[bind_assoc] >> pure_once_rewrite_tac[bind_def] >>
     asm_rewrite_tac[] >>
     simp[selfdestruct_tail_def, lift_option_type_def, bind_def, raise_def,
       expr_res_ok_def, vyperStateTheory.evaluation_state_component_equality]) >>
  Cases_on `v` >> gvs[dest_AddressV_def, value_has_type_def]
QED

Theorem selfdestruct_child_address_word[local]:
  post_value_type ce e = BaseT AddressT /\
  expr_post H ctx func ce cx e es sa sm s0 (ee with gas_obs := []) v op t /\
  ptr_val_ok cx (post_value_type ce e) v op G tn t ==>
  eval_operand op t = SOME (typed_val_to_w256 (BaseTV AddressT) v) /\
  op_taint tn op = {} /\ op_prov G op = NONE
Proof
  strip_tac >> conj_tac
  >- (qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
      simp[NoAsms, expr_post_def] >> strip_tac >>
      gvs[expr_val_rel_def, is_word_type_def, evaluate_type_def]) >>
  gvs[ptr_val_ok_def, is_word_type_def]
QED

Theorem selfdestruct_selected_address_prefix:
  expr_type e = BaseT AddressT /\
  gas_admissible
    (bind (bind (bind (eval_expr cx e) (read_result cx)) (selfdestruct_tail cx))
      (read_result cx)) expr_res_ok es /\
  expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx (expr_type e) e es
    (st0,sa,sm,sha,shm,op,s0,G0,tn0) /\
  (!tail. bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
     (INL v, ee with gas_obs := tail)) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
       (s0,G0,tn0) marks (OK t,G,tn) /\
     expr_sim_full_post (DF,lo,d,ctx,func) ce cx e (es,sa,sm,s0,op,G0,tn0)
       H (INL v) (ee with gas_obs := []) G tn t) ==>
  valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace /\
  valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) es.storage_trace /\
  expr_post (storage_trace_horizon ee.storage_trace) ctx func ce cx e
    es sa sm s0 (ee with gas_obs := []) v op t /\
  dest_AddressV v = SOME (w2w (typed_val_to_w256 (BaseTV AddressT) v)) /\
  eval_operand op t = SOME (typed_val_to_w256 (BaseTV AddressT) v) /\
  ~t.vs_halted /\ op_taint tn op = {} /\ op_prov G op = NONE /\
  t.vs_call_ctx.cc_address = cx.txn.target /\
  t.vs_call_ctx.cc_created_in_tx = cx.txn.created_in_tx /\
  t.vs_call_ctx.cc_static = cx.txn.is_static /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  gas_value_prefix (storage_trace_horizon ee.storage_trace) T
    (ctx,func,ce,cx) (expr_type e,e) (sa,sm,op) (es,s0) marks (v,ee,t)
Proof
  strip_tac >>
  qmatch_goalsub_abbrev_tac `valid_horizon cx st0 hc ee.storage_trace` >>
  `valid_horizon cx st0 hc ee.storage_trace` by
    fs[Abbr `hc`, storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
    (qspec_then `hc` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) [expr_sim_full_post_def]) >>
  `bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
      (INL v,ee with gas_obs := [])` by
    (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     pure_rewrite_tac[listTheory.APPEND_NIL] >> disch_then ACCEPT_TAC) >>
  `dest_AddressV v = SOME (w2w (typed_val_to_w256 (BaseTV AddressT) v))` by
    (irule address_typed_dest >> irule selfdestruct_child_address >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  `valid_horizon cx st0 hc es.storage_trace` by
    (`storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
       (irule storage_trace_frame_bind_all >>
        simp[evaluate_storage_trace_frame,storage_trace_frame_read_result]) >>
     drule valid_horizon_frame >> disch_then drule >> simp[]) >>
  `post_value_type ce e = BaseT AddressT` by simp[is_word_type_def] >>
  drule_all selfdestruct_child_address_word >> strip_tac >>
  drule gas_origin_ptr_path_projections >> strip_tac >>
  drule gas_origin_path_erase >> strip_tac >>
  `~t.vs_halted` by metis_tac[gas_path_ptr_ok_not_halted] >>
  `t.vs_call_ctx.cc_address = cx.txn.target /\
   t.vs_call_ctx.cc_created_in_tx = cx.txn.created_in_tx /\
   t.vs_call_ctx.cc_static = cx.txn.is_static` by
    fs[expr_post_def, stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  simp[gas_value_prefix_def, gas_marked_exec_def] >>
  gvs[expr_sim_full_pre_def, expr_sim_full_endpoint_def] >>
  first_x_assum drule >> simp[]
QED
