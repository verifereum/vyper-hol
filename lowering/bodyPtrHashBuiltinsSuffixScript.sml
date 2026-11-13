(* Marked operand execution is the boundary needed to recover source typing. *)
Theory bodyPtrHashBuiltinsSuffix
Ancestors
  bodyPtrDefs gasSummaryComposePtr gasSummaryComposePtrAll fragGasSeqPtr gasExemptCert
  gasSummary exprSimHash exprSimDefs fragGasPathPtr vyperState list

Theorem hash_marked_ptr_normal:
  gas_marked_exec_ptr D (ctx, func) PG source (es, s0, G0, tn0)
    marks res ee G tn (OK t) ==>
  source (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (res, ee with gas_obs := []) /\ ~t.vs_halted
Proof
  rewrite_tac[gas_marked_exec_ptr_def] >> strip_tac >>
  conj_tac
  >- (first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  metis_tac[gas_path_ptr_ok_not_halted]
QED

(* General value-result bind boundary: normal callbacks see the actual
   source run, whereas exceptional/exempt operands need no continuation. *)
Theorem hash_value_outcome_ptr_suffix:
  gas_outcome_ptr D tops (ctx, func) PG cx st0 source (es, s0, G0, tn0)
    (\H res ee G tn t. ?v:value. res = INL v /\ P H v ee G tn t)
    (\H res ee gt r. expr_exit res r) /\
  (!H exc ee gt r. valid_horizon cx st0 H ee.storage_trace /\
     expr_exit (INR exc : value + exception) r ==>
     R H (INR exc) ee gt r) /\
  (!v. storage_trace_frame (k v)) /\
  (!gs v ee G tn t.
     source (es with gas_obs := gs) = (INL v, ee) /\
     ee.gas_obs = [] /\
     (?H. valid_horizon cx st0 H ee.storage_trace) /\
     (!H. valid_horizon cx st0 H ee.storage_trace ==>
       P H v ee G tn t /\ ~t.vs_halted) ==>
     ?right. gas_summary_ptr_at D (ctx, func) PG cx st0 right (k v)
       (ee, t, G, tn) Q R) ==>
  gas_outcome_ptr D tops (ctx, func) PG cx st0 (bind source k)
    (es, s0, G0, tn0) Q R
Proof
  strip_tac >> irule gas_outcome_ptr_bind_all >>
  first_assum (irule_at (Pat `gas_outcome_ptr _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> rpt conj_tac >> rpt strip_tac
  >~ [`gas_exempt_cert F tops (ctx,func) _ _ (left ++ right) _ _`]
  >- (irule gas_exempt_cert_bind_value >>
      goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert F tops (ctx,func) _ _ marks _ _`]
  >- (simp[ignore_bind_def, bind_assoc] >>
      irule gas_exempt_cert_error_value >> fs[ignore_bind_def])
  >~ [`gas_outcome_ptr D tops (ctx,func) PG cx st0 (k v) _ Q R`]
  >- (fs[gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def] >>
      `~t.vs_halted` by metis_tac[fragGasPathTheory.gas_path_normal] >>
      `?right. gas_summary_ptr_at D (ctx,func) PG cx st0 right (k v)
        (mid with gas_obs := [],t,G,tn) Q R` by
        (first_x_assum irule >> simp[] >> metis_tac[]) >>
      rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `right` >>
      disj2_tac >> disj1_tac >> first_assum ACCEPT_TAC) >>
  Cases_on `res` >> gvs[expr_exit_INL] >> metis_tac[]
QED

Theorem hash_expr_sim_ptr_suffix:
  expr_sim_ptr d ctx PG func cenv cx ty e es /\
  lower_value compile_expr cenv ty e sa = (op, sm) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv H d cenv cx es G0 tn0 s0) /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!H exc ee gt r. valid_horizon cx st0 H ee.storage_trace /\
     expr_exit (INR exc : value + exception) r ==>
     R H (INR exc) ee gt r) /\
  (!v. storage_trace_frame (k v)) /\
  (!gs v ee G tn t.
     bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
       (INL v, ee) /\ ee.gas_obs = [] /\
     (?H. valid_horizon cx st0 H ee.storage_trace) /\
     (!H. valid_horizon cx st0 H ee.storage_trace ==>
     expr_post H ctx func cenv cx e es sa sm s0 ee v op t /\ ~t.vs_halted /\
     t.vs_current_bb = sm.cs_current_bb /\
     t.vs_inst_idx = LENGTH sm.cs_current_insts /\
     ghost_inv H d cenv cx ee G tn t /\
     ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
     (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G t) /\
     ghost_kept cenv es sa G0 tn0 s0 G tn) ==>
     ?right. gas_summary_ptr_at (\H. cx_dead H cx) (ctx, func) PG cx st0 right (k v)
       (ee, t, G, tn) Q R) ==>
  gas_outcome_ptr (\H. cx_dead H cx) (cx_tops cx) (ctx, func) PG cx st0
    (bind (bind (eval_expr cx e) (read_result cx)) k)
    (es, s0, G0, tn0) Q R
Proof
  strip_tac >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_ptr_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `op`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  irule hash_value_outcome_ptr_suffix >>
  conj_tac >- metis_tac[] >> simp[] >>
  qexists_tac `\H v ee G tn t.
    expr_post H ctx func cenv cx e es sa sm s0 ee v op t /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    ghost_inv H d cenv cx ee G tn t /\
    ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G t) /\
    ghost_kept cenv es sa G0 tn0 s0 G tn` >>
  simp[] >> metis_tac[]
QED
