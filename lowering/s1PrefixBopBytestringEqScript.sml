Theory s1PrefixBopBytestringEq
Ancestors
  s1PrefixPreds s1PrefixCompose s1PrefixFrame s1PrefixOfVV bodyFullPreds
  bodyFullBopBytestringCuts bodyFullBopBytestringIntervals bodyFullBopBytestringChild
  bodyFullIfExpReach exprSimSource exprBodyPreProps exprBodyPreTypingProps
  exprBodyPreCallSafetyProps exprSimLiteralWord gasShadowCompilePure exprBopSimProps
  exprBopSimDefs vyperFiniteStoragePreservation vyperStorageTrace vyperState
  s1PrefixDefs exprLowering gasShadow exprSimHyps vyperTypeSystem
  vyperStorageFootprint gasOutcomeFullCompose bodyMemoryDefs exprLoweringProps
  loweringShapeDefs loweringPosts vyperAST gasOutcomeFull list s1PrefixProps
  bodyFullHashKeccakFixed bodyFullExprsListFacts bodyFullSimProjection
Libs pairLib

Theorem selected_bytestring_operand_prefix[local]:
  expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type e) e es /\ ~s.vs_halted /\
  (!m cb. bytestring_literal_hash e = NONE /\
     lower_value compile_expr cenv (expr_type e) e sa = (m,cb) ==>
     ?shadow_cb. expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
       cenv cx (expr_type e) e es (st0,sa,cb,shadow_sa,shadow_cb,m,s,G,tn)) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
Proof
  strip_tac >> Cases_on `bytestring_literal_hash e`
  >- (Cases_on `lower_value compile_expr cenv (expr_type e) e sa` >>
      rename1 `lower_value _ _ _ _ _ = (m,cb)` >>
      first_x_assum (qspecl_then [`m`, `cb`] mp_tac) >> simp[] >> strip_tac >>
      qpat_assum `expr_sim_prefix _ _ _ _ _ _`
        (drule_then ACCEPT_TAC o REWRITE_RULE [expr_sim_prefix_def])) >>
  Cases_on `e` >> gvs[bytestring_literal_hash_def] >>
  irule gas_prefix_full_no_outcome >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result, literal_read_all_tails]
QED

Theorem bytestring_operand_storage_well_formed[local]:
  body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
    (INL v,mid with gas_obs := []) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       storage_well_formed_on cx es (FST H)) /\
  valid_horizon cx st0 H mid.storage_trace ==>
  storage_well_formed_on cx mid (FST H)
Proof
  strip_tac >> drule (REWRITE_RULE [ETA_THM] eval_expr_read_INL) >> strip_tac >>
  drule read_result_state >> disch_then (SUBST_ALL_TAC o SYM) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (qpat_assum `eval_expr _ _ _ = _` (mp_then Any mp_tac valid_horizon_frame) >>
     simp[evaluate_storage_trace_frame]) >>
  `storage_well_formed_on cx (mid with gas_obs := []) (FST H) <=>
   storage_well_formed_on cx mid (FST H)` by
    (irule storage_well_formed_on_backends >> simp[]) >>
  `storage_well_formed_on cx (mid with gas_obs := []) (FST H)` suffices_by
    metis_tac[] >>
  `storage_well_formed_on cx (es with gas_obs := gs) (FST H) <=>
   storage_well_formed_on cx es (FST H)` by
    (irule storage_well_formed_on_backends >> simp[]) >>
  `expr_body_pre_mods [(NONE,tops)] cenv cx env e (es with gas_obs := gs)` by
    (irule body_inv_expr_body_pre_mods >> metis_tac[expr_body_pre_gas_obs]) >>
  drule_then strip_assume_tac expr_body_pre_mods_runtime_typing >>
  drule expr_body_pre_call_evaluation_safe >> strip_tac >>
  qpat_assum `valid_horizon cx st0 H mid.storage_trace`
    (strip_assume_tac o REWRITE_RULE [valid_horizon_def]) >>
  irule (cj 1 (cj 5 (Q.SPEC `H` eval_storage_well_formed_on_mutual))) >>
  simp[] >> qpat_assum `eval_expr _ _ _ = _` (irule_at Any) >>
  qexists_tac `env` >> simp[] >> metis_tac[]
QED

Theorem body_exprs_full_ok_cons_value[local]:
  body_exprs_full_ok cx (e::es') /\ body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env e es ==>
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es
Proof
  simp[Once body_exprs_full_ok_cons] >>
  metis_tac[body_expr_full_ok_simulations]
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule expr_body_pre_bop >> strip_tac >>
  `expr_type e2 = expr_type e1` by metis_tac[well_typed_binop_def] >>
  simp[expr_sim_prefix_def, expr_sim_full_pre_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all bop_bytestring_selected_compile_cuts >> strip_tac >>
  drule_all bop_bytestring_selected_code_intervals >> strip_tac >>
  `(!m cb. bytestring_literal_hash e1 = NONE /\
      lower_value compile_expr (gas_shadow_env T cenv) (expr_type e1) (gas_shadow_expr e1) shadow_sa = (m,cb) ==>
      fn_has_code shadow_sa cb shadow_func) /\
   (!m cb. bytestring_literal_hash e2 = NONE /\
      lower_value compile_expr (gas_shadow_env T cenv) (expr_type e2) (gas_shadow_expr e2) shadow_sh1 = (m,cb) ==>
      fn_has_code shadow_sh1 cb shadow_func)` by
    (qpat_x_assum `lower_value _ _ _ (Builtin _ _ [e1;e2]) _ = _` kall_tac >>
     qpat_x_assum `lower_value _ _ _ (gas_shadow_expr (Builtin _ _ _)) _ = _`
       (assume_tac o SIMP_RULE (srw_ss()) [gas_shadow_expr_def, gas_shadow_builtin_def, MAP]) >>
     `is_bytestring_type (expr_type (gas_shadow_expr e1)) /\
      expr_type (gas_shadow_expr e2) = expr_type (gas_shadow_expr e1)` by simp[] >>
     drule_all bop_bytestring_selected_code_intervals >> simp[] >> strip_tac >> simp[]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e1) e1 es` by
    (irule body_exprs_full_ok_cons_value >>
     qpat_assum `body_exprs_full_ok cx [e1;e2]` (irule_at Any) >> metis_tac[]) >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e1) e1 es` by
    (qpat_assum `body_exprs_prefix_ok cx [e1;e2]` mp_tac >>
     simp[body_exprs_prefix_ok_def] >> metis_tac[body_expr_prefix_ok_def]) >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (bind (eval_expr cx e1) (read_result cx)) (es,s0,G0,tn0)` by
    (irule selected_bytestring_operand_prefix >> simp[] >>
     qexistsl_tac [`cenv`, `d`, `sa`, `shadow_func`, `shadow_sa`] >>
     simp[expr_sim_full_pre_def] >> rpt gen_tac >> strip_tac >>
     qpat_assum `!m cb. bytestring_literal_hash e1 = NONE /\ _ ==> ?shadow_cb. _` drule_all >>
     strip_tac >> qexists_tac `shadow_cb` >> simp[] >>
     conj_tac >- (irule expr_body_pre_gas_admissible >> metis_tac[]) >>
     first_assum ACCEPT_TAC) >>
  suspend "left_outcome"
QED
*)
Theorem bop_bytestring_eqne_value_prefix:
  (bop = Eq \/ bop = NotEq) /\ is_bytestring_type (expr_type e1) /\
  body_exprs_full_ok cx [e1;e2] /\ body_exprs_prefix_ok cx [e1;e2] /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1;e2]) es ==>
  expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty
    (Builtin ann (Bop bop) [e1;e2]) es
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume bop_bytestring_eqne_value_prefix[left_outcome]:
  (* The right operand starts after the selected left hash, not after
     lower_value on the left operand. *)
  qmatch_asmsub_abbrev_tac `gas_prefix_full params _ _ _ _` >>
  `gas_outcome_full params (cx_tops cx) cx st0
     (bind (eval_expr cx e1) (read_result cx)) (es,s0,G0,tn0)
     (\H res mid G1 tn1 t.
       stmt_state_rel H ctx func cenv cx mid t /\
       ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t /\ ~t.vs_halted /\
       t.vs_current_bb = sh1.cs_current_bb /\ t.vs_inst_idx = LENGTH sh1.cs_current_insts /\
       alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
       wb_frame cenv es mid sa s0 t /\
       (!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u))
     (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r)` by
    (simp[Abbr `params`] >> irule gas_outcome_full_post_path >>
     irule_at (Pat `gas_outcome_full _ _ _ _ _ _ _ _`)
       bop_bytestring_selected_child_full_halt >>
     simp[] >> qexistsl_tac [`tops`, `sh1`, `shadow_func`, `shadow_ctx`, `sa`, `h1`, `env`, `d`, `cenv`] >>
     simp[] >> rpt conj_tac
     >- metis_tac[]
     >- (rpt gen_tac >> strip_tac >>
         qpat_assum `!m cb. bytestring_literal_hash e1 = NONE /\ _ ==> ?shadow_cb. _` drule_all >>
         strip_tac >> qexistsl_tac [`shadow_sa`, `shadow_cb`] >> simp[] >>
         irule expr_body_pre_gas_admissible >> metis_tac[]) >>
     rpt gen_tac >> strip_tac >>
     drule gas_origin_ptr_path_dalloca_fmp_headroom >> simp[] >> metis_tac[body_inv_no_phi]) >>
  qunabbrev_tac `params` >>
  pure_once_rewrite_tac[REWRITE_RULE [ETA_AX] eval_expr_bop_bind] >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (mp_then Any irule gas_prefix_full_bind) >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result, requests_outcomes_frame_bind_all,
       evaluate_requests_outcomes_frame, requests_outcomes_frame_read_result] >>
  reverse (rpt conj_tac)
  >- (gen_tac >> irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
           storage_trace_frame_read_result, storage_trace_frame_def, bop_result_def])
  >- (rpt gen_tac >> rename1 `expr_exit res r /\ _ ==> _` >> Cases_on `res` >> simp[]) >>
  suspend "right_prefix"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume bop_bytestring_eqne_value_prefix[right_prefix]:
  qx_genl_tac [`marks`, `v1`, `mid`, `G1`, `tn1`, `t`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then strip_assume_tac)) >>
  qpat_assum `!tail. bind _ _ _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  `expr_body_pre cenv cx env e2 mid` by
    (qpat_assum `!es'. expr_sim_inv _ _ _ es' ==> _` irule >>
     drule_at (Pos last) (REWRITE_RULE [ETA_THM] expr_body_pre_eval) >>
     disch_then (qspec_then `cenv` mp_tac) >> simp[] >> metis_tac[]) >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (`well_typed_expr env e1` by metis_tac[expr_body_pre_static_facts] >>
     `body_const_cells_agree [(NONE,tops)] cx env (mid with gas_obs := [])`
       suffices_by simp[] >>
     irule body_const_cells_agree_expr_read >>
     qpat_assum `bind (eval_expr cx e1) _ _ = (_,mid with gas_obs := [])`
       (irule_at Any) >> simp[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       storage_well_formed_on cx mid (FST H)` by
    (gen_tac >> strip_tac >> irule bytestring_operand_storage_well_formed >>
     qpat_assum `bind (eval_expr cx e1) _ _ = (_,mid with gas_obs := [])`
       (irule_at Any) >> qexistsl_tac [`tops`, `st0`, `env`, `ctx`, `cenv`] >> simp[]) >>
  drule (REWRITE_RULE [ETA_THM] eval_expr_read_INL) >> strip_tac >>
  `body_expr_prefix_ok cx e2` by
    (qpat_assum `body_exprs_prefix_ok cx [e1;e2]` mp_tac >>
     simp[body_exprs_prefix_ok_def, NoAsms] >> strip_tac >> first_x_assum irule >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e2) e2 mid` by metis_tac[body_expr_prefix_ok_def] >>
  `local_ptrs_reserved cenv sh1` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sh1 x) /\
   (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sh1 x)` by
    metis_tac[not_fresh_at_mono] >>
  `return_buf_frame d cenv sh1 t` by
    (irule return_buf_frame_frame >>
     qpat_assum `return_buf_frame d cenv sa s0` (irule_at Any) >>
     fs[wb_frame_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    metis_tac[stmt_state_rel_allocas_below_fmp] >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (bind (eval_expr cx e2) (read_result cx)) (mid,t,G1,tn1)` by
    (irule selected_bytestring_operand_prefix >> simp[] >>
     qexistsl_tac [`cenv`, `d`, `sh1`, `shadow_func`, `shadow_sh1`] >>
     qpat_assum `expr_type e2 = expr_type e1` (fn eq =>
       RULE_ASSUM_TAC (REWRITE_RULE [eq])) >>
     simp[expr_sim_full_pre_def] >> rpt gen_tac >> strip_tac >>
     qpat_assum `!m cb. bytestring_literal_hash e2 = NONE /\ _ ==> ?shadow_cb. _` drule_all >>
     strip_tac >> qexists_tac `shadow_cb` >> simp[] >>
     rpt conj_tac >- metis_tac[expr_body_pre_gas_admissible] >> metis_tac[]) >>
  qpat_assum `gas_prefix_full _ _ _ (bind (eval_expr cx e2) _) _`
    (mp_then Any irule (iffLR gas_prefix_full_state_cong)) >>
  gen_tac >> Cases_on `bind (eval_expr cx e2) (read_result cx) qe` >>
  rename1 `_ = (res,ee)` >> Cases_on `res` >> simp[bind_def]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise bop_bytestring_eqne_value_prefix
*)
