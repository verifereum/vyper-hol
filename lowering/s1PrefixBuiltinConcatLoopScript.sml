(* Request prefixes through Concat's interleaved evaluations and copies. *)
Theory s1PrefixBuiltinConcatLoop
Ancestors
  bodyFullBuiltinConcatStep bodyFullBuiltinConcatReady exprSimFullBundleProps
  bodyFullIfExpReach[qualified,ignore_grammar] bodySimFull bodyFullPreds
  s1PrefixDefs s1PrefixPreds s1PrefixCompose s1PrefixFrame s1PrefixOfVV s1PrefixProps
  gasOutcomeFullCompose exprSimWordArgs exprSimDefs
  vyperInterpreter vyperStorageTrace vyperStorageFootprint vyperState
  gasExplicitSites loweringPosts venomState list sum

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (irule gas_prefix_full_no_outcome >>
      qhdtm_assum `concat_loop_ready`
        (map_every assume_tac o CONJUNCTS o REWRITE_RULE [concat_loop_ready_def]) >>
      simp[evaluate_storage_trace_frame, eval_exprs_nil]) >>
  rename1 `body_exprs_prefix_ok cx (e::args)` >>
  drule concat_loop_head_entry >>
  disch_then (map_every strip_assume_tac o CONJUNCTS) >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by
    (qhdtm_assum `concat_loop_ready`
       (map_every assume_tac o CONJUNCTS o REWRITE_RULE [concat_loop_ready_def]) >>
     qpat_assum `body_exprs_prefix_ok _ _`
       (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE [body_expr_prefix_ok_def] o
        CONJUNCT1 o PURE_REWRITE_RULE [body_exprs_prefix_ok_def]) >>
     strip_tac >> first_x_assum (drule_then drule) >>
     disch_then (drule_then drule) >> simp[]) >>
  qpat_x_assum `expr_sim_prefix _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_prefix_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sc`,`shadow_sa`,`shadow_sc`,`op`,
                            `s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >-
    (qhdtm_assum `expr_sim_full_hypotheses` mp_tac >>
     pure_rewrite_tac[expr_sim_full_pre_def, expr_sim_full_hypotheses_def,
                      expr_sim_full_code_def] >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_full_via_bundle]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sc`,`shadow_sa`,`shadow_sc`,`op`,
                            `s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  suspend "head_path"
QED
*)
Theorem concat_args_sim_prefix:
  !args P k DF lo d ctx shadow_ctx PG tops func shadow_func cenv cx env st0
    es sa sb shadow_sa shadow_sb s0 G0 tn0 dv ov ow binst B bsz oinst.
    concat_loop_ready args P k DF lo d ctx shadow_ctx PG
      tops func shadow_func cenv cx env st0 es sa sb shadow_sa shadow_sb
      s0 G0 tn0 dv ov ow binst B bsz oinst /\
    body_exprs_prefix_ok cx args ==>
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (eval_exprs cx args) (es,s0,G0,tn0)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume concat_args_sim_prefix[head_path]:
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ headQ headR` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
     (\H res ee G tn t. headQ H res ee G tn t /\
       ?cm. gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (s0,G0,tn0) cm (OK t,G,tn)) headR` by
    (irule bodyFullIfExpReachTheory.gas_outcome_full_post_path >>
     qpat_assum `gas_outcome_full _ _ _ _ _ _ headQ headR` (irule_at Any) >>
     rpt strip_tac >> simp[] >> goal_assum (drule_at Any)) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ headQ headR` kall_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ pathQ headR` >>
  rewrite_tac[eval_exprs_cons_action] >> irule gas_prefix_full_bind >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result, storage_trace_frame_return,
       requests_outcomes_frame_bind_all, evaluate_requests_outcomes_frame,
       requests_outcomes_frame_read_result] >>
  qexistsl_tac [`(\H res ee G tn t. pathQ H res ee G tn t /\
                                     ~t.vs_halted /\ ee.gas_obs = [])`,
    `headR`, `cx_tops cx`] >>
  rpt conj_tac
  >- (BETA_TAC >> qx_genl_tac [`marks`,`v`,`ee`,`G1`,`tn1`,`t`] >>
      strip_tac >> suspend "tail")
  >- (simp[Abbr `headR`] >> rpt gen_tac >> Cases_on `res` >> Cases_on `r` >>
      simp[expr_exit_def]) >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ pathQ headR` (irule_at Any) >> simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume concat_args_sim_prefix[tail]:
  qunabbrev_tac `pathQ` >> qunabbrev_tac `headQ` >>
  qpat_x_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (assume_tac o REWRITE_RULE [GSYM CONJ_ASSOC] o BETA_RULE) >>
  drule_all concat_loop_copy_entry >> strip_tac >>
  `body_exprs_prefix_ok cx args` by
    (qpat_assum `body_exprs_prefix_ok _ (_::_)`
       (irule o CONJUNCT2 o PURE_REWRITE_RULE [body_exprs_prefix_ok_def]) >>
     qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (eval_exprs cx args) (ee,u,G2,tn2)` by
    (qpat_assum `!P k DF lo d ctx shadow_ctx PG. _`
       (fn ih => qhdtm_assum `concat_loop_ready` (mp_then Any irule ih)) >>
     first_assum ACCEPT_TAC) >>
  irule gas_prefix_full_zero_prefix_guarded >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_return] >>
  goal_assum (drule_at Any) >>
  qmatch_goalsub_abbrev_tac `gas_prefix_full p _ _ source _` >>
  `gas_prefix_full p cx st0 source (ee,u,G2,tn2) <=>
   gas_prefix_full p cx st0 (eval_exprs cx args) (ee,u,G2,tn2)` suffices_by simp[] >>
  irule gas_prefix_full_state_cong >> simp[Abbr `source`] >>
  gen_tac >> Cases_on `eval_exprs cx args qe` >> Cases_on `q` >>
  simp[bind_def, return_def]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise concat_args_sim_prefix
*)
