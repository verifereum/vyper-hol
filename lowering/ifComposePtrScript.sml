Theory ifComposePtr
Ancestors
  ifBranchPtr bodyPtrDefs exprSimDefs exprLoweringProps stmtSimIfProps
  loweringPosts compileEnv loweringStateRelDefs venomState gasSummaryComposePtr fragGasPathPtr
  gasSummaryCompose gasExemptCert vyperState list vyperStorageTrace vyperStorageFootprint

Theorem if_condition_stmt_post_ptr:
  expr_post H ctx func cenv cx c es sa cond s0 mid v op t /\
  ghost_kept cenv es sa G0 tn0 s0 G1 tn1 /\
  sa.cs_next_var <= entry.cs_next_var /\
  stmt_post_ptr H d ctx func cx lctx cenv cenv entry sb
    (jump_to label t) G1 tn1 res ee G tn u ==>
  stmt_post_ptr H d ctx func cx lctx cenv cenv sa sb s0 G0 tn0 res ee G tn u
Proof
  simp[expr_post_def, stmt_post_ptr_def, ghost_kept_def,
       jump_to_def, lookup_var_def] >> strip_tac >>
  qexists_tac `cenv''` >> simp[] >> rpt strip_tac >>
  `not_fresh_at entry x` by fs[not_fresh_at_def] >> metis_tac[]
QED

Theorem if_selected_outcome_prefix_ptr:
  gas_marked_exec F (ctx,func) (bind (eval_expr cx c) (read_result cx))
    (es,s0) marks (INL (BoolV b)) mid (OK t) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_path_ptr (D H) 0 ctx func PG G0 tn0 s0 (LENGTH marks) G1 tn1 (OK t) /\
    expr_post H ctx func cenv cx c es sa cond s0
      (mid with gas_obs := []) (BoolV b) op t) /\
  (!H. gas_path_ptr (D H) 0 ctx func PG G1 tn1 t 0 G1 tn1
    (OK (jump_to label t))) /\
  ghost_kept cenv es sa G0 tn0 s0 G1 tn1 /\
  sa.cs_next_var <= entry.cs_next_var /\
  gas_outcome_ptr D (cx_tops cx) (ctx,func) PG cx st0
    (ignore_bind push_scope (finally (eval_stmts cx (if b then ss1 else ss2)) pop_scope))
    (mid with gas_obs := [],jump_to label t,G1,tn1)
    (\H. stmt_post_ptr H d ctx func cx lctx cenv cenv entry sb (jump_to label t) G1 tn1)
    (\H res ee gt r. !tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) ==>
  gas_outcome_ptr D (cx_tops cx) (ctx,func) PG cx st0 (eval_stmt cx (If c ss1 ss2))
    (es,s0,G0,tn0)
    (\H. stmt_post_ptr H d ctx func cx lctx cenv cenv sa sb s0 G0 tn0)
    (\H res ee gt r. !tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r)
Proof
  strip_tac >>
  `storage_trace_frame
    (ignore_bind push_scope (finally (eval_stmts cx (if b then ss1 else ss2)) pop_scope))` by
    (irule storage_trace_frame_ignore_bind >>
     simp[storage_trace_frame_state_updates] >>
     irule storage_trace_frame_finally >>
     simp[evaluate_storage_trace_frame, storage_trace_frame_pop_scope]) >>
  `gas_outcome_ptr D (cx_tops cx) (ctx,func) PG cx st0
    (ignore_bind push_scope (finally (eval_stmts cx (if b then ss1 else ss2)) pop_scope))
    (mid with gas_obs := [],jump_to label t,G1,tn1)
    (\H. stmt_post_ptr H d ctx func cx lctx cenv cenv sa sb s0 G0 tn0)
    (\H res ee gt r. !tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r)` by
    (qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[gas_outcome_ptr_def, gas_summary_ptr_at_def] >> BETA_TAC >>
     strip_tac >> qexists_tac `marks'`
     >- (disj1_tac >> simp[])
     >- (disj2_tac >> disj1_tac >>
         qexistsl_tac [`res`,`es_end`,`G`,`tn`,`r`] >> asm_rewrite_tac[] >>
         qx_gen_tac `H` >> strip_tac >>
         `valid_horizon cx st0 H mid.storage_trace` by
           (qpat_assum `!tail. ignore_bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
            `valid_horizon cx st0 H (es_end with gas_obs := []).storage_trace` by simp[] >>
            drule_all valid_horizon_frame >> simp[]) >>
         qpat_x_assum `!H. valid_horizon _ _ _ es_end.storage_trace ==> _`
           (drule_then strip_assume_tac) >>
         qpat_x_assum `!H. valid_horizon _ _ _ mid.storage_trace ==> _`
           (drule_then strip_assume_tac) >> simp[]
         >- (disj1_tac >> simp[] >> irule if_condition_stmt_post_ptr >> metis_tac[]) >>
         disj2_tac >> simp[]) >>
     disj2_tac >> disj2_tac >> metis_tac[]) >>
  `gas_outcome_ptr D (cx_tops cx) (ctx,func) PG cx st0
    (ignore_bind push_scope (finally (eval_stmts cx (if b then ss1 else ss2)) pop_scope))
    (mid with gas_obs := [],t,G1,tn1)
    (\H. stmt_post_ptr H d ctx func cx lctx cenv cenv sa sb s0 G0 tn0)
    (\H res ee gt r. !tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r)` by
    (irule gas_outcome_ptr_prefix >> goal_assum (drule_at Any) >>
     qexists_tac `0` >> simp[]) >>
  rewrite_tac[eval_stmt_if_forced] >>
  irule gas_outcome_ptr_bind_normal >>
  qexistsl_tac [`G1`,`marks`,`mid`,`t`,`tn1`,`BoolV b`] >>
  Cases_on `b` >> (
    fs[] >> rpt strip_tac >> irule gas_exempt_cert_bind_value >>
    goal_assum (drule_at Any) >> simp[])
QED
