Theory ifComposePtr
Ancestors
  ifBranchPtr bodyPtrDefs exprSimDefs exprLoweringProps stmtSimIfProps
  loweringPosts compileEnv venomState gasSummaryComposePtr fragGasPathPtr
  gasSummaryCompose gasExemptCert vyperState list

Theorem if_condition_stmt_post_ptr:
  expr_post ctx func cenv cx c es sa cond s0 mid v op t /\
  ghost_kept cenv es sa G0 tn0 s0 G1 tn1 /\
  sa.cs_next_var <= entry.cs_next_var /\
  stmt_post_ptr d ctx func cx lctx cenv cenv entry sb
    (jump_to label t) G1 tn1 res ee G tn u ==>
  stmt_post_ptr d ctx func cx lctx cenv cenv sa sb s0 G0 tn0 res ee G tn u
Proof
  simp[expr_post_def, stmt_post_ptr_def, ghost_kept_def,
       jump_to_def, lookup_var_def] >> strip_tac >>
  qexists_tac `cenv''` >> simp[] >> rpt strip_tac >>
  `not_fresh_at entry x` by fs[not_fresh_at_def] >> metis_tac[]
QED

Theorem if_selected_outcome_prefix_ptr:
  gas_marked_exec_ptr D (ctx,func) PG (bind (eval_expr cx c) (read_result cx))
    (es,s0,G0,tn0) marks (INL (BoolV b)) mid G1 tn1 (OK t) /\
  gas_path_ptr D 0 ctx func PG G1 tn1 t 0 G1 tn1 (OK (jump_to label t)) /\
  expr_post ctx func cenv cx c es sa cond s0 (mid with gas_obs := []) (BoolV b) op t /\
  ghost_kept cenv es sa G0 tn0 s0 G1 tn1 /\
  sa.cs_next_var <= entry.cs_next_var /\
  gas_outcome_ptr D (cx_tops cx) (ctx,func) PG
    (ignore_bind push_scope (finally (eval_stmts cx (if b then ss1 else ss2)) pop_scope))
    (mid with gas_obs := [],jump_to label t,G1,tn1)
    (stmt_post_ptr d ctx func cx lctx cenv cenv entry sb (jump_to label t) G1 tn1)
    (\res ee gt r. !tail. stmt_exit_ptr RetQ (ee with gas_obs := tail) res gt r) ==>
  gas_outcome_ptr D (cx_tops cx) (ctx,func) PG (eval_stmt cx (If c ss1 ss2))
    (es,s0,G0,tn0)
    (stmt_post_ptr d ctx func cx lctx cenv cenv sa sb s0 G0 tn0)
    (\res ee gt r. !tail. stmt_exit_ptr RetQ (ee with gas_obs := tail) res gt r)
Proof
  strip_tac >>
  `gas_marked_exec_ptr D (ctx,func) PG (bind (eval_expr cx c) (read_result cx))
     (es,s0,G0,tn0) marks (INL (BoolV b)) mid G1 tn1 (OK (jump_to label t))` by
    (qpat_x_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_ptr_def] >> strip_tac >> simp[] >>
     drule_all gas_path_ptr_then >> simp[]) >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_ptr_def, gas_summary_ptr_at_marked] >> strip_tac
  >- suspend "normal"
  >- suspend "exit"
  >> suspend "cert"
QED

Resume if_selected_outcome_prefix_ptr[normal]:
  gvs[] >> qexists_tac `marks ++ marks'` >> disj1_tac >>
  qexistsl_tac [`res`, `es_end`, `G`, `tn`, `OK t'`] >> conj_tac
  >- (rewrite_tac[eval_stmt_if_forced] >>
      irule gas_marked_exec_ptr_bind_normal >>
      qexistsl_tac [`G1`, `mid`, `jump_to label t`, `tn1`, `BoolV b`] >>
      simp[] >> Cases_on `b` >> fs[]) >>
  disj1_tac >> simp[] >> drule_all if_condition_stmt_post_ptr >> simp[]
QED

Resume if_selected_outcome_prefix_ptr[exit]:
  qexists_tac `marks ++ marks'` >> disj1_tac >>
  qexistsl_tac [`res`, `es_end`, `G`, `tn`, `r`] >> simp[] >>
  rewrite_tac[eval_stmt_if_forced] >>
  irule gas_marked_exec_ptr_bind_normal >>
  qexistsl_tac [`G1`, `mid`, `jump_to label t`, `tn1`, `BoolV b`] >>
  simp[] >> Cases_on `b` >> fs[]
QED

Resume if_selected_outcome_prefix_ptr[cert]:
  drule gas_marked_exec_ptr_exec >> strip_tac >>
  qexists_tac `marks ++ marks'` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  rewrite_tac[eval_stmt_if_forced] >>
  pure_once_rewrite_tac[ignore_bind_def] >>
  pure_once_rewrite_tac[vyperStateTheory.bind_assoc] >>
  irule gas_exempt_cert_bind_value >>
  qexistsl_tac [`mid`, `jump_to label t`, `BoolV b`] >> simp[] >>
  Cases_on `b` >> fs[GSYM ignore_bind_def]
QED
Finalise if_selected_outcome_prefix_ptr
