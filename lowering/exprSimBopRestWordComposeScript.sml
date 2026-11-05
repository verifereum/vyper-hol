(* Source-only bridges for counted mixed word/vv operand composition. *)
Theory exprSimBopRestWordCompose
Ancestors
  gasSummary gasSummaryCompose gasExemptCert exprBopSimProps vyperState
  vyperInterpreter exprSimMemorySource list allocLimits exprSimHypsDefs
  localPtrsProps exprSimProps freshWrites exprSimBopRestWordTail

Theorem rest_word_marked_read:
  gas_marked_exec memory (ctx, func) (eval_expr cx e)
    (es,s0) marks (INL tv) mid (OK t) /\
  (!tail. read_result cx tv (mid with gas_obs := tail) =
    (INL v, mid with gas_obs := tail)) ==>
  gas_marked_exec memory (ctx, func)
    (bind (eval_expr cx e) (read_result cx))
    (es,s0) marks (INL v) mid (OK t)
Proof
  simp[gas_marked_exec_def] >> strip_tac >>
  simp[bind_def]
QED

Theorem rest_word_raw_second_exempt_cert:
  gas_marked_exec memory (ctx,func)
    (bind (eval_expr cx e1) (read_result cx))
    (es,s0) left (INL v1) mid (OK t) /\
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (eval_expr cx e2) (return ()))
    (mid with gas_obs := [],t) right (err,ee) (leaf,sf) ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (bind (eval_expr cx (Builtin ann (Bop bop) [e1;e2]))
                      (read_result cx)) (return ()))
    (es,s0) (left ++ right) (err,ee) (leaf,sf)
Proof
  strip_tac >> drule force_exempt_cert >> strip_tac >>
  irule (REWRITE_RULE [ETA_AX] bop_second_exempt_cert) >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem rest_word_mixed_marked_tail:
  gas_marked_exec memory (ctx,func)
    (bind (eval_expr cx e1) (read_result cx))
    (es,s0) left (INL v1) mid (OK t) /\
  gas_marked_exec memory (ctx,func) (eval_expr cx e2)
    (mid with gas_obs := [],t) right (INL tv2) fin (OK u) /\
  (!tail. read_result cx tv2 (fin with gas_obs := tail) =
    (INL v2,fin with gas_obs := tail)) /\
  gas_marked_exec memory (ctx,func)
    (\ee. (bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 ee,ee))
    (fin with gas_obs := [],u) suffix res last r ==>
  gas_marked_exec memory (ctx,func)
    (bind (eval_expr cx (Builtin ann (Bop bop) [e1;e2])) (read_result cx))
    (es,s0) (left ++ right ++ suffix) res last r
Proof
  strip_tac >> drule_all rest_word_marked_read >> strip_tac >>
  pure_once_rewrite_tac[REWRITE_RULE [ETA_AX] eval_expr_bop_bind] >>
  rewrite_tac[GSYM APPEND_ASSOC] >>
  irule gas_marked_exec_bind_normal >>
  goal_assum (drule_at Any) >> BETA_TAC >>
  irule gas_marked_exec_bind_normal >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem rest_word_mixed_tail_summary:
  gas_marked_exec memory (ctx,func)
    (bind (eval_expr cx e1) (read_result cx))
    (es,s0) left (INL v1) mid (OK t) /\
  gas_marked_exec memory (ctx,func) (eval_expr cx e2)
    (mid with gas_obs := [],t) right (INL tv2) fin (OK u) /\
  (!tail. read_result cx tv2 (fin with gas_obs := tail) =
    (INL v2,fin with gas_obs := tail)) /\
  gas_marked_exec memory (ctx,func)
    (\ee. (bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 ee,ee))
    (fin with gas_obs := [],u) suffix res last r /\
  ((?z. r = OK z /\ Q res (last with gas_obs := []) z) \/
   (exit_result r /\ R res (last with gas_obs := []) r)) ==>
  gas_summary_at memory (ctx,func) (left ++ right ++ suffix)
    (bind (eval_expr cx (Builtin ann (Bop bop) [e1;e2])) (read_result cx))
    (es,s0) Q R
Proof
  strip_tac >> drule_all rest_word_mixed_marked_tail >> strip_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`res`, `last`, `r`] >> simp[]
QED

Theorem rest_word_mixed_post:
  expr_post ctx func cenv cx e1 es sa s1 s0 es1 v1 x t /\
  vv_post ctx func cenv cx e2 es1 s1 sm t es2 tv vv q /\
  expr_val_rel cx ann v out q /\
  expr_val_at cenv cx ann sa ct es2 v out q /\
  local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s0 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id ==>
  expr_post ctx func cenv cx (Builtin ann (Bop bop) [e1;e2])
    es sa ct s0 es2 v out q
Proof
  simp[loweringPostsTheory.expr_post_def, loweringPostsTheory.vv_post_def] >> strip_tac >>
  simp[vyperASTTheory.expr_type_def] >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at s1 x'` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
      metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!aid off sz. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> _`
        (qspecl_then [`aid`, `off`, `sz`] mp_tac) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      disch_then (fn th => rewrite_tac [GSYM th]) >>
      qpat_x_assum `!aid off sz. FLOOKUP t.vs_allocas aid = _ /\ _ ==> _`
        (qspecl_then [`aid`, `off`, `sz`] mp_tac) >>
      disch_then irule >> rpt conj_tac
      >- (rpt strip_tac >>
          qpat_x_assum `!n b sz'. local_region _ es.scopes s0 _ _ _ ==> _` irule >>
          qexists `n` >> irule local_region_frame >>
          conj_tac >- (qexists `func` >>
            gvs[exprLoweringPropsTheory.stmt_state_rel_def, compileEnvTheory.state_rel_def]) >>
          qexistsl [`sa`, `es1.scopes`, `t`] >> asm_rewrite_tac[])
      >- (irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
          qexists `sa.cs_next_id` >> asm_rewrite_tac[]) >>
      metis_tac[]) >>
  irule locals_kept_trans >> qexistsl [`es1`, `sa`, `t`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem rest_word_alloc_root:
  alloc_limits_expr cenv e ==> type_alloc_ok cenv (expr_type e)
Proof
  Cases_on `e` >> simp[allocLimitsTheory.alloc_limits_expr_def,
    vyperASTTheory.expr_type_def]
QED

Theorem rest_word_array_alloc_bound:
  is_word_type ty /\ type_alloc_ok cenv (ArrayT ty bd) ==>
  (case bd of Fixed n => n | Dynamic n => n) < dimword (:256)
Proof
  strip_tac >>
  `elem_size_in_location cenv LocMemory ty = word_scale LocMemory` by
    metis_tac[exprSimBopRestWordTailTheory.rest_word_word_stride] >>
  `type_memory_bytes cenv ty = 32` by
    fs[compileEnvTheory.elem_size_in_location_def,
      compileEnvTheory.is_slot_addressed_def, compileEnvTheory.word_scale_def] >>
  Cases_on `bd` >>
  gvs[allocLimitsTheory.type_alloc_ok_def, compileEnvTheory.is_word_type_def,
    compileEnvTheory.type_memory_bytes_def, wordsTheory.dimword_def] >> decide_tac
QED

Theorem rest_word_mixed_outcome:
  lower_value compile_expr cenv (expr_type e1) e1 sa = (x,s1) /\
  compile_expr cenv (expr_type e2) e2 s1 = (vv,sm) /\
  compile_var_array_membership cenv x vv (expr_type e2) (bop = In) sm = (out,ct) /\
  fn_has_code sa s1 func /\ fn_has_code s1 sm func /\ fn_has_code sm ct func /\
  fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv s1 /\
  sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  gas_admissible (bind (eval_expr cx (Builtin ann (Bop bop) [e1;e2])) (read_result cx))
    expr_res_ok es /\
  expr_sim ctx func cenv cx (expr_type e1) e1 es /\
  (!left v1 mid t.
    gas_marked_exec F (ctx,func) (bind (eval_expr cx e1) (read_result cx))
      (es,s0) left (INL v1) mid (OK t) /\
    expr_post ctx func cenv cx e1 es sa s1 s0 (mid with gas_obs := []) v1 x t /\
    t.vs_current_bb = s1.cs_current_bb /\ t.vs_inst_idx = LENGTH s1.cs_current_insts ==>
    expr_vv_sim ctx func cenv cx (expr_type e2) e2 (mid with gas_obs := []) /\
    gas_admissible (eval_expr cx e2) expr_vv_res_ok (mid with gas_obs := []) /\
    MAP FDOM es.scopes = MAP FDOM (mid with gas_obs := []).scopes /\
    !right tv fin u.
      gas_marked_exec F (ctx,func) (eval_expr cx e2)
        (mid with gas_obs := [],t) right (INL tv) fin (OK u) /\
      vv_post ctx func cenv cx e2 (mid with gas_obs := []) s1 sm t
        (fin with gas_obs := []) tv vv u /\
      u.vs_current_bb = sm.cs_current_bb /\ u.vs_inst_idx = LENGTH sm.cs_current_insts ==>
      ?v2 suffix last q v.
        (!tail. read_result cx tv (fin with gas_obs := tail) =
          (INL v2,fin with gas_obs := tail)) /\
        gas_marked_exec F (ctx,func)
          (\ee. (bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 ee,ee))
          (fin with gas_obs := [],u) suffix (INL v) last (OK q) /\
        vv_post ctx func cenv cx e2 (mid with gas_obs := []) s1 sm t
          (last with gas_obs := []) tv vv q /\
        expr_val_rel cx ann v out q /\
        expr_val_at cenv cx ann sa ct (last with gas_obs := []) v out q /\
        q.vs_current_bb = ct.cs_current_bb /\ q.vs_inst_idx = LENGTH ct.cs_current_insts) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (eval_expr cx (Builtin ann (Bop bop) [e1;e2])) (read_result cx)) (es,s0)
    (\res ee q. ?v. res = INL v /\
      expr_post ctx func cenv cx (Builtin ann (Bop bop) [e1;e2])
        es sa ct s0 ee v out q /\
      q.vs_current_bb = ct.cs_current_bb /\ q.vs_inst_idx = LENGTH ct.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `gas_admissible (bind (eval_expr cx e1) (read_result cx)) expr_res_ok es` by
    metis_tac[bop_first_admissible] >>
  qpat_x_assum `expr_sim _ _ _ _ _ e1 _`
    (mp_tac o REWRITE_RULE [exprSimDefsTheory.expr_sim_def]) >>
  disch_then (qspecl_then [`sa`, `s1`, `x`, `s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >> strip_tac
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gasSummaryTheory.gas_summary_at_def])
      >- suspend "left_normal"
      >> suspend "left_exit") >>
  suspend "left_exempt"
QED

Resume rest_word_mixed_outcome[left_exit]:
  Cases_on `res` >- gvs[] >>
  rename1 `gas_marked_exec _ _ _ _ _ (INR exc) _ _` >>
  qexists `marks` >> disj1_tac >> simp[gasSummaryTheory.gas_summary_at_def] >>
  qexistsl [`INR exc`, `es_end`, `r`] >> conj_tac
  >- (pure_once_rewrite_tac[REWRITE_RULE [ETA_AX] eval_expr_bop_bind] >>
      irule gasSummaryComposeTheory.gas_marked_exec_bind_exception >> first_assum ACCEPT_TAC) >>
  disj2_tac >> gnvs[]
QED

Resume rest_word_mixed_outcome[left_exempt]:
  qexists `marks` >> disj2_tac >>
  drule (REWRITE_RULE [ETA_AX] bop_first_exempt_cert) >> metis_tac[]
QED

Resume rest_word_mixed_outcome[left_normal]:
  qpat_x_assum `(\res ee t. _) _ _ _` (strip_assume_tac o BETA_RULE) >>
  gnvs[] >> rename1 `expr_post _ _ _ _ e1 _ _ _ _ _ v1 _ t` >>
  qpat_x_assum `!left v1 mid t. _` drule_all >> strip_tac >>
  `stmt_state_rel ctx func cenv cx (es_end with gas_obs := []) t` by
    fs[loweringPostsTheory.expr_post_def] >>
  `~t.vs_halted` by
    metis_tac[gasSummaryTheory.gas_marked_exec_def,
      fragGasModeTheory.gas_marked_path_exec, fragGasPathTheory.gas_path_normal] >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ e2 _`
    (mp_tac o REWRITE_RULE [exprSimDefsTheory.expr_vv_sim_def]) >>
  disch_then (qspecl_then [`s1`, `sm`, `vv`, `t`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >> strip_tac
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gasSummaryTheory.gas_summary_at_def])
      >- suspend "right_normal"
      >> suspend "right_exit") >>
  suspend "right_exempt"
QED

Resume rest_word_mixed_outcome[right_exit]:
  Cases_on `res` >- gvs[] >>
  rename1 `gas_marked_exec _ _ _ _ _ (INR exc) _ _` >>
  qexists `marks ++ marks'` >> disj1_tac >>
  simp[gasSummaryTheory.gas_summary_at_def] >>
  qexistsl [`INR exc`, `es_end'`, `r`] >> conj_tac
  >- (pure_once_rewrite_tac[REWRITE_RULE [ETA_AX] eval_expr_bop_bind] >>
      irule gasSummaryComposeTheory.gas_marked_exec_bind_normal >>
      qpat_assum `gas_marked_exec _ _ _ _ _ (INL v1) _ _` (irule_at Any) >>
      BETA_TAC >> irule gasSummaryComposeTheory.gas_marked_exec_bind_exception >>
      irule gasSummaryComposeTheory.gas_marked_exec_bind_exception >> first_assum ACCEPT_TAC) >>
  disj2_tac >> Cases_on `exc` >> Cases_on `r` >>
  gvs[exprSimDefsTheory.expr_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >> gvs[exprSimDefsTheory.expr_exit_def]
QED
Resume rest_word_mixed_outcome[right_exempt]:
  qexists `marks ++ marks'` >> disj2_tac >>
  irule_at Any rest_word_raw_second_exempt_cert >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any)
QED
Resume rest_word_mixed_outcome[right_normal]:
  qpat_x_assum `(\res ee t'. _) _ _ _` (strip_assume_tac o BETA_RULE) >>
  gnvs[] >>
  qpat_x_assum `!right tv fin u. _` drule_all >> strip_tac >>
  `expr_post ctx func cenv cx (Builtin ann (Bop bop) [e1;e2])
     es sa ct s0 (last with gas_obs := []) v out q` by
    (irule rest_word_mixed_post >>
     qpat_assum `expr_post _ _ _ _ e1 _ _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `vv_post _ _ _ _ e2 _ _ _ _ _ _ _ q` (irule_at Any) >> simp[]) >>
  qexists `marks ++ marks' ++ suffix` >> disj1_tac >>
  irule rest_word_mixed_tail_summary >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[]
QED
Finalise rest_word_mixed_outcome
