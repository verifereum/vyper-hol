(* Seam 2 joint induction, a family leaf of the stmt step: If. *)
Theory bodyIntCallFamStmtIf
Ancestors
  bodyIntCallJointContract bodyIntCallJointStmtJump
  bodyIntCallJointStmtBoundary bodyIntCallDeclarationRegions
  bodyExprPreFacts exprLoweringProps intCallFrame compileEnv loweringStateRelDefs
  vyperState finite_map list exprSimHypsDefs vyperTypeEvalSoundness
  vyperTypeInvariants vyperTypeSystem vyperTypeCallGraph
  bodyStoragePreservation vyperTypeExprSoundness vyperTypeStoragePreservation
  vyperEvalOutcomeSuffix stmtSimProps loweringPosts bodySim
  fragGasPath emitHelperProps venomState venomInst compileVyper
  stmtSimIfProps gasOutcome gasSummary gasSummaryCompose
  bodyIntCallJointStmtSeq supportedStmts supportedStmtTraverse stmtLowering
  exprSimSource exprSimDefs stmtSimDefs allocLimits gasContext vyperTypeCallStackSoundness

Theorem intcall_joint_res_push_scope:
  intcall_joint_res fp ce env es sa s ==>
  intcall_joint_res fp ce env (es with scopes := FEMPTY :: es.scopes) sa s
Proof
  simp[intcall_joint_res_def, intcall_expr_res_def, stmt_state_rel_push_scope,
       local_region_def, lookup_scopes_def] >>
  strip_tac >> drule expr_sim_inv_push_scope >> metis_tac[]
QED

Theorem intcall_stmt_exit_scopes:
  intcall_stmt_exit fp res (ee with scopes := scopes) r <=>
  intcall_stmt_exit fp res ee r
Proof
  simp[intcall_stmt_exit_def]
QED

(* A statement whose typing leaves the environment unchanged preserves the
   expression invariant even on a control exception. *)
Theorem expr_sim_inv_stmt_same_env:
  supported_program tops /\ get_module_code cx NONE = SOME tops /\
  supported_stmt tops bindings st /\ expr_sim_inv ce cx env es /\
  type_stmt env rt st = SOME env /\
  call_evaluation_safe cx (int_calls_stmt st) /\
  eval_stmt cx st es = (res,ee) ==>
  expr_sim_inv ce cx env ee
Proof
  strip_tac >>
  `contract_storage_well_formed cx ee /\ oracle_storage_ok cx ee /\
   IS_SOME ee.outcomes` by
    (drule_at (Pos (el 4)) (cj 1 eval_stmts_storage_conjs) >>
     disch_then irule >>
     fs[expr_sim_inv_def, runtime_storage_consistent_def,
        runtime_consistent_def] >>
     conj_tac >- (qexistsl [`res`, `es`] >> simp[]) >>
     qexists `bindings` >> simp[]) >>
  `state_well_typed ee /\ accounts_well_typed ee.accounts /\
   env_consistent env cx ee` by
    (drule (cj 1 eval_scc_type_sound_mutual) >>
     disch_then (qspecl_then [`cx`, `es`, `res`, `ee`] mp_tac) >>
     impl_tac >- fs[expr_sim_inv_def] >>
     Cases_on `res` >> simp[] >> metis_tac[]) >>
  `outcomes_accounts_typed ee.outcomes` by
    (rw[outcomes_accounts_typed_def] >>
     drule (cj 1 vyperEvalOutcomeSuffixTheory.eval_outcome_suffix_mutual) >>
     strip_tac >> drule_then irule vyperEvalOutcomeSuffixTheory.outcome_suffix_EVERY >>
     gvs[expr_sim_inv_def, outcomes_accounts_typed_def]) >>
  `popped_keys_indexed ee.scopes` by
    (drule (cj 1 eval_stmts_popped_keys_indexed) >>
     disch_then irule >>
     qexistsl [`cx`, `es`, `res`] >>
     fs[expr_sim_inv_def, runtime_consistent_def]) >>
  fs[expr_sim_inv_def] >> metis_tac[]
QED

(* Dropping a lexical scope restores the outer static compiler interface.
   Its source typing is supplied by semantic preservation, not by restricting
   the arbitrary typing witness of a control-exception endpoint. *)
Theorem intcall_joint_res_pop_top_ext:
  intcall_joint_res fp ce' env' ee sb u /\
  cenv_top_ext ce ce' ee.scopes /\ ee.scopes = sc :: rest /\
  (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE) /\
  expr_sim_inv ce fp.jc_cx env (ee with scopes := rest) /\
  ce_locals_declared ce env /\ locals_alloc_ok ce env /\
  local_ptrs_reserved ce sb /\ same_frame fp.jc_root_ce ce ==>
  intcall_joint_res fp ce env (ee with scopes := rest) sb u
Proof
  strip_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx
     (ee with scopes := rest) u` by
    (irule stmt_state_rel_pop_top_ext >>
     conj_tac >- (qexists `sc` >> simp[]) >>
     qexists `ce'` >> fs[intcall_joint_res_def, intcall_expr_res_def]) >>
  `ce'.ce_return_pc = ce.ce_return_pc /\
   ce'.ce_return_buf = ce.ce_return_buf /\
   ce'.ce_is_ctor = ce.ce_is_ctor /\
   ce'.ce_module_vars = ce.ce_module_vars /\
   ce'.ce_module = ce.ce_module` by
    fs[cenv_top_ext_def, compile_env_component_equality] >>
  `!n p k. local_region ce rest u n p k ==>
           local_region ce' (sc :: rest) u n p k` by
    (rpt strip_tac >>
     irule local_region_pop_scope >> simp[] >>
     fs[local_region_def, cenv_top_ext_def] >>
     metis_tac[optionTheory.NOT_SOME_NONE]) >>
  fs[intcall_joint_res_def, intcall_expr_res_def, ret_pc_ok_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac >-
    (Cases_on `fp.jc_rb` >> fs[return_buf_frame_def] >>
     rename1 `fp.jc_rb = SOME rb` >> PairCases_on `rb` >>
     fs[return_buf_frame_def]) >>
  metis_tac[]
QED

(* Only normal completion takes the branch's trailing JMP.  Break and
   continue have already landed at their loop targets. *)
Theorem intcall_if_branch_join:
  intcall_joint_res fp ce env ee last t /\
  stmt_lands lctx last res t /\ ~t.vs_halted /\
  (res = INL () ==> ~block_is_terminated last) /\
  last.cs_next_var <= sb.cs_next_var /\
  (~block_is_terminated last ==>
    emit_inst JMP [Label xl] [] last = ((),after) /\
    fn_has_code last after fp.jc_func /\
    sb.cs_current_bb = xl /\ sb.cs_current_insts = []) ==>
  ?u. gas_path fp.jc_ctx fp.jc_func t 0 (OK u) /\
      stmt_lands lctx sb res u /\ ~u.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb) /\
      intcall_joint_res fp ce env ee sb u /\
      u.vs_vars = t.vs_vars /\ u.vs_allocas = t.vs_allocas /\
      u.vs_alloca_next = t.vs_alloca_next
Proof
  strip_tac >>
  `intcall_joint_res fp ce env ee sb t` by
    (irule intcall_joint_res_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  Cases_on `res = INL ()`
  >- (fs[] >>
      `t.vs_current_bb = last.cs_current_bb /\
       t.vs_inst_idx = LENGTH last.cs_current_insts` by fs[stmt_lands_def] >>
      `gas_path fp.jc_ctx fp.jc_func t 0 (OK (jump_to xl t))` by
        (irule emit_jump_zero_path >> simp[] >>
         qexistsl [`last`, `after`] >>
         metis_tac[emit_inst_extends]) >>
      qexists `jump_to xl t` >>
      simp[intcall_joint_res_jump_to, stmt_lands_def, jump_to_def,
           block_is_terminated_def]) >>
  qexists `t` >> simp[] >>
  conj_tac >- metis_tac[gas_path_rules] >>
  fs[stmt_lands_def]
QED

(* A scope wrapper with an execution-aware post transformer: unlike the
   ordinary If rule, this interface does not discard resource information. *)
Theorem gas_outcome_scoped_stmts:
  gas_outcome memory tops (ctx,func) (eval_stmts cx ss)
    (es with scopes := FEMPTY :: es.scopes,s0) Q R /\
  es.gas_obs = [] /\ ~s0.vs_halted /\
  (!marks res ee t sc rest.
     gas_marked_exec memory (ctx,func) (eval_stmts cx ss)
       (es with scopes := FEMPTY :: es.scopes,s0) marks res ee (OK t) /\
     Q res (ee with gas_obs := []) t /\ ee.scopes = sc :: rest /\
     (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE) ==>
     Q' res ((ee with scopes := rest) with gas_obs := []) t) /\
  (!res ee r rest. R res ee r ==> R' res (ee with scopes := rest) r) ==>
  gas_outcome memory tops (ctx,func)
    (ignore_bind push_scope (finally (eval_stmts cx ss) pop_scope))
    (es,s0) Q' R'
Proof
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> strip_tac
  >- (rename1 `gas_marked_exec _ _ _ _ marks res ee r` >>
      drule if_branch_marked_scopes >> strip_tac >>
      qexists `marks` >> disj1_tac >>
      qexistsl [`res`, `ee with scopes := rest`, `r`] >>
      conj_tac
      >- (irule if_branch_marked_cleanup >> simp[] >> metis_tac[]) >>
      disj1_tac >> qexists `t` >> simp[] >>
      `ee with <|scopes := rest; gas_obs := []|> =
       ee with <|gas_obs := []; scopes := rest|>` by
        simp[evaluation_state_component_equality] >>
      asm_rewrite_tac[] >>
      first_x_assum irule >> metis_tac[])
  >- (rename1 `gas_marked_exec _ _ _ _ marks res ee r` >>
      drule if_branch_marked_scopes >> strip_tac >>
      qexists `marks` >> disj1_tac >>
      qexistsl [`res`, `ee with scopes := rest`, `r`] >>
      conj_tac
      >- (irule if_branch_marked_cleanup >> simp[] >> metis_tac[]) >>
      disj2_tac >> simp[] >> first_x_assum irule >> simp[]) >>
  rename1 `gas_exempt_cert _ _ _ _ _ marks (err,ee) (leaf,fin)` >>
  drule if_branch_cert_scopes >> strip_tac >>
  qexists `marks` >> disj2_tac >>
  qexistsl [`err`, `ee with scopes := rest`, `leaf`, `fin`] >>
  irule eval_stmt_if_scoped_cert >> simp[if_push_scope_marked] >>
  `es with <|scopes := FEMPTY :: es.scopes; gas_obs := []|> =
   es with scopes := FEMPTY :: es.scopes` by
    simp[evaluation_state_component_equality] >>
  asm_rewrite_tac[]
QED

(* Reservation facts depend on the static environment, not the dynamic
   state.  A continuation can use any frontier that already reserved that
   environment on entry, including a branch-entry frontier. *)
Theorem intcall_joint_res_rebase:
  intcall_joint_res fp ce env es sa s /\
  intcall_joint_res fp ce env ee sb t /\
  sa.cs_next_var <= sc.cs_next_var ==>
  intcall_joint_res fp ce env ee sc t
Proof
  strip_tac >>
  `intcall_joint_res fp ce env es sc s` by
    (irule intcall_joint_res_next_var >> metis_tac[]) >>
  fs[intcall_joint_res_def, intcall_expr_res_def, ret_pc_ok_def] >>
  conj_tac >- metis_tac[] >>
  Cases_on `fp.jc_rb` >> fs[return_buf_frame_def] >>
  rename1 `fp.jc_rb = SOME rb` >> PairCases_on `rb` >>
  gvs[return_buf_frame_def] >> metis_tac[]
QED

(* Typing on control exceptions is recovered from the actual scoped
   execution, not from the branch producer's existential typing witness. *)
Theorem expr_sim_inv_if_branch:
  supported_program tops /\ get_module_code cx NONE = SOME tops /\
  supported_stmt tops bindings (If e ss1 ss2) /\
  expr_sim_inv ce cx env es /\
  type_stmt env rt (If e ss1 ss2) = SOME env /\
  call_evaluation_safe cx (int_calls_stmt (If e ss1 ss2)) /\
  bind (eval_expr cx e) (read_result cx) es = (INL (BoolV b),mid) /\
  eval_stmts cx (if b then ss1 else ss2)
    (mid with scopes := FEMPTY :: mid.scopes) = (res,ee) ==>
  expr_sim_inv ce cx env (ee with scopes := TL ee.scopes)
Proof
  strip_tac >> drule_all eval_stmt_if_selected >> strip_tac >>
  irule expr_sim_inv_stmt_same_env >> goal_assum (drule_at Any) >>
  metis_tac[]
QED

Theorem intcall_if_producer:
  intcall_forced_producer fp e /\ intcall_stmts_producer fp ss1 /\
  intcall_stmts_producer fp ss2 ==>
  intcall_stmts_producer fp [If e ss1 ss2]
Proof
  strip_tac >>
  simp[intcall_stmts_producer_def, eval_stmts_singleton] >>
  rpt gen_tac >> strip_tac >>
  gvs[supported_stmt_def, type_stmt_def, int_calls_stmt_def,
      supported_stmt_expr_exists_def] >>
  qpat_x_assum `stmts_env _ _ _ _ _ = _` mp_tac >>
  simp[stmts_env_singleton, stmt_env_def, declare_stmt_local_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_stmt ce lctx
    (if fp.jc_ret_ty = NoneT then BaseT BoolT else fp.jc_ret_ty)
    (If e ss1 ss2) sa` >>
  rename1 `_ = (u, sm)` >> Cases_on `u` >> simp[] >> strip_tac >> gvs[] >>
  gvs[AllCaseEqs()] >>
  `supported_expr fp.jc_tops e` by
    simp[supportedExprsTheory.supported_expr_def] >>
  `expr_body_pre ce fp.jc_cx env e es` by
    (irule stmt_expr_body_pre >>
     fs[intcall_joint_res_def, intcall_expr_res_def, stmt_exprs_ok_def,
        supported_stmt_expr_exists_def, alloc_limits_stmt_def] >>
     drule supported_expr_body_calls >> strip_tac >>
     fs[body_inv_def, cx_tops_def, AllCaseEqs()] >>
     qexists `[]` >> simp[call_evaluation_safe_def] >>
     fs[intcall_frame_ok_def] >> metis_tac[]) >>
  `!sx op sy. lower_value compile_expr ce (BaseT BoolT) e sx = (op,sy) ==>
       cs_extends sx sy /\ sx.cs_next_var <= sy.cs_next_var` by
    (rpt gen_tac >> disch_tac >>
     drule expr_body_pre_lower_value_word_shape >>
     simp[is_word_type_def] >> disch_then drule >> simp[]) >>
  drule compile_if_code_layout_frontiers >>
  disch_then (qspec_then `fp.jc_func` mp_tac) >>
  (impl_tac >- simp[stmts_env_cs_mono]) >> strip_tac >>
  `gas_admissible (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx))
     expr_res_ok es` by
    (irule if_condition_admissible >> metis_tac[]) >>
  imp_res_tac (GEN_ALL (DISCH_ALL (CONJUNCT1 (UNDISCH
    (iffLR (SPEC_ALL intcall_joint_res_def)))))) >>
  qpat_x_assum `intcall_forced_producer _ _`
    (mp_tac o REWRITE_RULE [intcall_forced_producer_def]) >>
  disch_then drule_all >> strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> strip_tac
  >- suspend "selected"
  >- (gvs[] >> Cases_on `res` >- fs[expr_exit_def] >>
      rename1 `INR ex` >>
      qexists `marks` >> disj1_tac >>
      qexistsl [`INR ex`, `es_end`, `r`] >> conj_tac
      >- (rewrite_tac[eval_stmt_if_forced] >>
          irule gas_marked_exec_bind_exception >> simp[]) >>
      disj2_tac >> simp[intcall_stmt_exit_def] >>
      metis_tac[expr_exit_INR_type]) >>
  qexists `marks` >> disj2_tac >>
  drule eval_stmt_if_condition_cert >> metis_tac[]
QED

Resume intcall_if_producer[selected]:
  gvs[] >>
  `post_value_type ce e = BaseT BoolT` by
    metis_tac[post_value_type_word, is_word_type_def] >>
  `?b. v = BoolV b` by
    (spose_not_then assume_tac >>
     `v <> BoolV T /\ v <> BoolV F` by metis_tac[] >>
     qpat_x_assum `gas_admissible (eval_stmt _ _) _ _` mp_tac >>
     rewrite_tac[gas_admissible_def] >>
     disch_then (qspecl_then [`gas_explicit marks s.vs_gas_readings`,
       `INR (Error (TypeError "not BoolV"))`, `es_end with gas_obs := []`] mp_tac) >>
     simp[stmt_res_ok_def] >>
     qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` assume_tac) >>
     fs[] >> rewrite_tac[eval_stmt_if_forced] >>
     pure_once_rewrite_tac[bind_def] >> simp[raise_def]) >>
  gvs[] >>
  qpat_x_assum `!b. ?entry last after. _`
    (qspec_then `b` strip_assume_tac) >>
  `!tail. bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)
     (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
     (INL (BoolV b), es_end with gas_obs := tail)` by
    fs[gas_marked_exec_def] >>
  `gas_admissible (eval_stmts fp.jc_cx (if b then ss1 else ss2))
     (stmt_res_ok lctx) (es_end with scopes := FEMPTY :: es_end.scopes)` by
    (drule_all if_branch_admissible >> simp[]) >>
  `eval_operand op t = SOME (val_to_w256 (BoolV b))` by
    fs[expr_val_rel_def, vyperValueTheory.evaluate_type_def,
       is_word_type_def, valueEncodingTheory.typed_val_to_w256_def] >>
  `gas_path fp.jc_ctx fp.jc_func t 0 (OK (jump_to (if b then tl else el) t))` by
    (irule assert_jnz_zero_path >>
     drule emit_inst_extends >> strip_tac >>
     fs[intcall_expr_cont_def] >>
     qexistsl [`op`, `pre`, `post`] >>
     simp[valueEncodingTheory.val_to_w256_def]) >>
  suspend "branch_start"
QED

Resume intcall_if_producer[branch_start]:
  `intcall_stmts_producer fp (if b then ss1 else ss2)` by
    (Cases_on `b` >> simp[]) >>
  `intcall_joint_res fp ce env
      ((es_end with gas_obs := []) with scopes := FEMPTY :: es_end.scopes)
      entry (jump_to (if b then tl else el) t)` by
    (`intcall_joint_res fp ce env (es_end with gas_obs := []) entry t` by
       (fs[intcall_expr_cont_def] >>
        imp_res_tac (GEN_ALL (DISCH_ALL (CONJUNCT2 (UNDISCH
          (iffLR (SPEC_ALL intcall_joint_res_def)))))) >>
        imp_res_tac (GEN_ALL (iffRL (SPEC_ALL intcall_joint_res_def))) >>
        irule intcall_joint_res_rebase >> metis_tac[]) >>
     drule intcall_joint_res_push_scope >>
     simp[intcall_joint_res_jump_to]) >>
  qmatch_asmsub_abbrev_tac `compile_stmts ce lctx cty branch entry` >>
  `?branch_ce. stmts_env ce lctx cty branch entry = (branch_ce,last)` by
    (qexists `FST (stmts_env ce lctx cty branch entry)` >>
     qpat_x_assum `compile_stmts ce lctx cty branch entry = _` mp_tac >>
     rewrite_tac[stmtSimPropsTheory.compile_stmts_env] >>
     Cases_on `stmts_env ce lctx cty branch entry` >> simp[]) >>
  `?branch_env. type_stmts env fp.jc_ret_ty branch = SOME branch_env` by
    (Cases_on `b` >> fs[Abbr `branch`, optionTheory.IS_SOME_EXISTS]) >>
  qpat_x_assum `intcall_stmts_producer fp branch`
    (mp_tac o REWRITE_RULE [intcall_stmts_producer_def]) >>
  disch_then (qspecl_then [`bindings`, `ce`, `branch_ce`, `env`, `branch_env`,
    `lctx`, `(es_end with gas_obs := []) with scopes := FEMPTY :: es_end.scopes`,
    `entry`, `last`, `jump_to (if b then tl else el) t`] mp_tac) >>
  impl_tac >- suspend "branch_pre" >>
  strip_tac >> suspend "branch_outcome"
QED

Resume intcall_if_producer[branch_pre]:
  `EVERY (stmt_exprs_ok ce) ss1 /\ EVERY (stmt_exprs_ok ce) ss2` by
    fs[stmts_exprs_ok_EVERY, stmt_exprs_ok_def,
       supported_stmt_expr_exists_def, alloc_limits_stmt_def,
       stmt_valued_return_def] >>
  fs[intcall_expr_cont_def] >>
  simp[block_is_terminated_def, jump_to_def] >>
  Cases_on `b` >> gvs[Abbr `branch`, AllCaseEqs()] >>
  qpat_x_assum `IS_SOME (case _ of NONE => NONE | SOME _ => _)` mp_tac >>
  simp[optionTheory.IS_SOME_EXISTS, AllCaseEqs()] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  qpat_x_assum `gas_admissible (eval_stmts _ _) _ _` mp_tac >>
  simp[gas_admissible_def]
QED

Resume intcall_if_producer[branch_outcome]:
  `gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (ignore_bind push_scope (finally (eval_stmts fp.jc_cx branch) pop_scope))
    (es_end with gas_obs := [], jump_to (if b then tl else el) t)
    (\res ee u. stmt_lands lctx last res u /\ ~u.vs_halted /\
      (res = INL () ==> ~block_is_terminated last) /\
      intcall_joint_res fp ce env ee last u /\
      (!x w. not_fresh_at entry x /\
        lookup_var x (jump_to (if b then tl else el) t) = SOME w ==>
        lookup_var x u = SOME w) /\
      (!aid z. FLOOKUP (jump_to (if b then tl else el) t).vs_allocas aid = SOME z ==>
        FLOOKUP u.vs_allocas aid = SOME z) /\
      (jump_to (if b then tl else el) t).vs_alloca_next <= u.vs_alloca_next)
    (intcall_stmt_exit fp)` by
    (qmatch_asmsub_abbrev_tac `gas_outcome _ _ _ _ (pushed,s0) _ _` >>
     `pushed = (es_end with gas_obs := []) with
        scopes := FEMPTY :: (es_end with gas_obs := []).scopes` by
       simp[Abbr `pushed`, evaluation_state_component_equality] >>
     qpat_x_assum `gas_outcome _ _ _ _ (pushed,s0) _ _` mp_tac >>
     asm_rewrite_tac[] >> disch_tac >>
     drule_at (Pos (el 1)) gas_outcome_scoped_stmts >>
     disch_then irule >>
     reverse conj_tac
     >- (simp[NoAsms, intcall_stmt_exit_scopes] >>
         qpat_x_assum `intcall_expr_cont _ _ _ _ _ _ _ _ _`
           (mp_tac o cj 2 o REWRITE_RULE [intcall_expr_cont_def]) >>
         simp[NoAsms, Abbr `s0`, jump_to_def]) >>
     rpt strip_tac >> simp[] >> suspend "branch_pop") >>
  suspend "scoped_outcome"
QED

Resume intcall_if_producer[branch_pop]:
  qpat_x_assum `(\res ee u. _) _ _ _` mp_tac >>
  BETA_TAC >> strip_tac >>
  simp[] >>
  `ee with <|scopes := rest; gas_obs := []|> =
   (ee with gas_obs := []) with scopes := rest` by
    simp[evaluation_state_component_equality] >>
  pop_assum (fn th => pure_once_rewrite_tac[th]) >>
  irule intcall_joint_res_pop_top_ext >>
  `ce_locals_declared ce env /\ locals_alloc_ok ce env /\
   local_ptrs_reserved ce sa /\ same_frame fp.jc_root_ce ce` by
    (qpat_x_assum `intcall_joint_res fp ce env es sa s`
      (strip_assume_tac o REWRITE_RULE [intcall_joint_res_def, intcall_expr_res_def]) >> simp[]) >>
  `local_ptrs_reserved ce last` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >>
     qpat_x_assum `stmts_env ce lctx cty branch entry = _` mp_tac >>
     mp_tac (REWRITE_RULE [fragExecTheory.cs_mono_def] stmts_env_cs_mono) >>
     disch_then (qspecl_then [`ce`, `lctx`, `cty`, `branch`] assume_tac) >>
     strip_tac >> first_x_assum drule >> simp[]) >>
  simp[] >>
  reverse conj_tac >-
    (qexistsl [`ce''`, `env''`] >> simp[] >>
     qpat_x_assum `cenv_top_ext _ _ _` mp_tac >> simp[]) >>
  `expr_sim_inv ce fp.jc_cx env
     ((ee with gas_obs := []) with scopes := TL (ee with gas_obs := []).scopes)`
    suffices_by simp[] >>
  qpat_x_assum `gas_marked_exec _ _ (eval_stmts _ _) _ _ _ _ _`
    (mp_tac o cj 1 o REWRITE_RULE [gas_marked_exec_def]) >>
  disch_then (qspec_then `[]` mp_tac) >>
  simp[NoAsms] >> strip_tac >>
  qpat_x_assum `!tail. bind _ _ _ = _`
    (qspec_then `gas_explicit marks' s0.vs_gas_readings` assume_tac) >>
  drule_at (Pos (el 7)) expr_sim_inv_if_branch >>
  disch_then (assume_tac o SIMP_RULE (srw_ss()) []) >>
  qpat_x_assum `eval_stmts _ branch _ = _` mp_tac >>
  simp[NoAsms, Abbr `branch`] >> disch_tac >>
  first_x_assum (drule_at (Pos (el 7))) >>
  disch_then (assume_tac o SIMP_RULE (srw_ss()) []) >>
  first_x_assum irule >>
  conj_tac >- (qexists `fp.jc_ret_ty` >> simp[type_stmt_def]) >>
  `expr_sim_inv ce fp.jc_cx env es` by
    (qpat_x_assum `intcall_joint_res fp ce env es sa s`
       (mp_tac o cj 2 o REWRITE_RULE [intcall_joint_res_def, intcall_expr_res_def]) >> simp[]) >>
  simp[] >> reverse conj_tac >-
    (qexistsl [`bindings`, `fp.jc_tops`] >>
     qpat_x_assum `body_inv _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [body_inv_def]) >>
     simp[cx_tops_def, supported_stmt_def]) >>
  simp[int_calls_stmt_def, call_evaluation_safe_def] >>
  qexistsl [`fp.jc_edges`, `fp.jc_owner`, `fp.jc_ancestors`] >>
  qpat_x_assum `intcall_frame_ok fp`
    (strip_assume_tac o REWRITE_RULE [intcall_frame_ok_def]) >>
  simp[]
QED

Resume intcall_if_producer[scoped_outcome]:
  `gas_marked_exec F (fp.jc_ctx,fp.jc_func)
     (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx))
     (es,s) marks (INL (BoolV b)) es_end
     (OK (jump_to (if b then tl else el) t))` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ marks _ _ _` mp_tac >>
     simp[gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def] >>
     strip_tac >> simp[] >> drule_all gas_path_then >> simp[]) >>
  qpat_x_assum `gas_outcome _ _ _ (ignore_bind _ _) _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> strip_tac
  >- suspend "scoped_normal"
  >- suspend "scoped_exit"
  >> suspend "scoped_cert"
QED

Resume intcall_if_producer[scoped_normal]:
  qpat_x_assum `(\res ee u. _) _ _ _` mp_tac >> BETA_TAC >> strip_tac >>
  gvs[] >>
  drule_at (Pos (el 1)) intcall_if_branch_join >>
  disch_then (qspecl_then [`xl`, `sb`, `res`, `lctx`, `after`] mp_tac) >>
  (impl_tac >- (Cases_on `block_is_terminated last` >> gvs[])) >> strip_tac >>
  qexists `marks ++ marks'` >> disj1_tac >>
  qexistsl [`res`, `es_end'`, `OK u`] >> conj_tac
  >- suspend "normal_execution" >>
  disj1_tac >> simp[] >> qexistsl [`ce`, `env`] >>
  simp[cenv_top_ext_refl] >> suspend "normal_preservation"
QED

Resume intcall_if_producer[scoped_exit]:
  qexists `marks ++ marks'` >> disj1_tac >>
  qexistsl [`res`, `es_end'`, `r`] >> simp[] >>
  rewrite_tac[eval_stmt_if_forced] >>
  irule gas_marked_exec_bind_normal >>
  qexistsl [`es_end`, `jump_to (if b then tl else el) t`, `BoolV b`] >>
  simp[] >> Cases_on `b` >> fs[Abbr `branch`]
QED

Resume intcall_if_producer[scoped_cert]:
  rename1 `gas_exempt_cert _ _ _ _ _ marks' (err,ee) (leaf,fin)` >>
  qexists `marks ++ marks'` >> disj2_tac >>
  qexistsl [`err`, `ee`, `leaf`, `fin`] >>
  rewrite_tac[eval_stmt_if_forced] >>
  pure_once_rewrite_tac[ignore_bind_def] >>
  pure_once_rewrite_tac[vyperStateTheory.bind_assoc] >>
  irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
  qexistsl [`es_end`, `jump_to (if b then tl else el) t`, `BoolV b`] >>
  simp[] >> Cases_on `b` >> fs[Abbr `branch`, GSYM ignore_bind_def]
QED

Resume intcall_if_producer[normal_execution]:
  `gas_marked_exec F (fp.jc_ctx,fp.jc_func)
    (ignore_bind push_scope (finally (eval_stmts fp.jc_cx branch) pop_scope))
    (es_end with gas_obs := [],jump_to (if b then tl else el) t)
    marks' res es_end' (OK u)` by
    (qpat_x_assum `gas_marked_exec _ _ (ignore_bind _ _) _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def] >>
     strip_tac >> simp[] >> drule_all gas_path_then >> simp[]) >>
  rewrite_tac[eval_stmt_if_forced] >>
  irule gas_marked_exec_bind_normal >>
  qexistsl [`es_end`, `jump_to (if b then tl else el) t`, `BoolV b`] >>
  simp[] >> Cases_on `b` >> fs[Abbr `branch`]
QED

Resume intcall_if_producer[normal_preservation]:
  qpat_x_assum `intcall_expr_cont _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [intcall_expr_cont_def]) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at entry x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
      `lookup_var x t = SOME w` by metis_tac[] >>
      `lookup_var x t' = SOME w` by metis_tac[] >>
      fs[lookup_var_def]) >>
  conj_tac >- (fs[jump_to_def] >> metis_tac[]) >>
  gvs[jump_to_def] >> decide_tac
QED

Finalise intcall_if_producer

Theorem intcall_if_stmt_step:
  (!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
       intcall_map_producer fp e) /\
  (!ss. list_size stmt_size ss < stmt_size st ==>
         intcall_stmts_producer fp ss) /\
  (?e s1 s2. st = If e s1 s2) ==>
  intcall_stmts_producer fp [st]
Proof
  strip_tac >> gvs[] >>
  irule intcall_if_producer >> simp[] >>
  conj_tac >> first_x_assum irule >> simp[vyperASTTheory.stmt_size_def]
QED
