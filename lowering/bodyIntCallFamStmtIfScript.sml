(* Seam 2 joint induction, a family leaf of the stmt step: If. *)
Theory bodyIntCallFamStmtIf
Ancestors
  bodyIntCallJointContract bodyIntCallJointStmtJump
  bodyIntCallJointStmtBoundary bodyIntCallDeclarationRegions
  bodyExprPreFacts exprLoweringProps intCallFrame compileEnv
  vyperState finite_map list exprSimHypsDefs vyperTypeEvalSoundness
  vyperTypeInvariants vyperTypeSystem vyperTypeCallGraph
  bodyStoragePreservation vyperTypeExprSoundness vyperTypeStoragePreservation
  vyperEvalOutcomeSuffix stmtSimProps loweringPosts bodySim
  fragGasPath emitHelperProps venomState venomInst compileVyper
  stmtSimIfProps gasOutcome gasSummary gasSummaryCompose

Theorem intcall_joint_res_push_scope:
  intcall_joint_res fp ce env es sa s ==>
  intcall_joint_res fp ce env (es with scopes := FEMPTY :: es.scopes) sa s
Proof
  simp[intcall_joint_res_def, stmt_state_rel_push_scope,
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
     qexists `ce'` >> fs[intcall_joint_res_def]) >>
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
  fs[intcall_joint_res_def, ret_pc_ok_def] >>
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

Theorem intcall_if_stmt_step:
  (!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
       intcall_map_producer fp e) /\
  (!ss. list_size stmt_size ss < stmt_size st ==>
         intcall_stmts_producer fp ss) /\
  (?e s1 s2. st = If e s1 s2) ==>
  intcall_stmts_producer fp [st]
Proof
  cheat
QED
