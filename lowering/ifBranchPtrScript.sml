Theory ifBranchPtr
Ancestors
  ifGhostPtr ifJumpPtr fragGasPathPtr bodyPtrDefs stmtSimIfProps gasSummaryComposePtr
  emitHelperProps exprLoweringProps stmtSimProps stmtSimDefs loweringPosts compileEnv vyperState
  vyperInterpreter finite_map venomState vyperStorageFootprint vyperStorageBackend gasStorage vyperStorageTrace
  vyperEvalPreservesScopes
  fragExec

(* This names exactly stmt_frag_ptr's normal post.  Scope cleanup and
   optional joins repeatedly transform this same post, so naming it avoids
   repeating its existential environment and two frame clauses in each
   boundary interface.  It imposes no additional invariant. *)
Definition stmt_post_ptr_def:
  stmt_post_ptr H d ctx func cx lctx cenv cenv' sa sb s0 G0 tn0 res ee G tn t <=>
    ?cenv''.
      stmt_lands lctx sb res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv') /\
      cenv_top_ext cenv cenv'' ee.scopes /\
      stmt_state_rel H ctx func cenv'' cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      ghost_inv H d cenv'' cx ee G tn t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
             lookup_var x t = SOME w) /\
      (!x. not_fresh_at sa x ==>
           FLOOKUP G x = FLOOKUP G0 x /\
           op_taint tn (Var x) = op_taint tn0 (Var x))
End

Theorem if_branch_post_pop_ptr:
  stmt_post_ptr H d ctx func cx lctx cenv cenv' sa sb s0 G0 tn0 res ee G tn t /\
  ee.scopes = sc :: rest /\
  (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE) ==>
  stmt_post_ptr H d ctx func cx lctx cenv cenv sa sb s0 G0 tn0 res
    (ee with scopes := rest) G tn t
Proof
  rewrite_tac[stmt_post_ptr_def] >> strip_tac >>
  qexists_tac `cenv` >> simp[cenv_top_ext_refl] >> rpt conj_tac
  >~ [`storage_well_formed_on _ (ee with scopes := rest) _`]
  >- fs[storage_well_formed_on_def, get_storage_scopes]
  >~ [`stmt_state_rel _ _ _ _ _ (ee with scopes := rest) _`]
  >- (irule stmt_state_rel_pop_top_ext >>
      conj_tac >- (qexists_tac `sc` >> simp[]) >>
      qexists_tac `cenv''` >> simp[]) >>
  irule if_ghost_inv_pop >> conj_tac
  >- (qexists_tac `sc` >> simp[]) >>
  qexists_tac `cenv''` >> simp[]
QED

Theorem if_branch_marked_cleanup_ptr:
  gas_marked_exec_ptr D (ctx,func) PG (eval_stmts cx ss)
    (es with scopes := FEMPTY :: es.scopes,s0,G0,tn0) marks res ee G tn r /\
  ~s0.vs_halted /\ ee.scopes = sc :: rest ==>
  gas_marked_exec_ptr D (ctx,func) PG
    (ignore_bind push_scope (finally (eval_stmts cx ss) pop_scope))
    (es,s0,G0,tn0) marks res (ee with scopes := rest) G tn r
Proof
  strip_tac >>
  `gas_marked_exec_ptr D (ctx,func) PG (finally (eval_stmts cx ss) pop_scope)
     (es with scopes := FEMPTY :: es.scopes,s0,G0,tn0) marks res
     (ee with scopes := rest) G tn r` by
    (irule gas_marked_exec_ptr_finally >> qexists_tac `ee` >>
     simp[pop_scope_def, return_def, evaluation_state_component_equality]) >>
  `!st. st with scopes updated_by CONS FEMPTY =
         st with scopes := FEMPTY :: st.scopes` by
    simp[evaluation_state_component_equality] >>
  gvs[gas_marked_exec_ptr_def] >> gen_tac >>
  simp[ignore_bind_def, bind_def, push_scope_def, return_def]
QED

Theorem if_branch_outcome_cleanup_ptr:
  gas_outcome_ptr D (cx_tops cx) (ctx,func) PG cx st0 (eval_stmts cx ss)
    (es with scopes := FEMPTY :: es.scopes,s0,G0,tn0)
    (\H. stmt_post_ptr H d ctx func cx lctx cenv cenv' sa sb s0 G0 tn0)
    (\H res ee gt r. !tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
  es.gas_obs = [] /\ ~s0.vs_halted ==>
  gas_outcome_ptr D (cx_tops cx) (ctx,func) PG cx st0
    (ignore_bind push_scope (finally (eval_stmts cx ss) pop_scope)) (es,s0,G0,tn0)
    (\H. stmt_post_ptr H d ctx func cx lctx cenv cenv sa sb s0 G0 tn0)
    (\H res ee gt r. !tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r)
Proof
  rewrite_tac[gas_outcome_ptr_def, gas_summary_ptr_at_def] >> BETA_TAC >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      qpat_x_assum `gas_bad_storage_at _ _ _ _ _ _` mp_tac >>
      pure_rewrite_tac[gas_bad_storage_at_def] >> strip_tac >> gen_tac >>
      first_x_assum (qspec_then `tail` mp_tac) >>
      `!X. (es with scopes := FEMPTY :: es.scopes) with gas_obs := X =
           (es with gas_obs := X) with scopes := FEMPTY :: (es with gas_obs := X).scopes` by
        simp[evaluation_state_component_equality] >>
      pop_assum (fn th => pure_rewrite_tac[th]) >>
      qabbrev_tac `sx = es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail` >>
      `!st. st with scopes updated_by CONS FEMPTY =
            st with scopes := FEMPTY :: st.scopes` by
        simp[evaluation_state_component_equality] >>
      simp[ignore_bind_def, bind_def, push_scope_def, return_def, finally_def] >>
      Cases_on `eval_stmts cx ss (sx with scopes := FEMPTY :: sx.scopes)` >>
      rename1 `_ = (rr,st1)` >> Cases_on `rr` >>
      simp[pop_scope_def, ignore_bind_def, bind_def, return_def, raise_def] >>
      Cases_on `st1.scopes` >> simp[])
  >- (`?sc rest. es_end.scopes = sc :: rest /\
         (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE)` by
        (qpat_assum `!tail. eval_stmts _ _ _ = _` (qspec_then `[]` assume_tac) >>
         drule eval_stmts_preserves_scopes_dom >>
         simp[preserves_scopes_dom_def] >> strip_tac >>
         Cases_on `es_end.scopes` >> gvs[] >> rpt strip_tac >>
         drule eval_stmts_new_in_head_not_in_tail >> simp[]) >>
      `!tail. finally (eval_stmts cx ss) pop_scope
        ((es with scopes := FEMPTY :: es.scopes) with
          gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
        (res,(es_end with scopes := rest) with gas_obs := tail)` by
        (gen_tac >> simp[finally_def] >> Cases_on `res` >>
         simp[ignore_bind_def, bind_def, pop_scope_def, return_def, raise_def]) >>
      qexists_tac `marks` >> disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`, `es_end with scopes := rest`, `G`, `tn`, `r`] >>
      conj_tac
      >- (`!st. st with scopes updated_by CONS FEMPTY =
                st with scopes := FEMPTY :: st.scopes` by
            simp[evaluation_state_component_equality] >>
          gen_tac >> simp[ignore_bind_def, bind_def, push_scope_def, return_def] >>
          qpat_x_assum `!tail. finally _ _ _ = _` (qspec_then `tail` mp_tac) >>
          simp[evaluation_state_component_equality]) >>
      gen_tac >> strip_tac >>
      qpat_x_assum `!H. valid_horizon _ _ _ _ ==> _` (qspec_then `H` mp_tac) >>
      impl_tac >- fs[] >> strip_tac >> simp[]
      >- (disj1_tac >> simp[] >> irule if_branch_post_pop_ptr >> simp[] >>
          metis_tac[]) >>
      disj2_tac >> gvs[stmt_exit_ptr_def]) >>
  drule if_branch_cert_scopes >> strip_tac >>
  qexists_tac `marks` >> disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`, `ee with scopes := rest`, `leaf`, `finish'`] >>
  irule eval_stmt_if_scoped_cert >> simp[if_push_scope_marked] >>
  `es with <|scopes := FEMPTY :: es.scopes; gas_obs := []|> =
   es with scopes := FEMPTY :: es.scopes` by
    simp[evaluation_state_component_equality] >> simp[]
QED

Theorem if_branch_post_to_exit_ptr:
  stmt_post_ptr H d ctx func cx lctx cenv cenv sa last s0 G0 tn0 res ee G tn t /\
  ~ctx_has_dalloca ctx /\
  (~block_is_terminated last ==>
    emit_inst JMP [Label xl] [] last = ((),after) /\
    fn_has_code last after func /\
    sb.cs_current_bb = xl /\ sb.cs_current_insts = []) ==>
  ?u. u = (if res = INL () then jump_to xl t else t) /\
      gas_path_ptr D 0 ctx func PG G tn t 0 G tn (OK u) /\
      stmt_post_ptr H d ctx func cx lctx cenv cenv sa sb s0 G0 tn0 res ee G tn u
Proof
  strip_tac >> Cases_on `res = INL ()`
  >- (gvs[] >>
      `~block_is_terminated last` by fs[stmt_post_ptr_def] >>
      `t.vs_current_bb = last.cs_current_bb /\
       t.vs_inst_idx = LENGTH last.cs_current_insts /\ ~t.vs_halted` by
        fs[stmt_post_ptr_def, stmt_lands_def] >>
      `gas_path_ptr D 0 ctx func PG G tn t 0 G tn (OK (jump_to xl t))` by
        (irule if_emit_jump_zero_path_ptr >> simp[] >>
         qexistsl_tac [`last`, `after`] >>
         fs[] >> drule emit_inst_extends >> simp[]) >>
      simp[] >>
      qpat_x_assum `stmt_post_ptr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
      simp[stmt_post_ptr_def] >> strip_tac >>
      `ghost_inv H d cenv cx ee G tn (jump_to xl t)` by
        metis_tac[if_ghost_inv_jump] >>
      gvs[stmt_lands_def, stmt_state_rel_jump_to,
          block_is_terminated_def, jump_to_def, lookup_var_def]) >>
  qexists_tac `t` >> simp[] >>
  conj_tac >- (fs[stmt_post_ptr_def] >> metis_tac[gas_path_ptr_rules]) >>
  gvs[stmt_post_ptr_def, stmt_lands_def] >> metis_tac[]
QED

Theorem if_branch_outcome_to_exit_ptr:
  gas_outcome_ptr D (cx_tops cx) (ctx,func) PG cx st0 source (es,s0,G0,tn0)
    (\H. stmt_post_ptr H d ctx func cx lctx cenv cenv sa last s0 G0 tn0) R /\
  ~ctx_has_dalloca ctx /\
  (~block_is_terminated last ==>
    emit_inst JMP [Label xl] [] last = ((),after) /\
    fn_has_code last after func /\
    sb.cs_current_bb = xl /\ sb.cs_current_insts = []) ==>
  gas_outcome_ptr D (cx_tops cx) (ctx,func) PG cx st0 source (es,s0,G0,tn0)
    (\H. stmt_post_ptr H d ctx func cx lctx cenv cenv sa sb s0 G0 tn0) R
Proof
  rewrite_tac[gas_outcome_ptr_def, gas_summary_ptr_at_def] >> BETA_TAC >>
  strip_tac >> qexists_tac `marks`
  >- (disj1_tac >> simp[])
  >- (disj2_tac >> disj1_tac >>
      reverse (Cases_on `?t. r = OK t`)
      >- (qexistsl_tac [`res`,`es_end`,`G`,`tn`,`r`] >> simp[] >> metis_tac[]) >>
      pop_assum strip_assume_tac >> gvs[exit_result_def] >>
      qexistsl_tac [`res`,`es_end`,`G`,`tn`,
        `OK (if res = INL () then jump_to xl t else t)`] >> asm_rewrite_tac[] >>
      qx_gen_tac `H` >> strip_tac >>
      qpat_x_assum `!H. valid_horizon _ _ _ _ ==> _`
        (drule_then strip_assume_tac) >>
      drule_all if_branch_post_to_exit_ptr >>
      disch_then (qspecl_then [`PG`,`D H`] strip_assume_tac) >> gvs[] >>
      `LENGTH marks = LENGTH marks + 0` by simp[] >> pop_assum SUBST1_TAC >>
      irule gas_path_ptr_then >> goal_assum (drule_at Any) >> simp[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

Theorem if_branch_outcome_ptr:
  gas_outcome_ptr D (cx_tops cx) (ctx,func) PG cx st0 (eval_stmts cx ss)
    (es with scopes := FEMPTY :: es.scopes,s0,G0,tn0)
    (\H. stmt_post_ptr H d ctx func cx lctx cenv cenv' sa last s0 G0 tn0)
    (\H res ee gt r. !tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
  es.gas_obs = [] /\ ~s0.vs_halted /\ ~ctx_has_dalloca ctx /\
  (~block_is_terminated last ==>
    emit_inst JMP [Label xl] [] last = ((),after) /\
    fn_has_code last after func /\
    sb.cs_current_bb = xl /\ sb.cs_current_insts = []) ==>
  gas_outcome_ptr D (cx_tops cx) (ctx,func) PG cx st0
    (ignore_bind push_scope (finally (eval_stmts cx ss) pop_scope)) (es,s0,G0,tn0)
    (\H. stmt_post_ptr H d ctx func cx lctx cenv cenv sa sb s0 G0 tn0)
    (\H res ee gt r. !tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r)
Proof
  strip_tac >> irule if_branch_outcome_to_exit_ptr >> simp[] >>
  qexistsl_tac [`after`, `last`, `xl`] >> simp[] >>
  irule if_branch_outcome_cleanup_ptr >> simp[] >> metis_tac[]
QED
