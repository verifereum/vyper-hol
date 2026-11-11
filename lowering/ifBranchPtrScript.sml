Theory ifBranchPtr
Ancestors
  ifGhostPtr ifJumpPtr fragGasPathPtr bodyPtrDefs stmtSimIfProps gasSummaryComposePtr
  emitHelperProps exprLoweringProps stmtSimProps stmtSimDefs loweringPosts compileEnv vyperState
  vyperInterpreter finite_map venomState

(* This names exactly stmt_frag_ptr's normal post.  Scope cleanup and
   optional joins repeatedly transform this same post, so naming it avoids
   repeating its existential environment and two frame clauses in each
   boundary interface.  It imposes no additional invariant. *)
Definition stmt_post_ptr_def:
  stmt_post_ptr d ctx func cx lctx cenv cenv' sa sb s0 G0 tn0 res ee G tn t <=>
    ?cenv''.
      stmt_lands lctx sb res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv') /\
      cenv_top_ext cenv cenv'' ee.scopes /\
      stmt_state_rel ctx func cenv'' cx ee t /\
      ghost_inv d cenv'' cx ee G tn t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
             lookup_var x t = SOME w) /\
      (!x. not_fresh_at sa x ==>
           FLOOKUP G x = FLOOKUP G0 x /\
           op_taint tn (Var x) = op_taint tn0 (Var x))
End

Theorem if_branch_post_pop_ptr:
  stmt_post_ptr d ctx func cx lctx cenv cenv' sa sb s0 G0 tn0 res ee G tn t /\
  ee.scopes = sc :: rest /\
  (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE) ==>
  stmt_post_ptr d ctx func cx lctx cenv cenv sa sb s0 G0 tn0 res
    (ee with scopes := rest) G tn t
Proof
  rewrite_tac[stmt_post_ptr_def] >> strip_tac >>
  qexists_tac `cenv` >> simp[cenv_top_ext_refl] >> conj_tac
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
  gas_outcome_ptr D (cx_tops cx) (ctx,func) PG (eval_stmts cx ss)
    (es with scopes := FEMPTY :: es.scopes,s0,G0,tn0)
    (stmt_post_ptr d ctx func cx lctx cenv cenv' sa sb s0 G0 tn0)
    (\res ee gt r. !tail. stmt_exit_ptr RetQ (ee with gas_obs := tail) res gt r) /\
  es.gas_obs = [] /\ ~s0.vs_halted ==>
  gas_outcome_ptr D (cx_tops cx) (ctx,func) PG
    (ignore_bind push_scope (finally (eval_stmts cx ss) pop_scope)) (es,s0,G0,tn0)
    (stmt_post_ptr d ctx func cx lctx cenv cenv sa sb s0 G0 tn0)
    (\res ee gt r. !tail. stmt_exit_ptr RetQ (ee with gas_obs := tail) res gt r)
Proof
  rewrite_tac[gas_outcome_ptr_def, gas_summary_ptr_at_marked] >> strip_tac
  >- (drule gas_marked_exec_ptr_exec >> strip_tac >> drule if_branch_marked_scopes >>
      strip_tac >> qexists_tac `marks` >> disj1_tac >>
      qexistsl_tac [`res`, `es_end with scopes := rest`, `G`, `tn`, `r`] >>
      conj_tac
      >- (irule if_branch_marked_cleanup_ptr >> simp[] >> metis_tac[]) >>
      disj1_tac >> qexists_tac `t` >> simp[] >>
      irule if_branch_post_pop_ptr >> simp[] >>
      qexists_tac `cenv'` >> simp[])
  >- (drule gas_marked_exec_ptr_exec >> strip_tac >> drule if_branch_marked_scopes >>
      strip_tac >> qexists_tac `marks` >> disj1_tac >>
      qexistsl_tac [`res`, `es_end with scopes := rest`, `G`, `tn`, `r`] >>
      conj_tac
      >- (irule if_branch_marked_cleanup_ptr >> simp[] >> metis_tac[]) >>
      disj2_tac >> gvs[stmt_exit_ptr_def]) >>
  drule if_branch_cert_scopes >> strip_tac >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee with scopes := rest`, `leaf`, `finish'`] >>
  irule eval_stmt_if_scoped_cert >> simp[if_push_scope_marked] >>
  `es with <|scopes := FEMPTY :: es.scopes; gas_obs := []|> =
   es with scopes := FEMPTY :: es.scopes` by
    simp[evaluation_state_component_equality] >> simp[]
QED

Theorem if_branch_post_to_exit_ptr:
  stmt_post_ptr d ctx func cx lctx cenv cenv sa last s0 G0 tn0 res ee G tn t /\
  ~ctx_has_dalloca ctx /\
  (~block_is_terminated last ==>
    emit_inst JMP [Label xl] [] last = ((),after) /\
    fn_has_code last after func /\
    sb.cs_current_bb = xl /\ sb.cs_current_insts = []) ==>
  ?u. gas_path_ptr D 0 ctx func PG G tn t 0 G tn (OK u) /\
      stmt_post_ptr d ctx func cx lctx cenv cenv sa sb s0 G0 tn0 res ee G tn u
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
      qexists_tac `jump_to xl t` >> simp[] >>
      qpat_x_assum `stmt_post_ptr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
      simp[stmt_post_ptr_def] >> strip_tac >>
      `ghost_inv d cenv cx ee G tn (jump_to xl t)` by
        metis_tac[if_ghost_inv_jump] >>
      gvs[stmt_lands_def, stmt_state_rel_jump_to,
          block_is_terminated_def, jump_to_def, lookup_var_def]) >>
  qexists_tac `t` >>
  conj_tac >- (fs[stmt_post_ptr_def] >> metis_tac[gas_path_ptr_rules]) >>
  gvs[stmt_post_ptr_def, stmt_lands_def] >> metis_tac[]
QED

Theorem if_branch_outcome_to_exit_ptr:
  gas_outcome_ptr D (cx_tops cx) (ctx,func) PG source (es,s0,G0,tn0)
    (stmt_post_ptr d ctx func cx lctx cenv cenv sa last s0 G0 tn0) R /\
  ~ctx_has_dalloca ctx /\
  (~block_is_terminated last ==>
    emit_inst JMP [Label xl] [] last = ((),after) /\
    fn_has_code last after func /\
    sb.cs_current_bb = xl /\ sb.cs_current_insts = []) ==>
  gas_outcome_ptr D (cx_tops cx) (ctx,func) PG source (es,s0,G0,tn0)
    (stmt_post_ptr d ctx func cx lctx cenv cenv sa sb s0 G0 tn0) R
Proof
  rewrite_tac[gas_outcome_ptr_def, gas_summary_ptr_at_marked] >> strip_tac
  >- (drule_all if_branch_post_to_exit_ptr >>
      disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
      qexists_tac `marks` >> disj1_tac >>
      qexistsl_tac [`res`, `es_end`, `G`, `tn`, `OK u`] >> simp[] >>
      qpat_x_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
      simp[gas_marked_exec_ptr_def] >> strip_tac >> simp[] >>
      drule_all gas_path_ptr_then >> simp[])
  >- (qexists_tac `marks` >> disj1_tac >>
      qexistsl_tac [`res`, `es_end`, `G`, `tn`, `r`] >> simp[]) >>
  qexists_tac `marks` >> disj2_tac >> metis_tac[]
QED

Theorem if_branch_outcome_ptr:
  gas_outcome_ptr D (cx_tops cx) (ctx,func) PG (eval_stmts cx ss)
    (es with scopes := FEMPTY :: es.scopes,s0,G0,tn0)
    (stmt_post_ptr d ctx func cx lctx cenv cenv' sa last s0 G0 tn0)
    (\res ee gt r. !tail. stmt_exit_ptr RetQ (ee with gas_obs := tail) res gt r) /\
  es.gas_obs = [] /\ ~s0.vs_halted /\ ~ctx_has_dalloca ctx /\
  (~block_is_terminated last ==>
    emit_inst JMP [Label xl] [] last = ((),after) /\
    fn_has_code last after func /\
    sb.cs_current_bb = xl /\ sb.cs_current_insts = []) ==>
  gas_outcome_ptr D (cx_tops cx) (ctx,func) PG
    (ignore_bind push_scope (finally (eval_stmts cx ss) pop_scope)) (es,s0,G0,tn0)
    (stmt_post_ptr d ctx func cx lctx cenv cenv sa sb s0 G0 tn0)
    (\res ee gt r. !tail. stmt_exit_ptr RetQ (ee with gas_obs := tail) res gt r)
Proof
  strip_tac >> irule if_branch_outcome_to_exit_ptr >> simp[] >>
  qexistsl_tac [`after`, `last`, `xl`] >> simp[] >>
  irule if_branch_outcome_cleanup_ptr >> simp[] >> metis_tac[]
QED
