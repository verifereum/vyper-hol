(* Seam 2 joint induction, a family leaf of the stmt step: If. *)
Theory bodyIntCallFamStmtIf
Ancestors
  bodyIntCallJointContract bodyIntCallJointStmtJump
  bodyIntCallJointStmtBoundary bodyIntCallDeclarationRegions
  bodyExprPreFacts exprLoweringProps intCallFrame compileEnv
  vyperState finite_map list exprSimHypsDefs vyperTypeEvalSoundness
  vyperTypeInvariants vyperTypeSystem vyperTypeCallGraph
  bodyStoragePreservation vyperTypeExprSoundness vyperTypeStoragePreservation
  vyperEvalOutcomeSuffix

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
