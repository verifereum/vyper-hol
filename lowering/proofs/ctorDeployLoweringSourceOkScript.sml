(* A piece of deploy_unit_execution_correct (ctorDeployLowering).
   The constructor body never ends in a break, a continue or a type error. *)
Theory ctorDeployLoweringSourceOk
Ancestors
  ctorDeployLoweringDefs stmtSimDefs vyperInterpreter vyperState finite_map
  ctorDeployDefs e2eDeployDefs vyperTypeDeploymentSoundness
  vyperTypeInvariants vyperTypeContractSoundness vyperContext alist

Theorem deploy_ctor_prefix_replay:
  ignore_bind (send_call_value mut cx) (lock_if_nr cx nr (is_view_mut mut))
    (initial_state am_c [env] with <|outcomes := NONE; requests := []|>) = (INL (), es0)
  ==>
  ignore_bind (send_call_value mut cx)
    (ignore_bind (set_scopes [env]) (lock_if_nr cx nr (is_view_mut mut)))
    (initial_state am_c [FEMPTY] with <|outcomes := oc; requests := []; gas_obs := gs|>)
  = (INL (), es0 with <|gas_obs := gs; outcomes := oc|>)
Proof
  Cases_on `cx.nonreentrant_slot` >>
  simp[send_call_value_def, transfer_value_def, lock_if_nr_def,
       acquire_nonreentrant_lock_def, initial_state_def,
       ignore_bind_def, bind_def, return_def, raise_def, check_def,
       assert_def, get_accounts_def, update_accounts_def,
       get_transient_storage_def, update_transient_def, set_scopes_def,
       COND_RATOR] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem deploy_typing_context_well_typed[local]:
  deploy_typing_ok tops am tx ==>
  context_well_typed (deploy_evaluation_context tops am tx)
Proof
  rw[deploy_typing_ok_def] >>
  gvs[call_tx_well_typed_def, context_well_typed_def,
      deploy_evaluation_context_def, initial_evaluation_context_def]
QED

Theorem deploy_ctor_full_run[local]:
  !mut cx nr am_c env es0 stmts oc gs r.
    ignore_bind (send_call_value mut cx) (lock_if_nr cx nr (is_view_mut mut))
      (initial_state am_c [env] with <|outcomes := NONE; requests := []|>) =
      (INL (), es0) /\
    eval_stmts cx stmts (es0 with <|gas_obs := gs; outcomes := oc|>) = r ==>
    ignore_bind (send_call_value mut cx)
      (ignore_bind (set_scopes [env])
         (ignore_bind (lock_if_nr cx nr (is_view_mut mut)) (eval_stmts cx stmts)))
      (initial_state am_c [FEMPTY] with
         <|outcomes := oc; requests := []; gas_obs := gs|>) = r
Proof
  rpt gen_tac >> strip_tac >>
  drule deploy_ctor_prefix_replay >>
  disch_then (qspecl_then [`oc`, `gs`] mp_tac) >>
  simp[ignore_bind_apply, AllCaseEqs()] >> strip_tac >> gvs[]
QED

(* The constructor body never ends in a break or a continue. *)
Theorem deploy_ctor_body_source_ok:
  !tops am tx mut nr body am_c es0 gs oc res ee.
    deploy_source_ok tops am tx /\ tx.function_name = "__init__" /\
    deploy_ctor_start tops am tx (mut, nr, body, am_c, es0) /\
    eval_stmts (deploy_evaluation_context tops am tx) body
      (es0 with <| gas_obs := gs; outcomes := oc |>) = (res, ee) ==>
    stmt_res_ok NoLoop res
Proof
  rpt gen_tac >> pure_rewrite_tac[deploy_source_ok_def, deploy_ctor_start_def] >>
  strip_tac >>
  drule deploy_typing_context_well_typed >> strip_tac >>
  drule_all deploy_ctor_full_run >>
  PURE_REWRITE_TAC [lock_if_nr_def, is_view_mut_def] >> strip_tac >>
  fs[deploy_typing_ok_def] >>
  `no_type_error_eval (res, ee)` by
    (qpat_x_assum `ignore_bind _ (ignore_bind _ _) _ = _` (SUBST1_TAC o SYM) >>
     irule (PURE_REWRITE_RULE [GSYM deploy_evaluation_context_def]
              (Q.INST [`mods` |-> `[(NONE,tops)]`]
                 checked_constructor_prefix_no_type_error)) >>
     simp[] >>
     qexistsl_tac [`am`, `args`, `deploy_art`, `[]`, `[]`, `imms`, `NoneT`,
                   `runtime_art`, `tops`, `tx`, `tx.args`] >>
     simp[]) >>
  Cases_on `res` >> simp[stmt_res_ok_def] >>
  rename1 `INR exc` >>
  `exc <> BreakException /\ exc <> ContinueException` by
    (irule checked_constructor_prefix_no_loop_control >>
     rpt (first_assum (irule_at Any)) >> simp[]) >>
  Cases_on `exc` >> gvs[vyperTypeExprSoundnessTheory.no_type_error_eval_def, vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  rename1 `INR (Error err)` >> Cases_on `err` >> gvs[]
QED
