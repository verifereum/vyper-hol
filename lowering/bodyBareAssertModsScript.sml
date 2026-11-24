(* Bind the linked condition outcome to the selected no-payload assertion. *)
Theory bodyBareAssertMods
Ancestors
  bodyAssertLandingMods bodyFullPostsMods bodyFullShared
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasExemptCertMods
  gasShadow gasShadowCompileStmtHelpers stmtSimAssertProps stmtSimDefs
  compileEnv exprLoweringProps exprSimDefs stmtSimProps loweringPosts bodyPtrDefs fragExec
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState

Theorem compile_assert_frag_full_mods:
  !DF lo d ctx shadow_ctx PG func shadow_func cx lctx RetQ cenv ty e ak es.
    (ak = AssertBare \/ ak = AssertUnreachable) /\
    expr_type e = BaseT BoolT /\
    expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (BaseT BoolT) e es ==>
    stmt_frag_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assert e ak))
      (stmt_env (gas_shadow_env T cenv) lctx ty (gas_shadow_stmt (Assert e ak)))
      (eval_stmt cx (Assert e ak)) es
Proof
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  pure_rewrite_tac[stmt_frag_full_mods_def] >> rpt gen_tac >> strip_tac >>
  qpat_assum `stmt_env _ _ _ (Assert e _) _ = _`
    (mp_then Any mp_tac compile_assert_parts) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `gas_shadow_assert_reason ak = ak` by
    (qpat_assum `ak = _ \/ _` strip_assume_tac >> simp[gas_shadow_assert_reason_def]) >>
  qpat_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _` mp_tac >>
  pure_rewrite_tac[gas_shadow_stmt_def] >>
  qpat_assum `gas_shadow_assert_reason ak = ak` (rewrite_tac o single) >>
  disch_then (mp_then Any mp_tac compile_assert_parts) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`sop`,`sc`,`sok`,`s2'`,`sfl`,`s3'`,`s4'`,
     `s5'`,`s6'`] strip_assume_tac) >>
  `sop = op /\ gas_shadow_state s1 sc` by
    (irule gas_shadow_step >>
     rpt (goal_assum (drule_at Any)) >>
     simp[gas_shadow_stmt_lower_value_env]) >>
  qpat_x_assum `sop = op` SUBST_ALL_TAC >>
  qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC >>
  `cs_extends sa s1 /\ cs_extends shadow_sa sc` by
    metis_tac[compile_expr_grows] >>
  qpat_assum `cs_extends sa s1`
    (mp_then (Pos hd) mp_tac assert_compiler_code) >>
  disch_then (drule_all_then strip_assume_tac) >>
  qpat_assum `cs_extends shadow_sa sc`
    (mp_then (Pos hd) mp_tac assert_compiler_code) >>
  disch_then (drule_all_then strip_assume_tac) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[assert_expr_admissible] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sa x` by metis_tac[ret_pc_ok_def] >>
  qpat_x_assum `expr_sim_full_mods _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_full_mods_def] >>
  disch_then (qspecl_then [`st0`,`sa`,`s1`,`shadow_sa`,`sc`,`op`,`s0`,
    `G0`,`tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  drule_all_then strip_assume_tac gas_outcome_full_mods_return_buf_allocas >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ _ _ (\H res ee G tn t. ?v. _) _`
    kall_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ condQ condR` >>
  `eval_stmt cx (Assert e ak) =
     bind (bind (eval_expr cx e) (read_result cx))
       (\v. if v = BoolV T then return ()
            else if v = BoolV F then
              raise (AssertException (if ak = AssertBare then "" else "UNREACHABLE"))
            else raise (Error (TypeError "not BoolV")))` by
    (irule eval_assert_bind >> first_assum ACCEPT_TAC) >>
  pop_assum (fn th => PURE_REWRITE_TAC [th]) >>
  irule gas_outcome_full_mods_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      qexistsl_tac [`mid`,`t`,`v`] >> RULE_ASSUM_TAC BETA_RULE >> BETA_TAC >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result])
  >~ [`storage_trace_frame _`]
  >- rw[storage_trace_frame_raise, storage_trace_frame_return] >>
  qexists_tac `\H res ee G tn t. condQ H res ee G tn t /\
      ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac
  >~ [`storage_trace_domain _ _ _`] >- suspend "selected" >>
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` (irule_at Any) >>
  conj_tac >- simp[] >>
  simp[Abbr `condR`] >> rpt strip_tac >>
  Cases_on `res` >- fs[expr_exit_def] >>
  fs[stmt_exit_ptr_def, expr_exit_INR_type, halt_exit_def] >>
  Cases_on `r` >> gvs[expr_exit_def]
QED

Resume compile_assert_frag_full_mods[selected]:
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] >>
  BETA_TAC >> strip_tac >> disj1_tac >>
  qunabbrev_tac `condQ` >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  qexists_tac `v` >> simp[] >>
  `post_value_type cenv e = BaseT BoolT` by
    simp[post_value_type_word, is_word_type_def] >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es s0` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
      expr_post_mods H ctx func cenv cx e es sa s1 s0 mid v op t /\
      ghost_inv_at_mods (DF H) lo d cenv cx mid G1 tn1 t` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> gvs[]) >>
  qpat_assum `stmt_env _ _ _ (Assert e _) sa = _`
    (mp_then (Pos (el 2)) mp_tac (Q.INST
       [`explicit` |-> `gas_explicit_sites ctx shadow_ctx`, `PG` |-> `PG`]
       assert_selected_landing_mods)) >>
  `ptr_val_ok cx (BaseT BoolT) v op G1 tn1 t` by fs[] >>
  disch_then (drule_all_then
    (qspecl_then [`shadow_ctx`,`PG`] (qx_choose_then `b` strip_assume_tac))) >>
  qpat_x_assum `v = BoolV _` SUBST_ALL_TAC >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  Cases_on `b` >> fs[] >>
  FIRST
  [ qmatch_goalsub_rename_tac `gas_outcome_full_mods _ _ _ _ (return ()) _ _ _` >>
    irule gas_outcome_full_mods_pure >> simp[] >>
    qexistsl_tac [`G1`,`mid`,`INL ()`,`jump_to sb.cs_current_bb t`,`tn1`] >>
    simp[return_def] >> qx_gen_tac `H` >> disch_tac >>
    qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
      (qspec_then `H` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> gvs[] >>
    first_assum ACCEPT_TAC,
    qmatch_goalsub_rename_tac `raise (AssertException msg)` >>
    irule gas_outcome_full_mods_exit >> simp[] >>
    qexistsl_tac [`G1`,`mid`,`Abort a u`,`INR (AssertException msg)`,`tn1`] >>
    gvs[raise_def, exit_result_def, stmt_exit_ptr_def, halt_exit_def] ]
QED

Finalise compile_assert_frag_full_mods
