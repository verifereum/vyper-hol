(* Conditional custom-error assertions with checked condition and branch paths. *)
Theory stmtSimCustomErrorPtrAssert
Ancestors
  stmtSimCustomErrorAssert stmtAssertPtr stmtFragPtr bodyPtrDefs
  fragGasPathPtr fragGasSeqPtr gasSummaryComposePtr gasSummaryCompose gasSummary gasExemptCert
  stmtSimAssertProps stmtSimIfProps stmtSimProps stmtSimDefs exprSimDefs exprSimProps
  loweringPosts gasContext gasCount fragExec localPtrsProps freshWrites
  stmtLowering exprLowering emitHelper emitHelperProps exprLoweringProps compileEnv
  valueEncoding ptrDiscipline venomExecSemantics venomInst venomState
  vyperInterpreter vyperState vyperValue vyperValueOperation vyperStatePreservation
  vyperExprNoControl vyperEvalPreservesScopes list finite_map arithmetic
Libs
  monadsyntax

Theorem compile_assert_custom_error_frag_general_ptr:
  !d ctx PG func cx lctx RetQ cenv ty e err es.
    expr_type e = BaseT BoolT /\
    expr_sim_ptr d ctx PG func cenv cx (BaseT BoolT) e es /\
    (!gs es1.
       (do raw <- eval_expr cx e; read_result cx raw od)
         (es with gas_obs := gs) = (INL (BoolV F),es1) ==>
       stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
         (stmt_env cenv lctx ty (Raise (RaiseCustomError err)))
         (eval_stmt cx (Raise (RaiseCustomError err))) es1) ==>
    stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assert e (AssertCustomError err)))
      (eval_stmt cx (Assert e (AssertCustomError err))) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_ptr_def] >> rpt gen_tac >> strip_tac >>
  drule_at (Pat `stmt_env _ _ _ _ _ = _`) compile_assert_custom_error_parts >>
  strip_tac >> gvs[] >>
  drule_all assert_custom_error_compiler_code >> strip_tac >>
  drule assert_custom_error_condition_admissible >> strip_tac >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
   gas_admissible (bind (eval_expr cx e) (read_result cx))
     (\r. !v. r = INL v ==> ?b. v = BoolV b) es` by
    (gvs[gas_admissible_def] >> metis_tac[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x`
    by metis_tac[ret_pc_ok_def] >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_ptr_def]) >>
  disch_then drule >> simp[] >>
  disch_then (qspecl_then [`s0`,`G0`,`tn0`] mp_tac) >> simp[] >>
  simp[gas_outcome_ptr_def, gas_summary_ptr_at_marked] >>
  disch_then (qx_choose_then `marks` (DISJ_CASES_THEN assume_tac))
  >- (qpat_x_assum `?res es_end G tn r. _` strip_assume_tac >> gvs[]
      >- suspend "normal"
      >> suspend "exception") >>
  qexists_tac `marks` >> disj2_tac >> pop_assum strip_assume_tac >>
  qexistsl_tac [`err'`,`ee`,`leaf`,`finish'`] >>
  rewrite_tac[eval_assert_custom_error_bind] >>
  pure_once_rewrite_tac[ignore_bind_def] >>
  pure_once_rewrite_tac[vyperStateTheory.bind_assoc] >>
  irule gas_exempt_cert_error_value >> simp[GSYM ignore_bind_def]
QED

Resume compile_assert_custom_error_frag_general_ptr[exception]:
  Cases_on `res` >- fs[expr_exit_def] >>
  qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`INR y`,`es_end`,`G`,`tn`,`r`] >> conj_tac
  >- (rewrite_tac[eval_assert_custom_error_bind] >>
      irule gas_marked_exec_ptr_bind_exception >> first_assum ACCEPT_TAC) >>
  disj2_tac >> simp[stmt_exit_ptr_def] >>
  metis_tac[expr_exit_INR_type]
QED

Resume compile_assert_custom_error_frag_general_ptr[normal]:
  `!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (INL v,es_end with gas_obs := tail)` by fs[gas_marked_exec_ptr_def] >>
  `bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (INL v,es_end with gas_obs := [])` by
    (qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >> simp[]) >>
  `?b. v = BoolV b` by
    (qpat_x_assum `gas_admissible _ (\r. _) _` mp_tac >>
     rewrite_tac[gas_admissible_def] >> disch_then drule >> simp[]) >>
  gvs[] >>
  `~t.vs_halted` by
    (fs[gas_marked_exec_ptr_def] >> metis_tac[gas_path_ptr_ok_not_halted]) >>
  `eval_operand op t = SOME (if b then 1w else 0w)` by
    (drule_all if_condition_operand >> Cases_on `b` >> simp[val_to_w256_def]) >>
  `op_taint tn op = {}` by gvs[ptr_val_ok_def] >>
  drule emit_inst_extends >> strip_tac >>
  `fn_has_code s3 s4 func` by gvs[fn_has_code_def, emitted_blocks_def] >>
  `gas_path_ptr (cx_dead cx) 0 ctx func PG G tn t 0 G tn
    (OK (jump_to (if b then sb.cs_current_bb else entry.cs_current_bb) t))` by
    (irule assert_jnz_zero_path_ptr >> simp[] >>
     qexistsl_tac [`op`,`s3`,`s4`] >> gvs[]) >>
  `gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0) marks
    (INL (BoolV b)) es_end G tn
    (OK (jump_to (if b then sb.cs_current_bb else entry.cs_current_bb) t))` by
    (fs[gas_marked_exec_ptr_def] >> metis_tac[gas_path_ptr_then, ADD_0]) >>
  Cases_on `b` >- suspend "true" >> suspend "false"
QED

Resume compile_assert_custom_error_frag_general_ptr[true]:
  gvs[] >>
  `stmt_post ctx func cx lctx cenv cenv sa sb es s0 (INL ())
    (es_end with gas_obs := []) (jump_to sb.cs_current_bb t)` by
    (irule assert_success_post >> simp[] >> conj_tac
     >- (qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
         drule stmtSimDefsTheory.eval_read_preserves_scopes_dom >> simp[]) >>
     qexistsl_tac [`e`,`op`,`s1`] >> simp[]) >>
  qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`INL ()`,`es_end`,`G`,`tn`,`OK (jump_to sb.cs_current_bb t)`] >>
  conj_tac
  >- (simp[gas_marked_exec_ptr_def] >> conj_tac
      >- (gen_tac >> asm_simp_tac (srw_ss()) [eval_assert_custom_error_bind] >>
          simp[Once bind_def, return_def]) >>
      metis_tac[gas_marked_exec_ptr_def]) >>
  disj1_tac >> simp[] >> gvs[stmt_post_def] >>
  gvs[ghost_inv_jump_to, jump_to_def, ghost_kept_def]
QED

Resume compile_assert_custom_error_frag_general_ptr[false]:
  gvs[] >>
  `gas_admissible (eval_stmt cx (Raise (RaiseCustomError err)))
    (stmt_res_ok lctx) (es_end with gas_obs := [])` by
    (irule assert_custom_error_raise_admissible >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any)) >>
  `stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
    (stmt_env cenv lctx ty (Raise (RaiseCustomError err)))
    (eval_stmt cx (Raise (RaiseCustomError err))) (es_end with gas_obs := [])` by
    (qpat_x_assum `!gs es1. _` irule >>
     qexists_tac `gas_explicit marks s0.vs_gas_readings` >>
     qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  `local_ptrs_reserved cenv entry` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  `ret_pc_ok cenv entry (jump_to entry.cs_current_bb t)` by
    (simp[ret_pc_ok_jump_to] >> irule ret_pc_ok_frame >>
     qexistsl_tac [`cenv`,`s0`,`sa`] >> gvs[expr_post_def]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at entry x` by metis_tac[not_fresh_at_mono] >>
  `gas_marked_exec F (ctx,func)
    (bind (eval_expr cx e) (read_result cx)) (es,s0) marks
    (INL (BoolV F)) es_end (OK (jump_to entry.cs_current_bb t))` by
    metis_tac[gas_marked_exec_ptr_exec] >>
  qpat_x_assum `stmt_frag_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[stmt_frag_ptr_def] >> disch_then drule >> simp[block_is_terminated_def] >>
  disch_then (qspecl_then [`jump_to entry.cs_current_bb t`,`G`,`tn`] mp_tac) >>
  (impl_tac >- gvs[stmt_state_rel_jump_to, jump_to_def, expr_post_def,
    ghost_inv_jump_to]) >>
  rewrite_tac[gas_outcome_ptr_def, gas_summary_ptr_at_marked] >> strip_tac
  >- suspend "false_normal"
  >- suspend "false_exit"
  >> suspend "false_cert"
QED

Resume compile_assert_custom_error_frag_general_ptr[false_normal]:
  gvs[gas_marked_exec_ptr_def] >>
  qpat_x_assum `!tail. eval_stmt _ (Raise _) _ = _`
    (qspec_then `[]` mp_tac) >> simp[] >> strip_tac >>
  drule eval_raise_custom_error_non_normal >>
  gvs[stmt_lands_def, AllCaseEqs(), no_control_exc_def]
QED

Resume compile_assert_custom_error_frag_general_ptr[false_exit]:
  rename1 `exit_result r` >>
  qexists_tac `marks ++ marks'` >> disj1_tac >>
  qexistsl_tac [`res`,`es_end'`,`G'`,`tn'`,`r`] >>
  reverse conj_tac >- (disj2_tac >> gvs[]) >>
  rewrite_tac[eval_assert_custom_error_bind] >>
  irule gas_marked_exec_ptr_bind_normal >>
  goal_assum (drule_at Any) >> simp[]
QED

Resume compile_assert_custom_error_frag_general_ptr[false_cert]:
  qexists_tac `marks ++ marks'` >> disj2_tac >>
  qexistsl_tac [`err'`,`ee`,`leaf`,`finish'`] >>
  rewrite_tac[eval_assert_custom_error_bind] >>
  pure_once_rewrite_tac[ignore_bind_def] >>
  pure_once_rewrite_tac[vyperStateTheory.bind_assoc] >>
  irule gas_exempt_cert_bind_value >>
  qexistsl_tac [`es_end`,`jump_to entry.cs_current_bb t`,`BoolV F`] >>
  simp[GSYM ignore_bind_def]
QED
Finalise compile_assert_custom_error_frag_general_ptr
