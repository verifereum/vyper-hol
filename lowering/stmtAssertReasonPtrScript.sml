(* A reason-independent checked assertion continuation. *)
Theory stmtAssertReasonPtr
Ancestors
  reasonSourceProps reasonCompilerProps stmtAssertPtr bodyPtrDefs stmtFragPtr
  fragGasPathPtr gasSummaryComposePtr gasSummary gasSummaryCompose gasExemptCert
  gasCount fragGasMode stmtSimDefs stmtSimProps stmtSimAssertProps exprSimDefs
  exprSimProps loweringPosts compileEnv context emitHelper emitHelperProps
  exprLoweringProps vyperInterpreter vyperState venomState fragExec
  list rich_list arithmetic gasContext fragGasSeqPtr vyperValue valueEncoding
Libs
  monadsyntax

Theorem assert_reason_false_outcome_prefix_ptr:
  gas_marked_exec_ptr D (ctx,fn) PG (bind (eval_expr cx e) (read_result cx))
    (es,s0,G0,tn0) marks (INL (BoolV F)) mid G tn (OK t) /\
  gas_path_ptr D 0 ctx fn PG G tn t 0 G tn (OK (jump_to fl t)) /\
  gas_outcome_ptr D (cx_tops cx) (ctx,fn) PG
    (eval_stmt cx (Raise (RaiseReason r)))
    (mid with gas_obs := [],jump_to fl t,G,tn) N
    (\res ee gt rr. !tail. stmt_exit_ptr RetQ (ee with gas_obs := tail) res gt rr) /\
  (!res ee Gf tnf u. N res ee Gf tnf u ==> stmt_lands lctx last res u) ==>
  gas_outcome_ptr D (cx_tops cx) (ctx,fn) PG
    (eval_stmt cx (Assert e (AssertReason r))) (es,s0,G0,tn0) Q
    (\res ee gt rr. !tail. stmt_exit_ptr RetQ (ee with gas_obs := tail) res gt rr)
Proof
  strip_tac >>
  `gas_marked_exec_ptr D (ctx,fn) PG (bind (eval_expr cx e) (read_result cx))
    (es,s0,G0,tn0) marks (INL (BoolV F)) mid G tn (OK (jump_to fl t))` by
    (fs[gas_marked_exec_ptr_def] >> drule_all gas_path_ptr_then >> simp[]) >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_ptr_def, gas_summary_ptr_at_marked] >> strip_tac
  >- suspend "normal"
  >- suspend "exit"
  >> suspend "cert"
QED

Resume assert_reason_false_outcome_prefix_ptr[normal]:
  gvs[gas_marked_exec_ptr_def] >>
  qpat_x_assum `!tail. eval_stmt _ _ _ = _` (qspec_then `[]` mp_tac) >> simp[] >>
  strip_tac >> drule eval_raise_reason_non_normal >> strip_tac >>
  `stmt_lands lctx last res t'` by metis_tac[] >>
  gvs[stmt_lands_def]
QED

Resume assert_reason_false_outcome_prefix_ptr[exit]:
  rename1 `exit_result rr` >>
  qexists `marks ++ marks'` >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_marked] >>
  qexistsl [`res`,`es_end`,`G'`,`tn'`,`rr`] >> simp[] >>
  rewrite_tac[eval_assert_reason_bind] >>
  irule gas_marked_exec_ptr_bind_normal >>
  qexistsl [`G`,`mid`,`jump_to fl t`,`tn`,`BoolV F`] >> simp[]
QED

Resume assert_reason_false_outcome_prefix_ptr[cert]:
  qexists `marks ++ marks'` >> disj2_tac >>
  qexistsl [`err`,`ee`,`leaf`,`finish'`] >>
  rewrite_tac[eval_assert_reason_bind] >>
  pure_once_rewrite_tac[ignore_bind_def] >>
  pure_once_rewrite_tac[vyperStateTheory.bind_assoc] >>
  irule gas_exempt_cert_bind_value >>
  qexistsl [`mid`,`jump_to fl t`,`BoolV F`] >>
  simp[GSYM ignore_bind_def] >>
  metis_tac[gas_marked_exec_ptr_exec]
QED

Finalise assert_reason_false_outcome_prefix_ptr

Theorem compile_assert_reason_frag_general_ptr:
  !d ctx PG fn cx lctx RetQ cenv ty e r es.
    expr_type e = BaseT BoolT /\
    expr_sim_ptr d ctx PG fn cenv cx (BaseT BoolT) e es /\
    (!gs es1.
       bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
         (INL (BoolV F),es1) ==>
       stmt_frag_ptr d ctx PG fn cx lctx RetQ cenv
         (stmt_env cenv lctx ty (Raise (RaiseReason r)))
         (eval_stmt cx (Raise (RaiseReason r))) es1) ==>
    stmt_frag_ptr d ctx PG fn cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assert e (AssertReason r)))
      (eval_stmt cx (Assert e (AssertReason r))) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_ptr_def] >> rpt gen_tac >> strip_tac >>
  drule_at (Pat `stmt_env _ _ _ _ _ = _`) compile_assert_reason_parts >>
  strip_tac >> gvs[] >>
  drule_all assert_reason_compiler_code >> strip_tac >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule assert_reason_expr_admissible >> goal_assum (drule_at Any)) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x`
    by metis_tac[ret_pc_ok_def] >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_ptr_def]) >>
  disch_then drule >> simp[] >>
  disch_then (qspecl_then [`s0`,`G0`,`tn0`] mp_tac) >> simp[] >>
  simp[gas_outcome_ptr_def, gas_summary_ptr_at_def] >>
  disch_then (qx_choose_then `marks` (DISJ_CASES_THEN assume_tac))
  >- (qpat_x_assum `?res es_end G tn rr. _` strip_assume_tac >> gvs[]
      >- suspend "normal"
      >> suspend "exception") >>
  qexists `marks` >> disj2_tac >> pop_assum strip_assume_tac >>
  qexistsl [`err`,`ee`,`leaf`,`finish'`] >>
  irule assert_reason_expr_exempt >> simp[]
QED

Resume compile_assert_reason_frag_general_ptr[exception]:
  Cases_on `res` >- fs[expr_exit_def] >>
  qexists `marks` >> disj1_tac >>
  qexistsl [`INR y`,`es_end`,`G`,`tn`,`r'`] >>
  conj_tac >- (gen_tac >> simp[eval_assert_reason_bind, Once bind_def]) >>
  conj_tac >- simp[] >>
  disj2_tac >> simp[stmt_exit_ptr_def] >> metis_tac[expr_exit_INR_type]
QED

Resume compile_assert_reason_frag_general_ptr[normal]:
  `?b. v = BoolV b` by
    (spose_not_then assume_tac >>
     qpat_x_assum `gas_admissible (eval_stmt _ _) _ _` mp_tac >>
     pure_rewrite_tac[gas_admissible_def] >>
     disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings` mp_tac) >>
     qpat_x_assum `!tail. _ = _` (qspec_then `[]` assume_tac) >>
     gvs[eval_assert_reason_bind, bind_def, raise_def, stmt_res_ok_def]) >>
  `~t.vs_halted` by metis_tac[gas_path_ptr_ok_not_halted] >>
  `eval_operand op t = SOME (if b then 1w else 0w)` by
    gvs[expr_post_def, expr_val_rel_def, evaluate_type_def, is_word_type_def,
        typed_val_to_w256_def, val_to_w256_def] >>
  `op_taint tn op = {}` by gvs[ptr_val_ok_def] >>
  `gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn t 0 G tn
     (OK (jump_to (if b then sb.cs_current_bb else entry.cs_current_bb) t))` by
    (imp_res_tac emit_inst_extends >> irule assert_jnz_zero_path_ptr >> simp[] >>
     qexistsl [`op`,`s3`,`s4`] >> simp[]) >>
  Cases_on `b` >- suspend "true" >> suspend "false"
QED

Resume compile_assert_reason_frag_general_ptr[true]:
  gvs[] >> qexists `marks` >> disj1_tac >>
  `stmt_post ctx fn cx lctx cenv cenv sa sb s0 (INL ())
     (es_end with gas_obs := []) (jump_to sb.cs_current_bb t)` by
    (irule assert_success_post >> simp[] >>
     qexistsl [`e`,`es`,`op`,`s1`] >> simp[]) >>
  qexistsl [`INL ()`,`es_end`,`G`,`tn`,`OK (jump_to sb.cs_current_bb t)`] >>
  conj_tac >- (gen_tac >> simp[eval_assert_reason_bind, Once bind_def, return_def]) >>
  conj_tac >- metis_tac[gas_path_ptr_then, ADD_CLAUSES] >>
  disj1_tac >> simp[] >> gvs[stmt_post_def] >>
  gvs[ghost_inv_jump_to, jump_to_def, ghost_kept_def]
QED

Resume compile_assert_reason_frag_general_ptr[false]:
  gvs[] >>
  `gas_admissible (eval_stmt cx (Raise (RaiseReason r)))
    (stmt_res_ok lctx) (es_end with gas_obs := [])` by
    (irule assert_reason_raise_admissible >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any)) >>
  `stmt_frag_ptr d ctx PG fn cx lctx RetQ cenv
    (stmt_env cenv lctx ty (Raise (RaiseReason r)))
    (eval_stmt cx (Raise (RaiseReason r))) (es_end with gas_obs := [])` by
    (qpat_x_assum `!gs es1. _` irule >>
     qexists `gas_explicit marks s0.vs_gas_readings` >>
     qpat_x_assum `!tail. _ = _` (qspec_then `[]` mp_tac) >> simp[]) >>
  `local_ptrs_reserved cenv entry` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  `ret_pc_ok cenv entry (jump_to entry.cs_current_bb t)` by
    (simp[ret_pc_ok_jump_to] >> irule ret_pc_ok_frame >>
     qexistsl [`cenv`,`s0`,`sa`] >> gvs[expr_post_def]) >>
  qpat_x_assum `stmt_frag_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[stmt_frag_ptr_def] >> disch_then drule >> simp[block_is_terminated_def] >>
  disch_then (qspecl_then [`jump_to entry.cs_current_bb t`,`G`,`tn`] mp_tac) >>
  (impl_tac >- (gvs[stmt_state_rel_jump_to, jump_to_def, expr_post_def,
                    ghost_inv_jump_to, ghost_inv_gas_obs] >>
                   metis_tac[stmtFragPtrTheory.not_fresh_at_mono])) >>
  strip_tac >> suspend "compose"
QED

Resume compile_assert_reason_frag_general_ptr[compose]:
  `gas_marked_exec_ptr (cx_dead cx) (ctx,fn) PG
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    marks (INL (BoolV F)) es_end G tn (OK t)` by
    simp[gas_marked_exec_ptr_def] >>
  drule_at (Pat `gas_outcome_ptr _ _ _ _ _ _ _ _`)
    assert_reason_false_outcome_prefix_ptr >>
  disch_then drule >>
  disch_then (qspecl_then [`lctx`,`last`] mp_tac) >> simp[] >>
  (impl_tac >- (rpt strip_tac >> simp[])) >>
  disch_then (qspec_then `\res ee G tn t. F` mp_tac) >>
  simp[gas_outcome_ptr_def, gas_summary_ptr_at_def] >>
  metis_tac[]
QED

Finalise compile_assert_reason_frag_general_ptr
