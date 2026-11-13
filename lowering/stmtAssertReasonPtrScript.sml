(* A reason-independent checked assertion continuation. *)
Theory stmtAssertReasonPtr
Ancestors
  reasonSourceProps reasonCompilerProps stmtAssertPtr bodyPtrDefs stmtFragPtr
  fragGasPathPtr gasSummaryComposePtr gasSummary gasSummaryCompose gasExemptCert
  gasCount fragGasMode stmtSimDefs stmtSimProps stmtSimAssertProps exprSimDefs
  exprSimProps loweringPosts compileEnv context emitHelper emitHelperProps
  exprLoweringProps vyperInterpreter vyperState venomState fragExec
  list rich_list arithmetic gasContext fragGasSeqPtr vyperValue valueEncoding
  gasStorage gasOutcomeMarkedPtr vyperStorageTrace vyperStorageFootprint
Libs
  monadsyntax

Theorem assert_reason_false_outcome_prefix_ptr:
  gas_marked_exec F (ctx,fn) (bind (eval_expr cx e) (read_result cx))
    (es,s0) marks (INL (BoolV F)) mid (OK t) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_path_ptr (D H) 0 ctx fn PG G0 tn0 s0 (LENGTH marks) G tn (OK t) /\
    gas_path_ptr (D H) 0 ctx fn PG G tn t 0 G tn (OK (jump_to fl t))) /\
  gas_outcome_ptr D (cx_tops cx) (ctx,fn) PG cx st0
    (eval_stmt cx (Raise (RaiseReason r)))
    (mid with gas_obs := [],jump_to fl t,G,tn) N
    (\H res ee gt rr. !tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt rr) /\
  (!H res ee Gf tnf u. N H res ee Gf tnf u ==> stmt_lands lctx last res u) ==>
  gas_outcome_ptr D (cx_tops cx) (ctx,fn) PG cx st0
    (eval_stmt cx (Assert e (AssertReason r))) (es,s0,G0,tn0) Q
    (\H res ee gt rr. !tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt rr)
Proof
  strip_tac >>
  reverse (Cases_on `?H. valid_horizon cx st0 H mid.storage_trace`)
  >- (rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `marks` >> disj1_tac >>
      rewrite_tac[eval_assert_reason_bind] >>
      irule gas_bad_storage_at_bind_left >> conj_tac
      >- (gen_tac >> BETA_TAC >> rpt IF_CASES_TAC >>
          simp[evaluate_storage_trace_frame, storage_trace_frame_return,
            storage_trace_frame_raise]) >>
      irule gas_bad_storage_at_no_horizon >>
      fs[gas_marked_exec_def] >> metis_tac[]) >>
  pop_assum (qx_choose_then `H0` assume_tac) >>
  `gas_marked_exec F (ctx,fn) (bind (eval_expr cx e) (read_result cx))
    (es,s0) marks (INL (BoolV F)) mid (OK (jump_to fl t))` by
    (fs[gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def] >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `H0` (drule_then strip_assume_tac)) >>
     drule_all_then assume_tac gas_path_ptr_then >>
     fs[] >> metis_tac[gas_path_ptr_erase]) >>
  `gas_outcome_ptr D (cx_tops cx) (ctx,fn) PG cx st0
    (eval_stmt cx (Raise (RaiseReason r)))
    (mid with gas_obs := [],jump_to fl t,G,tn) Q
    (\H res ee gt rr. !tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt rr)` by
    (irule gas_outcome_ptr_marked_conseq >>
     first_assum (irule_at (Pat `gas_outcome_ptr _ _ _ _ _ _ _ _ _ _`)) >>
     qx_genl_tac [`H1`, `right`, `res`, `fin`, `Gf`, `tnf`, `u`] >> strip_tac >>
     `stmt_lands lctx last res u` by metis_tac[] >>
     fs[gas_marked_exec_ptr_def] >>
     qpat_x_assum `!tail. eval_stmt _ _ _ = _`
       (qspec_then `[]` assume_tac) >> fs[] >>
     drule eval_raise_reason_non_normal >>
     fs[stmt_lands_def] >> metis_tac[]) >>
  rewrite_tac[eval_assert_reason_bind] >>
  irule gas_outcome_ptr_bind_normal >>
  first_assum (irule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >>
  simp[evaluate_storage_trace_frame] >>
  first_assum (irule_at (Pat `gas_outcome_ptr _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> rpt conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
      goal_assum (drule_at Any) >> simp[]) >>
  qx_gen_tac `H1` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `H1` (drule_then strip_assume_tac)) >>
  drule_all_then assume_tac gas_path_ptr_then >> fs[]
QED

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
    (mp_tac o Q.SPECL [`st0`, `sa`, `s1`, `op`, `s0`, `G0`, `tn0`] o
     REWRITE_RULE [expr_sim_ptr_def]) >>
  (impl_tac >- simp[]) >>
  disch_then (strip_assume_tac o REWRITE_RULE [gas_outcome_ptr_def])
  >- (rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `marks` >> disj1_tac >>
      rewrite_tac[eval_assert_reason_bind] >>
      irule gas_bad_storage_at_bind_left >> goal_assum (drule_at Any) >>
      gen_tac >> BETA_TAC >> rpt IF_CASES_TAC >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_return,
        storage_trace_frame_raise])
  >- (pop_assum (strip_assume_tac o REWRITE_RULE [gas_summary_ptr_at_def]) >>
      Cases_on `?H. valid_horizon cx st0 H es_end.storage_trace`
      >- (pop_assum (qx_choose_then `H1` assume_tac) >>
          qpat_assum `!H. _ ==> gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
            (drule_then strip_assume_tac) >>
          qpat_x_assum `!H. _ ==> gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
            assume_tac >>
          gvs[exit_result_def]
          >- suspend "normal"
          >> suspend "exception") >>
      rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `marks` >> disj1_tac >>
      rewrite_tac[eval_assert_reason_bind] >>
      irule gas_bad_storage_at_bind_left >> conj_tac
      >- (gen_tac >> BETA_TAC >> rpt IF_CASES_TAC >>
          simp[evaluate_storage_trace_frame, storage_trace_frame_return,
            storage_trace_frame_raise]) >>
      irule gas_bad_storage_at_no_horizon >> fs[] >> metis_tac[]) >>
  rewrite_tac[gas_outcome_ptr_def] >>
  qexists_tac `marks` >> disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`finish'`] >>
  irule assert_reason_expr_exempt >> simp[]
QED

Resume compile_assert_reason_frag_general_ptr[exception]:
  Cases_on `res` >- fs[expr_exit_def] >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `marks` >>
  disj2_tac >> disj1_tac >> rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INR y`,`es_end`,`G`,`tn`,`r'`] >>
  conj_tac >- (gen_tac >> simp[eval_assert_reason_bind, Once bind_def]) >>
  qx_gen_tac `H2` >> strip_tac >> BETA_TAC >>
  conj_tac
  >- (qpat_x_assum `!H. _ ==> gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` drule >> simp[]) >>
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
    (qpat_x_assum `!H. _ ==> gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     gvs[expr_post_def, expr_val_rel_def, evaluate_type_def, is_word_type_def,
         typed_val_to_w256_def, val_to_w256_def]) >>
  `op_taint tn op = {}` by gvs[ptr_val_ok_def] >>
  `!D. gas_path_ptr D 0 ctx fn PG G tn t 0 G tn
     (OK (jump_to (if b then sb.cs_current_bb else entry.cs_current_bb) t))` by
    (gen_tac >> imp_res_tac emit_inst_extends >> irule assert_jnz_zero_path_ptr >> simp[] >>
     qexistsl [`op`,`s3`,`s4`] >> simp[]) >>
  Cases_on `b` >- suspend "true" >> suspend "false"
QED

Resume compile_assert_reason_frag_general_ptr[true]:
  markerLib.RESUME_TAC >> (
  gvs[] >>
  `MAP FDOM es_end.scopes = MAP FDOM es.scopes` by
    (qpat_x_assum `!tail. _` (qspec_then `[]` assume_tac) >>
     drule stmtSimDefsTheory.eval_read_preserves_scopes_dom >> simp[]) >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `marks` >>
  disj2_tac >> disj1_tac >> rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL ()`, `es_end`, `G`, `tn`,
                `OK (jump_to sb.cs_current_bb t)`] >>
  conj_tac
  >- (rpt gen_tac >>
      simp[eval_assert_reason_bind] >>
      simp[Once bind_def, return_def]) >>
  qx_gen_tac `H2` >> strip_tac >> BETA_TAC >>
  `valid_horizon cx st0 H2 es.storage_trace` by
    (`storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
       (irule storage_trace_frame_bind_all >>
        simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
     `valid_horizon cx st0 H2 (es_end with gas_obs := []).storage_trace` by
       simp[] >>
     qpat_x_assum `!tail. _` (qspec_then `[]` assume_tac) >>
     drule_all valid_horizon_frame >> simp[]) >>
  qpat_x_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `!H. _ ==> gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `stmt_post H2 ctx fn cx lctx cenv cenv sa sb es s0 (INL ())
     (es_end with gas_obs := []) (jump_to sb.cs_current_bb t)` by
    (irule assert_success_post >> simp[] >>
     qexistsl_tac [`e`, `op`, `s1`] >> simp[]) >>
  conj_tac >- metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES] >>
  disj1_tac >> simp[] >> gvs[stmt_post_def] >>
  gvs[ghost_inv_jump_to, jump_to_def, ghost_kept_def])
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
    (qpat_assum `!H. _ ==> gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     simp[ret_pc_ok_jump_to] >> irule ret_pc_ok_frame >>
     qexistsl [`cenv`,`s0`,`sa`] >> gvs[expr_post_def]) >>
  `!H. valid_horizon cx st0 H (es_end with gas_obs := []).storage_trace ==>
    stmt_state_rel H ctx fn cenv cx (es_end with gas_obs := [])
      (jump_to entry.cs_current_bb t) /\
    storage_well_formed_on cx (es_end with gas_obs := []) (FST H) /\
    ghost_inv H d cenv cx (es_end with gas_obs := []) G tn
      (jump_to entry.cs_current_bb t)` by
    (qx_gen_tac `H2` >> strip_tac >>
     qpat_assum `!H. _ ==> gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H2` assume_tac) >>
     fs[expr_post_def, stmt_state_rel_jump_to, jump_to_def,
       ghost_inv_jump_to, exit_result_def]) >>
  qpat_x_assum `stmt_frag_ptr _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o Q.SPEC `st0` o REWRITE_RULE [stmt_frag_ptr_def]) >>
  disch_then drule >> simp[block_is_terminated_def] >>
  disch_then (qspecl_then [`jump_to entry.cs_current_bb t`,`G`,`tn`] mp_tac) >>
  (impl_tac >- (gvs[stmt_state_rel_jump_to, jump_to_def, expr_post_def,
                    ghost_inv_jump_to, ghost_inv_gas_obs] >>
                   metis_tac[stmtFragPtrTheory.not_fresh_at_mono])) >>
  strip_tac >> suspend "compose"
QED

Resume compile_assert_reason_frag_general_ptr[compose]:
  irule assert_reason_false_outcome_prefix_ptr >>
  first_assum (irule_at (Pat `gas_outcome_ptr _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (fs[gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def] >>
      qpat_assum `!H. _ ==> gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
        (qspec_then `H1` (drule_then strip_assume_tac)) >>
      metis_tac[gas_path_ptr_erase]) >>
  rpt strip_tac >>
  qpat_assum `!H. _ ==> gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >> simp[]
QED

Finalise compile_assert_reason_frag_general_ptr
