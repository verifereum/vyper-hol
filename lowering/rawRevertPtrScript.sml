Theory rawRevertPtr
Ancestors
  rawRevertPtrTail rawRevertPtrBoundary exprSimRawRevertCore bodyPtrDefs
  exprSimDefs exprSimHypsDefs exprLoweringProps compileEnv loweringPosts
  gasSummaryComposePtr fragGasPathPtr gasSummaryCompose gasSummary
  gasOutcome gasExemptCert fragExec fragGasPath fragGasMode gasContext
  stmtSimLogArgsRun exprSimHash vyperTyping exprSimHyps exprPtrUnwrap
  vyperState vyperAST vyperValue vyperTypeSystem list arithmetic

Theorem raw_revert_vv_sim_ptr:
  expr_body_pre cenv cx env (Call ann RawRevert [e] dflt) es /\
  expr_sim_ptr d ctx PG func cenv cx (expr_type e) e es ==>
  expr_vv_sim_ptr d ctx PG func cenv cx ty (Call ann RawRevert [e] dflt) es
Proof
  strip_tac >> drule raw_revert_pre_bytes >> strip_tac >> gvs[] >>
  rewrite_tac[expr_vv_sim_ptr_def] >> rpt gen_tac >> strip_tac >>
  drule raw_revert_compile >> strip_tac >>
  `cs_extends sa sm` by metis_tac[cj 2 compile_expr_grows] >>
  `cs_extends sm sb` by metis_tac[raw_revert_extends] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (irule fn_has_code_split >> asm_rewrite_tac[]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (rw[gas_admissible_def] >> Cases_on `res` >- simp[expr_res_ok_def] >>
     qpat_x_assum `gas_admissible _ _ _`
       (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
     disch_then (qspecl_then [`gs`, `INR y`, `ee`] mp_tac) >>
     simp[eval_raw_revert_action] >>
     qpat_x_assum `bind _ _ _ = _` (fn th => simp[Once bind_def, th]) >>
     simp[expr_vv_res_ok_def, expr_res_ok_def]) >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ e _`
    (mp_tac o REWRITE_RULE [expr_sim_ptr_def]) >>
  disch_then (qspecl_then [`sa`, `sm`, `data`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  rewrite_tac[gas_outcome_ptr_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      rewrite_tac[eval_raw_revert_action] >>
      qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_ptr_at_marked]) >>
      gvs[]
      >- suspend "normal" >>
      Cases_on `res` >> gvs[expr_exit_def] >>
      simp[gas_summary_ptr_at_marked] >>
      qexistsl_tac [`INR y`, `es_end`, `G`, `tn`, `r`] >> simp[] >>
      conj_tac >- (irule gas_marked_exec_ptr_bind_exception >> simp[]) >>
      qpat_x_assum `expr_exit _ _` mp_tac >>
      Cases_on `r` >> Cases_on `y` >> simp[expr_exit_def] >>
      rename1 `Error err` >> Cases_on `err` >> simp[expr_exit_def]) >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  rewrite_tac[eval_raw_revert_action, ignore_bind_bind_return] >>
  irule gas_exempt_cert_error_value >> simp[]
QED

Resume raw_revert_vv_sim_ptr[normal]:
  `?bs. v = BytesV bs` by
    (qpat_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_ptr_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` assume_tac) >>
     drule_at (Pos last) (SRULE [SF ETA_ss] expr_body_pre_base_result) >>
     disch_then (qspecl_then [`env`, `cenv`, `BytesT (Dynamic cap)`] mp_tac) >>
     simp[] >>
     strip_tac >> Cases_on `v` >> gvs[value_has_type_def]) >>
  gvs[] >>
  `~t.vs_halted` by
    metis_tac[gas_marked_exec_ptr_exec, gas_marked_exec_def,
              gas_marked_path_exec, gas_path_normal] >>
  `evaluate_type (get_tenv cx) (expr_type e) =
    SOME (BaseTV (BytesT (Dynamic cap)))` by
    (drule_at Any expr_body_pre_type_evaluates >>
     simp[evaluate_type_def]) >>
  `lower_value compile_expr cenv (expr_type e) e sa = (data,sm) /\
   ptr_val_ok cx (expr_type e) (BytesV bs) data G tn t` by metis_tac[] >>
  drule_all raw_revert_post_path_ptr >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  rewrite_tac[gas_summary_ptr_at_marked] >>
  qexistsl_tac [`INR (Error (RuntimeError "raw_revert"))`, `es_end`,
                `G'`, `tn'`, `Abort Revert_abort t'`] >>
  simp[exit_result_def, expr_exit_def] >>
  irule (Q.INST [`right` |-> `[]`] gas_marked_exec_ptr_bind_normal
    |> REWRITE_RULE [APPEND_NIL]) >>
  qexistsl_tac [`G`, `es_end`, `t`, `tn`, `BytesV bs`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  simp[gas_marked_exec_ptr_def, raise_def]
QED

Finalise raw_revert_vv_sim_ptr

Theorem raw_revert_sim_ptr:
  expr_body_pre cenv cx env (Call ann RawRevert [e] dflt) es /\
  expr_sim_ptr d ctx PG func cenv cx (expr_type e) e es ==>
  expr_sim_ptr d ctx PG func cenv cx ty (Call ann RawRevert [e] dflt) es
Proof
  strip_tac >> irule expr_sim_ptr_of_vv >>
  conj_tac >- (qexists_tac `env` >> simp[]) >>
  irule raw_revert_vv_sim_ptr >> simp[] >> qexists_tac `env` >> simp[]
QED
