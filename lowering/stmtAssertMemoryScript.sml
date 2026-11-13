(* Actual-source counted conditional statement simulation. *)
Theory stmtAssertMemory
Ancestors
  exprSimMemDefs bodyMemoryDefs fragGasPathMem stmtSimAssert instMemFrontier
  stmtSimDefs stmtSimForced stmtSimProps stmtSimIfProps stmtSimAssertProps exprSimDefs exprSimProps loweringPosts
  gasOutcome gasSummary gasSummaryCompose gasContext gasCount fragGasPath fragGasMode
  list rich_list finite_map pred_set fragExec localPtrsProps loweringSlice
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding vyperInterpreter vyperState vyperValue vyperEvalPreservesScopes
  vyperExprNoControl vyperValueOperation vyperStatePreservation
  venomExecSemantics venomExecProofs venomInst venomState integer_word
Libs
  monadsyntax intLib

(* Historical fixed-result proof (retained verbatim):
Proof
  rpt gen_tac >> strip_tac >> simp[stmt_frag_mem_def] >> rpt gen_tac >>
  strip_tac >> gvs[] >> (
    qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
    simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def, comp_bind_def,
         comp_ignore_bind_def, comp_return_def] >>
    Cases_on `lower_value compile_expr cenv (BaseT BoolT) e sa` >>
    rename1 `_ = (op, s1)` >> simp[] >>
    Cases_on `fresh_label "assert_ok" s1` >> rename1 `_ = (ok, s2)` >> simp[] >>
    Cases_on `fresh_label "assert_fail" s2` >> rename1 `_ = (fl, s3)` >> simp[] >>
    Cases_on `emit_inst JNZ [op; Label ok; Label fl] [] s3` >>
    rename1 `_ = (u4, s4)` >> simp[] >>
    Cases_on `new_block fl s4` >> rename1 `_ = (x5, s5)` >> simp[] >>
    qmatch_goalsub_abbrev_tac `emit_inst opc ops [] s5` >>
    Cases_on `emit_inst opc ops [] s5` >> rename1 `_ = (u6, s6)` >> simp[] >>
    Cases_on `new_block ok s6` >> rename1 `new_block ok s6 = (x7, s7)` >>
    simp[] >> strip_tac >> gvs[] >>
    imp_res_tac fresh_label_props >> imp_res_tac new_block_props >>
    imp_res_tac emit_inst_extends >>
    drule lower_value_bool_grows_mem >> strip_tac >>
    `cs_extends s1 s2 /\ cs_extends s2 s3 /\
     cs_extends s3 s4 /\ cs_extends s4 s5 /\ cs_extends s5 s6 /\
     cs_extends s6 s7` by
      metis_tac[cs_extends_fresh_label, cs_extends_new_block,
                cs_appends_emit_helpers, cs_appends_def] >>
    `fn_has_code sa s1 func /\ fn_has_code s4 s5 func /\
     fn_has_code s5 s6 func` by
      metis_tac[fn_has_code_split, fn_has_code_mid, cs_extends_trans,
                cs_extends_refl] >>
    `lookup_block s4.cs_current_bb func.fn_blocks =
       SOME <| bb_label := s4.cs_current_bb;
               bb_instructions := s4.cs_current_insts |>` by
      metis_tac[fn_has_code_new_block] >>
    drule_at (Pat `eval_stmt _ _ _ = _`) eval_assert_forced_ok_mem >>
    disch_then (qspec_then `lctx` mp_tac) >>
    (impl_tac >- simp[]) >> strip_tac >>
    `s3.cs_current_bb = s1.cs_current_bb /\
     s3.cs_current_insts = s1.cs_current_insts` by metis_tac[] >>
    `emit_inst JNZ [op; Label ok; Label fl] [] s3 = ((), s4)` by
      fs[Abbr `ops`] >>
    `r <> INR (Error (RuntimeError "convert empty bytes to signed"))` by
      (strip_tac >> gvs[]) >>
    drule_all cond_jump_frag_mem >> strip_tac
    >- (qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _` kall_tac >>
        qpat_x_assum `!sa' op' sb'. _` kall_tac >>
        qpat_x_assum `eval_stmt _ _ _ = _` kall_tac >>
        rpt (qpat_x_assum `_.cs_blocks = _` kall_tac) >>
        qpat_x_assum `lookup_block _ _ = _` kall_tac >>
        Cases_on `b` >> gvs[]
        >- (disj1_tac >> rename1 `stmt_state_rel ctx func cenv cx es' sv` >>
            `return_buf_frame d cenv s7 sv` by
              (irule return_buf_frame_frame >> metis_tac[]) >>
            qexists_tac `jump_to s7.cs_current_bb sv` >>
            simp[stmt_lands_def, stmt_state_rel_jump_to, cenv_top_ext_refl,
                 block_is_terminated_def, return_buf_frame_jump_to] >>
            simp[jump_to_def, lookup_var_def] >>
            fs[lookup_var_def, jump_to_def, allocaHistoryTheory.alloca_history_def]) >>
        rename1 `stmt_state_rel ctx func cenv cx es' sv` >>
        qmatch_goalsub_abbrev_tac `stmt_exit RetQ es' rres _` >>
        `?fuel r. run_from fuel ctx func (jump_to s5.cs_current_bb sv) = r /\
                  exit_result r /\ stmt_exit RetQ es' rres r /\
                  mem_safe_run fuel ctx func (jump_to s5.cs_current_bb sv)` by
          (irule emit_abort_exit_mem >>
           conj_tac >- simp[jump_to_def] >>
           qexistsl_tac [`opc`, `ops`, `s5`, `s6`] >>
           fs[markerTheory.Abbrev_def, jump_to_def, control_abort_frontier] >>
           gvs[expr_exit_def] >> metis_tac[step_revert_zero_mem, step_invalid_mem]) >>
        disj2_tac >>
        qpat_x_assum `!fuel. (!e. run_from fuel ctx func (jump_to _ sv) <> Error e) ==> _`
          (qspec_then `fuel` mp_tac) >>
        (impl_tac >- metis_tac[exit_result_not_error]) >> strip_tac >>
        qexists_tac `fuel'` >> gvs[]) >>
    disj2_tac >> qexists_tac `fuel` >> Cases_on `r` >> gvs[stmt_exit_def] >>
    disj1_tac >> metis_tac[expr_exit_INR_type])
QED
*)
Theorem compile_assert_frag_mem:
  !d ctx func cx lctx RetQ cenv ty e ak es.
    (ak = AssertBare \/ ak = AssertUnreachable) /\
    expr_type e = BaseT BoolT /\
    expr_sim_mem ctx func cenv cx (BaseT BoolT) e es /\
    (!sa op sb. lower_value compile_expr cenv (BaseT BoolT) e sa = (op, sb) ==>
                cs_extends sa sb) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty (Assert e ak))
      (eval_stmt cx (Assert e ak)) es
Proof
  rpt gen_tac >> strip_tac >> (
  simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  drule_at (Pat `stmt_env _ _ _ _ _ = _`) compile_assert_parts >>
  (impl_tac >- simp[]) >> strip_tac >> gvs[] >>
  `cs_extends sa s1` by metis_tac[] >>
  drule_all assert_compiler_code >> strip_tac >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (drule (cj 2 compile_expr_grows) >> strip_tac >>
     imp_res_tac fresh_label_props >> imp_res_tac new_block_props >>
     imp_res_tac emit_inst_extends >> gvs[] >> decide_tac) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[assert_expr_admissible] >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `s1`, `op`, `s0`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `!sa op sb. _` kall_tac >>
  qmatch_goalsub_abbrev_tac `eval_stmt cx (Assert e ak)` >>
  mp_tac eval_assert_bind >> (impl_tac >- simp[Abbr `ak`]) >>
  disch_then (fn th => rewrite_tac[th]) >>
  irule forced_then_outcome >> BETA_TAC >> rpt conj_tac
  >- (rpt strip_tac >> simp[stmt_exit_def] >> metis_tac[expr_exit_INR_type])
  >- (rpt gen_tac >> rw[] >>
      simp[vyperStorageTraceTheory.storage_trace_frame_return,
           vyperStorageTraceTheory.storage_trace_frame_raise]) >>
  qexists_tac `\H v ee t.
    expr_post H ctx func cenv cx e es sa s1 s0 ee v op t /\
    expr_store_bound cx (expr_type e) v op t /\
    t.vs_current_bb = s1.cs_current_bb /\
    t.vs_inst_idx = LENGTH s1.cs_current_insts /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next` >>
  BETA_TAC >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >> suspend "continue")
QED

Resume compile_assert_frag_mem[continue]:
  markerLib.RESUME_TAC >> (
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `(ee with gas_obs := []) = ee` by
    simp[evaluation_state_component_equality] >>
  `?b. v = BoolV b` by
    (Cases_on `eval_stmt cx (Assert e ak) (es with gas_obs := gs)` >>
     `stmt_res_ok lctx q` by metis_tac[gas_admissible_result] >>
     drule_at (Pat `eval_stmt _ _ _ = _`) eval_assert_forced_ok >>
     disch_then (qspec_then `lctx` mp_tac) >>
     (impl_tac >- simp[Abbr `ak`]) >> strip_tac >>
     gvs[bind_def]) >>
  `eval_operand op t = SOME (if b then 1w else 0w)` by
    gvs[expr_post_def, expr_val_rel_def, evaluate_type_def, is_word_type_def,
        typed_val_to_w256_def, val_to_w256_def] >>
  `gas_path_mem ctx func t 0
     (OK (jump_to (if b then sb.cs_current_bb else s5.cs_current_bb) t))` by
    (imp_res_tac emit_inst_extends >>
     irule assert_jnz_zero_path_mem >> simp[] >>
     qexistsl_tac [`op`, `s3`, `s4`] >> simp[]) >>
  Cases_on `b`
  >- suspend "true"
  >> suspend "false")
QED

Resume compile_assert_frag_mem[true]:
  markerLib.RESUME_TAC >> (
  gvs[] >>
  qexistsl_tac [`INL ()`, `ee`, `OK (jump_to sb.cs_current_bb t)`] >>
  simp[return_def, gas_marked_path_def] >>
  disj1_tac >> qx_gen_tac `H1` >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (qspec_then `H1` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  drule_all assert_success_post_mem >> simp[])
QED

Resume compile_assert_frag_mem[false]:
  markerLib.RESUME_TAC >> (
  gvs[] >>
  `?a u. step_inst_base
      (mk_inst s5.cs_next_id (if ak = AssertBare then REVERT else INVALID)
        (if ak = AssertBare then [Lit 0w; Lit 0w] else []) [])
      (jump_to s5.cs_current_bb t) = Abort a u /\
      expr_exit (INR (AssertException
        (if ak = AssertBare then "" else "UNREACHABLE")) : unit + exception)
        (Abort a u)` by
    (simp[Abbr `ak`, expr_exit_def] >>
     metis_tac[step_revert_zero, step_invalid]) >>
  `gas_path_mem ctx func (jump_to s5.cs_current_bb t) 0 (Abort a u)` by
    (irule emit_abort_zero_path_mem >> simp[jump_to_def] >>
     qexistsl_tac [`if ak = AssertBare then REVERT else INVALID`,
                   `if ak = AssertBare then [Lit 0w; Lit 0w] else []`, `s5`, `s6`] >>
     gvs[jump_to_def, Abbr `ak`] >>
     simp[below_frontier_REVERT, eval_operand_def] >>
     irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  qexistsl_tac [`INR (AssertException
      (if ak = AssertBare then "" else "UNREACHABLE"))`, `ee`, `Abort a u`] >>
  simp[raise_def, gas_marked_path_def] >>
  conj_tac >- metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES] >>
  simp[exit_result_def, stmt_exit_def] >> fs[Abbr `ak`])
QED

Finalise compile_assert_frag_mem

