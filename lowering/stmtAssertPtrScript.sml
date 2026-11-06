(*
 * Pointer-checked assertions with no reason: the twin of stmtSimAssert's
 * compile_assert_frag over stmt_frag_ptr.  The condition's JNZ takes an
 * untainted operand (ptr_val_ok) and keeps the ghost; the failing block's
 * REVERT 0 0 or INVALID reads no memory.
 *
 * TOP-LEVEL:
 *   assert_jnz_zero_path_ptr -- the JNZ as a pointer-checked edge
 *   compile_assert_frag_ptr  -- the statement
 *)
Theory stmtAssertPtr
Ancestors
  stmtAbortPtr stmtFragPtr bodyPtrDefs fragGasPathPtr gasSummaryComposePtr gasCount fragGasSeqPtr
  stmtSimAssertProps stmtSimDefs stmtSimProps exprSimDefs exprSimProps
  loweringPosts gasContext gasSummary gasExemptCert fragExec
  stmtLowering exprLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding vyperInterpreter vyperState
  ptrSafeRun ptrDiscipline codegenRel contextCodegenRel
  venomExecSemantics venomExecProps venomInst
  venomState
  stmtSimIfProps gasSummaryCompose gasCount fragGasPath fragGasMode
  list rich_list finite_map pred_set localPtrsProps loweringSlice
  vyperValue vyperEvalPreservesScopes vyperExprNoControl
  vyperValueOperation vyperStatePreservation venomExecProofs integer_word
Libs
  monadsyntax

Theorem assert_jnz_zero_path_ptr:
  sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++
    [mk_inst sa.cs_next_id JNZ [op; Label lt; Label lf] []] /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  eval_operand op s = SOME (if b then 1w else 0w) /\ op_taint tn op = {} ==>
  gas_path_ptr D 0 ctx func PG G tn s 0 G tn
    (OK (jump_to (if b then lt else lf) s))
Proof
  strip_tac >> drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sa.cs_current_insts) =
    SOME (mk_inst sa.cs_next_id JNZ [op; Label lt; Label lf] [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst 0 ctx (mk_inst sa.cs_next_id JNZ [op; Label lt; Label lf] []) s =
     OK (jump_to (if b then lt else lf) s)` by
    (simp[step_inst_non_invoke, mk_inst_def] >>
     drule step_jnz_behavior >>
     disch_then (qspecl_then [`lt`, `lf`, `sa.cs_next_id`] mp_tac) >>
     simp[mk_inst_def] >> Cases_on `b` >> simp[]) >>
  `ptr_safe_step D 0 0 ctx func PG G tn
     (mk_inst sa.cs_next_id JNZ [op; Label lt; Label lf] []) s` by
    (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          allocas_from_def, source_memory_write_ranges_def,
          source_memory_read_ranges_def] >>
     simp[mk_inst_def, op_taint_def] >>
     qx_gen_tac `x` >> Cases_on `x = op` >> gvs[op_taint_def] >>
     Cases_on `x` >> simp[]) >>
  `gas_path_ptr_edge D 0 ctx func PG G tn s 0 G tn
     (OK (jump_to (if b then lt else lf) s))` by
    (rewrite_tac[gas_path_ptr_edge_def] >> simp[] >>
     `gas_count_step 0 ctx
        (mk_inst sa.cs_next_id JNZ [op; Label lt; Label lf] []) s = 0` by
       simp[gas_count_step_def, mk_inst_def] >>
     qexists_tac `0` >> simp[is_terminator_def] >>
     disj2_tac >> disj1_tac >> qexists_tac `if b then lt else lf` >> simp[]) >>
  `~(jump_to (if b then lt else lf) s).vs_halted` by simp[jump_to_def] >>
  drule (cj 1 gas_path_ptr_rules) >> strip_tac >>
  metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES]
QED

(* compile_assert_frag with the pointer check. *)
Theorem compile_assert_frag_ptr:
  !d ctx PG func cx lctx RetQ cenv ty e ak es.
    (ak = AssertBare \/ ak = AssertUnreachable) /\
    expr_type e = BaseT BoolT /\
    expr_sim_ptr d ctx PG func cenv cx (BaseT BoolT) e es /\
    (!sa op sb. lower_value compile_expr cenv (BaseT BoolT) e sa = (op, sb) ==>
                cs_extends sa sb) ==>
    stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assert e ak)) (eval_stmt cx (Assert e ak)) es
Proof
  rpt gen_tac >> strip_tac >> (
  simp[stmt_frag_ptr_def] >> rpt gen_tac >> strip_tac >>
  drule_at (Pat `stmt_env _ _ _ _ _ = _`) compile_assert_parts >>
  (impl_tac >- simp[]) >> strip_tac >> gvs[] >>
  `cs_extends sa s1` by metis_tac[] >>
  drule_all assert_compiler_code >> strip_tac >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[assert_expr_admissible] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x`
    by metis_tac[ret_pc_ok_def] >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_ptr_def]) >>
  disch_then drule >> simp[] >>
  disch_then (qspecl_then [`s0`, `G0`, `tn0`] mp_tac) >> simp[] >>
  simp[gas_outcome_ptr_def, gas_summary_ptr_at_def] >>
  disch_then (qx_choose_then `marks` (DISJ_CASES_THEN assume_tac))
  >- (qexists_tac `marks` >> disj1_tac >>
      qpat_x_assum `?res es_end G tn r. _` strip_assume_tac >> gvs[]
      >- suspend "normal"
      >> suspend "exception") >>
  qexists_tac `marks` >> disj2_tac >>
  pop_assum strip_assume_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  irule assert_expr_exempt >> simp[])
QED

Resume compile_assert_frag_ptr[normal]:
  markerLib.RESUME_TAC >> (
  qmatch_goalsub_abbrev_tac `eval_stmt cx (Assert e ak)` >>
  `~t.vs_halted` by metis_tac[gas_path_ptr_ok_not_halted] >>
  `?b. v = BoolV b` by
    (Cases_on `eval_stmt cx (Assert e ak)
       (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` >>
     drule_all gas_admissible_result >> strip_tac >>
     drule_at (Pat `eval_stmt _ _ _ = _`) eval_assert_forced_ok >>
     disch_then (qspec_then `lctx` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     qpat_x_assum `!tail. _ = _` (qspec_then `[]` assume_tac) >>
     gvs[bind_def]) >>
  `eval_operand op t = SOME (if b then 1w else 0w)` by
    gvs[expr_post_def, expr_val_rel_def, evaluate_type_def, is_word_type_def,
        typed_val_to_w256_def, val_to_w256_def] >>
  `op_taint tn op = {}` by gvs[ptr_val_ok_def] >>
  `gas_path_ptr (cx_dead cx) 0 ctx func PG G tn t 0 G tn
     (OK (jump_to (if b then sb.cs_current_bb else s5.cs_current_bb) t))` by
    (imp_res_tac emit_inst_extends >>
     irule assert_jnz_zero_path_ptr >> simp[] >>
     qexistsl_tac [`op`, `s3`, `s4`] >> simp[]) >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `!sa op sb. _` kall_tac >>
  Cases_on `b`
  >- suspend "true"
  >> suspend "false")
QED

Resume compile_assert_frag_ptr[exception]:
  markerLib.RESUME_TAC >> (
  Cases_on `res` >- fs[expr_exit_def] >>
  qexistsl_tac [`INR y`, `es_end`, `G`, `tn`, `r`] >>
  conj_tac
  >- (gen_tac >> asm_simp_tac (srw_ss()) [eval_assert_bind] >>
      simp[Once bind_def]) >>
  conj_tac >- simp[] >>
  disj2_tac >> simp[stmt_exit_ptr_def] >>
  metis_tac[expr_exit_INR_type])
QED

Resume compile_assert_frag_ptr[true]:
  markerLib.RESUME_TAC >> (
  gvs[] >>
  `stmt_post ctx func cx lctx cenv cenv sa sb es s0 (INL ())
     (es_end with gas_obs := []) (jump_to sb.cs_current_bb t)` by
    (irule assert_success_post >> simp[] >>
     qexistsl_tac [`e`, `es`, `op`, `s1`] >> simp[]) >>
  qexistsl_tac [`INL ()`, `es_end`, `G`, `tn`,
                `OK (jump_to sb.cs_current_bb t)`] >>
  conj_tac
  >- (rpt gen_tac >>
      asm_simp_tac (srw_ss()) [eval_assert_bind] >>
      simp[Once bind_def, return_def]) >>
  conj_tac >- metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES] >>
  disj1_tac >> simp[] >> gvs[stmt_post_def] >>
  gvs[ghost_inv_jump_to, jump_to_def, ghost_kept_def])
QED

Resume compile_assert_frag_ptr[false]:
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
  `gas_path_ptr (cx_dead cx) 0 ctx func PG G tn
     (jump_to s5.cs_current_bb t) 0 G tn (Abort a u)` by
    (irule emit_abort_zero_path_ptr >> simp[jump_to_def] >>
     qexistsl_tac [`if ak = AssertBare then REVERT else INVALID`,
                   `if ak = AssertBare then [Lit 0w; Lit 0w] else []`,
                   `s5`, `s6`] >>
     gvs[jump_to_def, Abbr `ak`] >>
     irule ptr_inst_ok_abort_zero >> simp[]) >>
  qexistsl_tac [`INR (AssertException
      (if ak = AssertBare then "" else "UNREACHABLE"))`, `es_end`, `G`, `tn`,
      `Abort a u`] >>
  conj_tac
  >- (gen_tac >> simp[Abbr `ak`, eval_assert_bind] >>
      simp[Once bind_def, raise_def]) >>
  conj_tac >- metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES] >>
  disj2_tac >> simp[exit_result_def, stmt_exit_ptr_def])
QED

Finalise compile_assert_frag_ptr
