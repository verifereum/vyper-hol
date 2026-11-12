(* Actual-source counted conditional statement simulation. *)
Theory stmtSimAssert
Ancestors
  stmtSimDefs stmtSimProps stmtSimIfProps stmtSimAssertProps exprSimDefs exprSimProps loweringPosts
  gasOutcome gasSummary gasSummaryCompose gasContext gasCount fragGasPath fragGasMode
  list rich_list finite_map pred_set fragExec localPtrsProps loweringSlice
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding vyperInterpreter vyperState vyperValue vyperEvalPreservesScopes
  vyperExprNoControl vyperValueOperation vyperStatePreservation
  venomExecSemantics venomExecProofs venomInst venomState integer_word
Libs
  monadsyntax intLib

(* The continuation after the condition only appends storage observations. *)
val assert_cont_frame_tac =
  simp[vyperStorageTraceTheory.storage_trace_frame_cond,
       vyperStorageTraceTheory.storage_trace_frame_return,
       vyperStorageTraceTheory.storage_trace_frame_raise];

(* The condition left the storage domain: the whole Assert is a bad-storage
   run under the condition's marks. *)
val assert_out_of_domain_tac =
  simp[eval_assert_bind] >>
  irule gasStorageTheory.gas_bad_storage_at_bind_left >>
  assert_cont_frame_tac >>
  irule gasStorageTheory.gas_bad_storage_at_counted_prefix >>
  qpat_assum `gas_marked_exec _ _ (bind _ _) _ _ _ _ _` (irule_at Any) >>
  simp[];

Theorem compile_assert_frag:
  !ctx func cx lctx RetQ cenv ty e ak es.
    (ak = AssertBare \/ ak = AssertUnreachable) /\
    expr_type e = BaseT BoolT /\
    expr_sim ctx func cenv cx (BaseT BoolT) e es /\
    (!sa op sb. lower_value compile_expr cenv (BaseT BoolT) e sa = (op, sb) ==>
                cs_extends sa sb) ==>
    stmt_frag ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty (Assert e ak))
      (eval_stmt cx (Assert e ak)) es
Proof
  rpt gen_tac >> strip_tac >> (
  simp[stmt_frag_def, stmt_framed_frag_def] >> rpt gen_tac >> strip_tac >>
  drule_at (Pat `stmt_env _ _ _ _ _ = _`) compile_assert_parts >>
  (impl_tac >- simp[]) >> strip_tac >> gvs[] >>
  `cs_extends sa s1` by metis_tac[] >>
  drule_all assert_compiler_code >> strip_tac >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[assert_expr_admissible] >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `s1`, `op`, `s0`] mp_tac) >>
  impl_tac >- simp[] >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> BETA_TAC >>
  disch_then (qx_choose_then `marks` strip_assume_tac) >>
  qexists_tac `marks`
  >- (disj1_tac >> simp[eval_assert_bind] >>
      irule gasStorageTheory.gas_bad_storage_at_bind_left >>
      assert_cont_frame_tac >> first_assum ACCEPT_TAC)
  >- (reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
      >- (disj1_tac >> assert_out_of_domain_tac) >>
      disj2_tac >> disj1_tac >> suspend "normal")
  >- (reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
      >- (disj1_tac >> assert_out_of_domain_tac) >>
      disj2_tac >> disj1_tac >> suspend "exception") >>
  disj2_tac >> disj2_tac >> metis_tac[assert_expr_exempt])
QED

Resume compile_assert_frag[normal]:
  markerLib.RESUME_TAC >> (
  `?H0. valid_horizon cx st0 H0 es_end.storage_trace` by
    metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `!H. valid_horizon cx st0 H es_end.storage_trace ==>
       valid_horizon cx st0 H es.storage_trace` by
    (qpat_assum `gas_marked_exec _ _ (bind _ _) _ _ _ _ _`
       (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                          gas_marked_exec_valid_prefix)) >>
     impl_tac >- simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
          vyperStorageTraceTheory.storage_trace_frame_read_result,
          vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
     simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> ?v. _` (qspec_then `H0` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `eval_stmt cx (Assert e ak)` >>
  qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
  simp[gas_marked_exec_def, gas_marked_path_def] >> strip_tac >>
  `~t.vs_halted` by metis_tac[gas_path_normal] >>
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
    (gvs[expr_post_def, expr_val_rel_def, evaluate_type_def, is_word_type_def,
         typed_val_to_w256_def, val_to_w256_def] >>
     metis_tac[]) >>
  `gas_path ctx func t 0
     (OK (jump_to (if b then sb.cs_current_bb else s5.cs_current_bb) t))` by
    (imp_res_tac emit_inst_extends >>
     irule assert_jnz_zero_path >> simp[] >>
     qexistsl_tac [`op`, `s3`, `s4`] >> simp[]) >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `!sa op sb. _` kall_tac >>
  Cases_on `b`
  >- suspend "true"
  >> suspend "false")
QED

Resume compile_assert_frag[exception]:
  markerLib.RESUME_TAC >> (
  `?H0. valid_horizon cx st0 H0 es_end.storage_trace` by
    metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  Cases_on `res`
  >- (qpat_x_assum `!H. valid_horizon _ _ H _ ==> expr_exit _ _`
        (qspec_then `H0` mp_tac) >> simp[expr_exit_def]) >>
  qexistsl_tac [`INR y`, `es_end`, `r`] >>
  conj_tac
  >- (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
      simp[gas_marked_exec_def] >> strip_tac >> simp[] >>
      gen_tac >> asm_simp_tac (srw_ss()) [eval_assert_bind] >>
      simp[Once bind_def]) >>
  disj2_tac >> simp[stmt_exit_def] >> rpt strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> expr_exit _ _`
    (qspec_then `H` mp_tac) >>
  simp[] >> metis_tac[expr_exit_INR_type])
QED

Resume compile_assert_frag[true]:
  markerLib.RESUME_TAC >> (
  gvs[] >>
  qexistsl_tac [`INL ()`, `es_end`, `OK (jump_to sb.cs_current_bb t)`] >>
  conj_tac
  >- (conj_tac
      >- (rpt gen_tac >>
          asm_simp_tac (srw_ss()) [eval_assert_bind] >>
          simp[Once bind_def, return_def]) >>
      metis_tac[gas_path_then, arithmeticTheory.ADD_CLAUSES]) >>
  disj1_tac >> simp[] >> rpt strip_tac >>
  `stmt_state_rel H ctx func cenv cx es s0 /\
   expr_post H ctx func cenv cx e es sa s1 s0 (es_end with gas_obs := [])
     (BoolV T) op t` by metis_tac[] >>
  irule assert_success_post >>
  simp[] >> conj_tac
  >- (qpat_x_assum `!tail. _` (qspec_then `[]` assume_tac) >>
      drule stmtSimDefsTheory.eval_read_preserves_scopes_dom >> simp[]) >>
  qexistsl_tac [`e`, `op`, `s1`] >> first_assum ACCEPT_TAC)
QED

Resume compile_assert_frag[false]:
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
  `gas_path ctx func (jump_to s5.cs_current_bb t) 0 (Abort a u)` by
    (irule emit_abort_zero_path >> simp[jump_to_def] >>
     qexistsl_tac [`if ak = AssertBare then REVERT else INVALID`,
                   `if ak = AssertBare then [Lit 0w; Lit 0w] else []`, `s5`, `s6`] >>
     gvs[jump_to_def, Abbr `ak`]) >>
  qexistsl_tac [`INR (AssertException
      (if ak = AssertBare then "" else "UNREACHABLE"))`, `es_end`, `Abort a u`] >>
  conj_tac
  >- (conj_tac
      >- (gen_tac >> simp[Abbr `ak`, eval_assert_bind] >>
          simp[Once bind_def, raise_def]) >>
      metis_tac[gas_path_then, arithmeticTheory.ADD_CLAUSES]) >>
  disj2_tac >> simp[exit_result_def, stmt_exit_def])
QED

Finalise compile_assert_frag

