(*
 * Expression simulation: calls (#636, Calls)
 *
 * The case lemmas of compile_expr_sim (exprSimMain) for the call targets
 * but internal calls.  Proved: send (compile_send_sim, by exprSimSend's
 * compile_send_case_sim, row 2 of #636's Calls table), selfdestruct
 * (compile_selfdestruct_case and compile_selfdestruct_sim), and, vacuously,
 * the creates (compile_create_sim: expr_sim_pre excludes them, below).
 * Each other lemma is its piece in a leaf theory exprSimCall*, by row of
 * that table:
 *   1 extcall/staticcall in SOME oracle mode, including reverts and
 *     default_return_value (#553): compile_extcall_sim
 *   3 raw_call (#554): compile_raw_call_sim; raw_call of msg.data:
 *     compile_raw_call_calldata_sim
 *   4 raw_log, raw_revert: compile_raw_log_sim, compile_raw_revert_sim
 *
 * Selfdestruct now uses the H-indexed account/halt agreement, including
 * EIP-6780 deletion and empty return data. Static execution aborts, and
 * recipient overflow retains the whole-call gas exemption certificate.
 *
 * Unprovable as the definitions stand (for raw_call and the creates, once
 * expr_sim_pre's exclusion of them, below, is lifted):
 *   - compile_raw_call_calldata_sim, and the create lowerings: they allocate with DALLOCA, at vs_fmp, which
 *     stmt_state_rel does not relate to the ALLOCA allocations, so
 *     expr_post's memory frame does not follow (#668, #636 Infrastructure
 *     row 2).
 *
 * A call, staticcall or delegate raw_call takes its outcome from the
 * oracle, as the lowered CALL/STATICCALL/DELEGATECALL does.  expr_sim_pre
 * still excludes delegate raw_calls and the creates (~expr_has_evm_run e).
 * Selfdestruct is rooted and covers HaltException through expr_exit and
 * the horizon-uniform halt_exit postcondition.
 *
 * Internal calls (row 6) have no lemma: expr_sim_pre excludes them
 * (int_calls_expr e = []) until #638 states the INVOKE hypothesis.
 *)

Theory exprSimCalls
Ancestors
  list  exprSimHyps exprSimSend vyperAST
  exprSimCallExtcall exprSimCallRawCall exprSimCallRawCallCalldata
  exprSimCallRawLog exprSimCallRawRevert
  selfdestructHalt gasContext gasOutcome gasStorage gasSummary gasSummaryCompose
  gasExemptOrigin gasExemptCert gasNormalPrefix fragGasMode fragGasPath
  exprSimDefs exprSimHypsDefs exprSimSource exprLowering exprLoweringProps
  emitHelper emitHelperProps builtinSystem loweringPosts loweringStateRelDefs
  vyperState vyperSystemControl vyperStorageTrace vyperStorageFootprint
  venomExecSemantics venomInst venomState rich_list compileEnv fragExec

Theorem compile_extcall_sim:
  !cenv ann is_static skip sig opts args dflt.
    expr_sim_below cenv (expr_size (Call ann (ExtCall is_static skip sig opts) args dflt)) ==>
    expr_vv_ok cenv (Call ann (ExtCall is_static skip sig opts) args dflt)
Proof
  ACCEPT_TAC extcall_expr_vv_ok
QED

Theorem compile_send_sim:
  !cenv ann has_gas args dflt.
    expr_sim_below cenv (expr_size (Call ann (Send has_gas) args dflt)) ==>
    expr_vv_ok cenv (Call ann (Send has_gas) args dflt)
Proof
  ACCEPT_TAC compile_send_case_sim
QED

Theorem compile_raw_call_sim:
  !cenv ann flags args dflt.
    expr_sim_below cenv (expr_size (Call ann (RawCallTarget flags) args dflt)) ==>
    expr_vv_ok cenv (Call ann (RawCallTarget flags) args dflt)
Proof
  ACCEPT_TAC raw_call_expr_vv_ok
QED

Theorem compile_raw_call_calldata_sim:
  !cenv ann flags args dflt.
    expr_sim_below cenv (expr_size (Call ann (RawCallCalldataTarget flags) args dflt)) ==>
    expr_vv_ok cenv (Call ann (RawCallCalldataTarget flags) args dflt)
Proof
  ACCEPT_TAC raw_call_calldata_expr_vv_ok
QED

Theorem compile_raw_log_sim:
  !cenv ann args dflt.
    expr_sim_below cenv (expr_size (Call ann (RawLog) args dflt)) ==>
    expr_vv_ok cenv (Call ann (RawLog) args dflt)
Proof
  ACCEPT_TAC raw_log_expr_vv_ok
QED

Theorem compile_raw_revert_sim:
  !cenv ann args dflt.
    expr_sim_below cenv (expr_size (Call ann (RawRevert) args dflt)) ==>
    expr_vv_ok cenv (Call ann (RawRevert) args dflt)
Proof
  ACCEPT_TAC raw_revert_expr_vv_ok
QED

(* The singleton address operand is the only normal prefix. *)
Theorem selfdestruct_pre_arg[local]:
  expr_body_pre cenv cx env (Call ann SelfDestructTarget args dflt) es ==>
  ?e. args = [e] /\ expr_type e = BaseT AddressT /\
      expr_body_pre cenv cx env e es
Proof
  strip_tac >>
  `?e. args = [e]` by
    gvs[expr_body_pre_def, vyperTypeSystemTheory.well_typed_expr_def,
        LENGTH_EQ_NUM_compute] >>
  gvs[expr_body_pre_def, vyperTypeSystemTheory.well_typed_expr_def,
      byte_widths_expr_def, allocLimitsTheory.alloc_limits_expr_def,
      vyperTypeCallGraphTheory.int_calls_expr_def,
      supportedExprTraverseTheory.expr_has_evm_run_thm,
      supportedExprTraverseTheory.supported_expr_exists_def,
      supportedExprTraverseTheory.expr_evm_run_root_def]
QED

Theorem selfdestruct_compile[local]:
  compile_expr cenv ty (Call ann SelfDestructTarget [e] dflt) sa = (vv,sb) ==>
  ?op sm. lower_value compile_expr cenv (BaseT AddressT) e sa = (op,sm) /\
    compile_selfdestruct op sm = ((),sb) /\ vv = StackValue ann (Lit 0w)
Proof
  simp[compile_expr_call, compile_call_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >> Cases_on `p_1` >> simp[]
QED

Theorem selfdestruct_extends[local]:
  compile_selfdestruct op sm = (u,sb) ==> cs_extends sm sb
Proof
  rw[compile_selfdestruct_def, emit_void_def, emit_inst_def,
     comp_bind_def, comp_return_def, fresh_id_def, emit_def,
     cs_extends_def] >>
  qexists_tac `[]` >> simp[IS_PREFIX_APPEND]
QED

Theorem selfdestruct_tail_path[local]:
  compile_selfdestruct op sm = ((),sb) /\ fn_has_code sm sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  step_inst_base (mk_inst sm.cs_next_id SELFDESTRUCT [op] []) s = r /\
  exit_result r ==> gas_path ctx func s 0 r
Proof
  pure_rewrite_tac[compile_selfdestruct_def, emit_void_def, GSYM emit_inst_def] >>
  strip_tac >>
  drule emit_inst_extends >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sm.cs_current_insts) =
    SOME (mk_inst sm.cs_next_id SELFDESTRUCT [op] [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  irule (cj 3 gas_path_rules) >> simp[] >>
  simp[gas_path_edge_def] >> qexists_tac `0` >>
  simp[step_inst_non_invoke, mk_inst_def,
       gasCountTheory.gas_count_step_def]
QED

Theorem selfdestruct_tail_sim[local]:
  compile_selfdestruct op sm = ((),sb) /\ fn_has_code sm sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  valid_horizon cx st0 H0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
       state_rel H func cenv cx ee s) /\
  eval_operand op s = SOME aw /\ dest_AddressV v = SOME (w2w aw) /\
  (~cx.txn.is_static ==> ~selfdestruct_overflows cx (w2w aw) ee.accounts) ==>
  ?(res:eval_result + exception) fin r.
    gas_marked_exec F (ctx,func) (selfdestruct_tail cx v)
      (ee,s) [] res fin r /\ fin.storage_trace = ee.storage_trace /\
    exit_result r /\ expr_exit res r /\
    (!H. valid_horizon cx st0 H fin.storage_trace ==>
         halt_exit H cx (fin with gas_obs := []) res r)
Proof
  strip_tac >>
  `state_rel H0 func cenv cx ee s` by metis_tac[] >>
  `halt_rel H0 cx ee s` by metis_tac[halt_rel_from_state_rel] >>
  `s.vs_call_ctx.cc_address = cx.txn.target /\
   s.vs_call_ctx.cc_created_in_tx = cx.txn.created_in_tx /\
   s.vs_call_ctx.cc_static = cx.txn.is_static` by
    gvs[state_rel_def, call_ctx_rel_def] >>
  Cases_on `cx.txn.is_static`
  >- (`step_inst_base (mk_inst sm.cs_next_id SELFDESTRUCT [op] []) s =
       Abort ExHalt_abort (halt_state (set_returndata [] s))` by
        simp[step_inst_base_opcode_eqs, mk_inst_def, eval_operands_def] >>
      `gas_path ctx func s 0 (Abort ExHalt_abort (halt_state (set_returndata [] s)))` by
        (irule selfdestruct_tail_path >> simp[exit_result_def] >> metis_tac[]) >>
      qexistsl_tac [`INR (Error (RuntimeError "write in static context"))`,
                   `ee`, `Abort ExHalt_abort (halt_state (set_returndata [] s))`] >>
      simp[gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def,
           exit_result_def, expr_exit_def, halt_exit_def, selfdestruct_tail_def,
           lift_option_type_def, bind_def, ignore_bind_def, return_def,
           check_not_static_def, check_def, assert_def, raise_def]) >>
  `~selfdestruct_overflows cx (w2w aw) ee.accounts` by metis_tac[] >>
  `~s.vs_call_ctx.cc_static` by simp[] >>
  drule_all step_selfdestruct_halt_rel >>
  disch_then (qspec_then `sm.cs_next_id` strip_assume_tac) >>
  `gas_path ctx func s 0 (Halt s')` by
    (irule selfdestruct_tail_path >> simp[exit_result_def] >> metis_tac[]) >>
  qexistsl_tac [`INR HaltException`, `selfdestruct_final cx (w2w aw) ee`, `Halt s'`] >>
  simp[gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def,
       exit_result_def, expr_exit_def, halt_exit_def] >>
  conj_tac
  >- (gen_tac >>
      qspecl_then [`cx`, `v`, `w2w aw`, `ee with gas_obs := tail`]
        mp_tac selfdestruct_tail_halt >> simp[]) >>
  conj_tac >- simp[selfdestruct_final_def] >>
  gen_tac >> simp[selfdestruct_final_def] >> strip_tac >>
  `halt_rel H cx ee s` by metis_tac[halt_rel_from_state_rel] >>
  drule_all step_selfdestruct_halt_rel >>
  disch_then (qspec_then `sm.cs_next_id` strip_assume_tac) >>
  gvs[] >>
  gvs[halt_rel_def, accounts_rel_def, selfdestruct_final_def]
QED

Theorem selfdestruct_vv_sim[local]:
  expr_body_pre cenv cx env e es /\ expr_type e = BaseT AddressT /\
  expr_sim ctx func cenv cx (expr_type e) e es ==>
  expr_vv_sim ctx func cenv cx ty (Call ann SelfDestructTarget [e] dflt) es
Proof
  strip_tac >> rewrite_tac[expr_vv_sim_def] >> rpt gen_tac >> strip_tac >>
  drule selfdestruct_compile >> strip_tac >>
  `cs_extends sa sm` by metis_tac[cj 2 compile_expr_grows] >>
  `cs_extends sm sb` by metis_tac[selfdestruct_extends] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (rw[gas_admissible_def] >> Cases_on `res` >- simp[expr_res_ok_def] >>
     qpat_x_assum `gas_admissible _ _ _`
       (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
     disch_then (qspecl_then [`gs`, `INR y`, `ee`] mp_tac) >>
     simp[eval_selfdestruct_action] >>
     qpat_x_assum `bind _ _ _ = _` (fn th => simp[Once bind_def, th]) >>
     simp[expr_vv_res_ok_def, expr_res_ok_def]) >>
  qpat_x_assum `expr_sim _ _ _ _ _ e _`
    (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `op`, `s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_def] >> BETA_TAC >>
  disch_then (qx_choose_then `marks` (DISJ_CASES_THEN mp_tac))
  >- (strip_tac >> qexists_tac `marks` >> disj1_tac >>
      rewrite_tac[eval_selfdestruct_action] >>
      irule gas_bad_storage_at_bind_left >> simp[] >>
      simp[storage_trace_frame_selfdestruct_tail]) >>
  disch_then (DISJ_CASES_THEN mp_tac)
  >- (rewrite_tac[gas_summary_at_def] >>
      disch_then (qx_choose_then `res` (qx_choose_then `es_end`
        (qx_choose_then `r` (CONJUNCTS_THEN2 assume_tac mp_tac)))) >>
      reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
      >- (disch_then kall_tac >> qexists_tac `marks` >> disj1_tac >>
          rewrite_tac[eval_selfdestruct_action] >>
          irule gas_bad_storage_at_bind_left >>
          simp[storage_trace_frame_selfdestruct_tail] >>
          irule gas_bad_storage_at_counted_prefix >> metis_tac[]) >>
      `valid_horizon cx st0 (storage_trace_horizon es_end.storage_trace)
         es_end.storage_trace` by fs[storage_trace_domain_def] >>
      disch_then (DISJ_CASES_THEN (strip_assume_tac o BETA_RULE))
      >- (qpat_x_assum `!H. valid_horizon _ _ H _ ==> ?v. _`
            (assume_tac o SIMP_RULE (srw_ss()) []) >>
          first_assum drule >> strip_tac >> gvs[] >>
          `?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                value_has_type tv v` by
            (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
               (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
             disch_then (CONJUNCTS_THEN2 (qspec_then `[]` assume_tac) kall_tac) >>
             `expr_body_pre cenv cx env e
                (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ [])` by simp[] >>
             drule_at (Pos hd) exprSimPrecompilesTheory.expr_body_pre_stack_result >>
             simp[is_word_type_def] >> strip_tac >> gvs[] >> metis_tac[]) >>
          `tv = BaseTV AddressT` by gvs[vyperValueTheory.evaluate_type_def] >>
          `eval_operand op t = SOME (typed_val_to_w256 tv v)` by
            (qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
               (qspec_then `storage_trace_horizon es_end.storage_trace` mp_tac) >>
             (impl_tac >- simp[]) >> disch_tac >>
             drule exprSimPrecompilesTheory.expr_post_typed_stack_operand >>
             simp[is_word_type_def]) >>
          `dest_AddressV v = SOME (w2w (typed_val_to_w256 tv v))` by
            metis_tac[address_typed_dest] >>
          `~t.vs_halted` by
            metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
          Cases_on `~cx.txn.is_static /\
            selfdestruct_overflows cx (w2w (typed_val_to_w256 tv v)) es_end.accounts`
          >- (qexists_tac `marks` >> disj2_tac >> disj2_tac >>
              qexistsl_tac [`RuntimeError "transfer_value recipient overflow"`,
                           `es_end`, `func`, `t`] >>
              irule gas_exempt_cert_origin >>
              rewrite_tac[gas_exempt_origin_def] >> disj2_tac >>
              qexistsl_tac [`storage_trace_horizon es_end.storage_trace`,
                `cenv`, `cx`, `ty`, `ann`, `e`, `dflt`, `sa`, `sb`, `sm`,
                `StackValue ann (Lit 0w)`, `op`, `v`,
                `w2w (typed_val_to_w256 tv v)`] >>
              simp[gas_value_prefix_def] >>
              `valid_horizon cx st0 (storage_trace_horizon es_end.storage_trace)
                 es.storage_trace` by
                (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
                   (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
                 disch_then (CONJUNCTS_THEN2 (qspec_then `[]` assume_tac) kall_tac) >>
                 drule_at (Pos (el 2)) valid_horizon_frame >>
                 simp[] >> disch_then irule >> simp[] >>
                 irule storage_trace_frame_bind_all >>
                 simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
              metis_tac[]) >>
          `!H. valid_horizon cx st0 H (es_end with gas_obs := []).storage_trace ==>
               state_rel H func cenv cx (es_end with gas_obs := []) t` by
            (simp[] >> metis_tac[expr_post_def, stmt_state_rel_def]) >>
          `valid_horizon cx st0 (storage_trace_horizon es_end.storage_trace)
             (es_end with gas_obs := []).storage_trace` by simp[] >>
          `~cx.txn.is_static ==> ~selfdestruct_overflows cx
             (w2w (typed_val_to_w256 tv v)) (es_end with gas_obs := []).accounts` by
            (simp[] >> metis_tac[]) >>
          drule_all selfdestruct_tail_sim >>
          disch_then (qspec_then `ctx` strip_assume_tac) >>
          qexists_tac `marks` >> disj2_tac >> disj1_tac >>
          qexistsl_tac [`res`, `fin`, `r`] >>
          reverse conj_tac
          >- (disj2_tac >> simp[] >> metis_tac[]) >>
          rewrite_tac[eval_selfdestruct_action] >>
          irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
                 |> REWRITE_RULE [APPEND_NIL]) >>
          qexistsl_tac [`es_end`, `t`, `v`] >> simp[]) >>
      qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
        (assume_tac o SIMP_RULE (srw_ss()) []) >>
      `expr_exit res r` by metis_tac[] >>
      Cases_on `res` >> gvs[expr_exit_def] >>
      qexists_tac `marks` >> disj2_tac >> disj1_tac >>
      simp[gas_summary_at_def] >>
      qexistsl_tac [`INR y`, `es_end`, `r`] >> simp[] >>
      conj_tac
      >- (rewrite_tac[eval_selfdestruct_action] >>
          irule gas_marked_exec_bind_exception >> simp[]) >>
      qpat_x_assum `expr_exit _ _` mp_tac >>
      Cases_on `r` >> Cases_on `y` >> gvs[expr_exit_def, halt_exit_def] >>
      rename1 `Error err` >> Cases_on `err` >> gvs[expr_exit_def, halt_exit_def]) >>
  strip_tac >> qexists_tac `marks` >> disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  rewrite_tac[eval_selfdestruct_action,
              exprSimRawRevertCoreTheory.ignore_bind_bind_unit] >>
  irule gas_exempt_cert_error_value >> simp[]
QED

Theorem compile_selfdestruct_case:
  !nocalls ctx func cenv cx ann args dflt.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_sim_case nocalls ctx func cenv cx (Call ann SelfDestructTarget args dflt) /\
    expr_vv_case nocalls ctx func cenv cx (Call ann SelfDestructTarget args dflt)
Proof
  rpt gen_tac >> strip_tac >>
  `expr_vv_case nocalls ctx func cenv cx (Call ann SelfDestructTarget args dflt)`
    suffices_by simp[expr_sim_case_of_vv] >>
  rewrite_tac[expr_vv_case_def] >> rpt strip_tac >>
  drule selfdestruct_pre_arg >> strip_tac >> gvs[] >>
  irule selfdestruct_vv_sim >> simp[] >> conj_tac
  >- (qexists_tac `env` >> simp[]) >>
  gvs[exprs_case_def, expr_sim_case_def,
      vyperTypeCallGraphTheory.int_calls_expr_def] >> metis_tac[]
QED

Theorem compile_selfdestruct_sim:
  !cenv ann args dflt.
    expr_sim_below cenv (expr_size (Call ann (SelfDestructTarget) args dflt)) ==>
    expr_vv_ok cenv (Call ann (SelfDestructTarget) args dflt)
Proof
  rpt strip_tac >> simp[expr_vv_ok_case] >> rpt gen_tac >>
  `exprs_case T ctx func cenv cx args` by
    (irule exprs_case_below >> irule expr_sim_below_mono >>
     goal_assum (drule_at Any) >> simp[expr_size_def]) >>
  metis_tac[compile_selfdestruct_case]
QED

Theorem compile_create_sim:
  !cenv ann kind has_salt rof order args dflt.
    expr_sim_below cenv (expr_size (Call ann (CreateTarget kind has_salt rof order) args dflt)) ==>
    expr_vv_ok cenv (Call ann (CreateTarget kind has_salt rof order) args dflt)
Proof
  rw[exprSimHypsDefsTheory.expr_vv_ok_def,
     exprSimHypsDefsTheory.expr_sim_pre_def,
     supportedExprTraverseTheory.expr_has_evm_run_thm,
     supportedExprTraverseTheory.expr_evm_run_root_def]
QED
