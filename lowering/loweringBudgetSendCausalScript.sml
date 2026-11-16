Theory loweringBudgetSendCausal
Ancestors
  loweringBudgetCallOracleTransport loweringBudgetCursorCuts
  sourceCallCount extCallOracleStep builtinSystem venomExecSemantics
  venomCallOracleDefs accountsRelProps vyperCallOutcome vyperState list pair
  venomState venomInst extCallOracle emitHelper vyperInterpreter vyperValue
  exprSimSend exprLowering compileEnv valueEncoding words loweringStateRelDefs
  loweringCallBudgetHistory loweringBudgetAbortFrontier instIdxIndep
  venomInstProofs venomInstProofs1 frameGasEvents fragExec contextCodegenRel rich_list
  entrySinkExtraction exprLoweringProps
Libs wordsLib

Theorem send_source_exhausted[local]:
  !cx es (aw:bytes32) (vw:bytes32).
    ~cx.txn.is_static /\ es.outcomes = SOME [] ==>
    eval_send cx F [AddressV (w2w aw); IntV (&w2n vw)] es =
      (INR (Error (RuntimeError "send failed")),
       es with <| outcomes := SOME [];
         requests := record_request
           (call_outcome_request (w2w aw) [] (SOME (w2n vw)) es) es.requests;
         storage_trace := es.storage_trace ++
           [StorageOutcome
             (call_outcome_request (w2w aw) [] (SOME (w2n vw)) es)
             (failed_outcome
               (call_outcome_request (w2w aw) [] (SOME (w2n vw)) es))] |>)
Proof
  rpt strip_tac >>
  simp[eval_send_def, frame_call_value_def, ext_call_kwarg_def,
       vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       type_check_def, check_def, assert_def, lift_option_type_def,
       vyperStateTheory.return_def, vyperStateTheory.raise_def,
       dest_AddressV_def, dest_NumV_def, fcpLib.INDEX_CONV ``dimindex(:160)``,
       byteTheory.word_of_bytes_be_def, byteTheory.word_of_bytes_word_to_bytes,
       dividesTheory.compute_divides,
       take_call_outcome_def, take_request_outcome_def,
       take_outcome_def, failed_outcome_def]
QED

Theorem two_instruction_send_abort_prefix[local]:
  !checked cfg p h marks q.
    lower_budget_path checked cfg p h marks q ==>
    !fn s ci ai op.
      p.bp_fn = fn /\ p.bp_state = s /\
      ci.inst_opcode = CALL /\ ai.inst_opcode = ASSERT /\
      ai.inst_operands = [op] /\
      (?u. run_inst_seq [ci;ai] s = Abort Revert_abort u) /\
      (!st i. st.vs_current_bb = s.vs_current_bb /\
        st.vs_inst_idx < s.vs_inst_idx + 2 /\
        s.vs_inst_idx <= st.vs_inst_idx /\ active_inst fn i st ==>
        i = EL (st.vs_inst_idx - s.vs_inst_idx) [ci;ai]) ==>
      q.bp_fn = fn /\ q.bp_stack = p.bp_stack /\ marks = [] /\
      q.bp_state.vs_current_bb = s.vs_current_bb /\
      ?n. n < 2 /\ q.bp_state.vs_inst_idx = s.vs_inst_idx + n /\
        lower_history_count h <= n /\
        (?u. run_inst_seq (DROP n [ci;ai]) q.bp_state = Abort Revert_abort u) /\
        (n = 1 ==> eval_operand op q.bp_state = SOME 0w)
Proof
  ho_match_mp_tac lower_budget_path_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac
  >- (gvs[lower_history_count_def] >> qexists_tac `0` >> simp[])
  >> first_x_assum (qspecl_then [`fn`,`s`,`ci`,`ai`,`op`] mp_tac)
  >> (impl_tac >- metis_tac[]) >> strip_tac >> gvs[]
  >> qpat_x_assum `!st i. _` (qspec_then `q.bp_state` assume_tac)
  >> gvs[]
  >> `n = 0 \/ n = 1` by decide_tac
  >> gvs[is_terminator_def]
  >> imp_res_tac step_preserves_control_flow
  >> gvs[Once step_inst_def]
  >> imp_res_tac step_inst_base_nonterminator_no_exit
  >> gvs[is_terminator_def]
  >> qpat_x_assum `run_inst_seq _ p.bp_state = _` kall_tac
  >> gvs[Once run_inst_seq_def]
  >> gvs[cj 1 run_inst_seq_def]
  >> simp[gas_events_step_plain]
  >> qexists_tac `1`
  >> simp[lower_history_count_def, FILTER_APPEND,
       lower_event_consumes_def, run_inst_seq_inst_idx, is_terminator_def,
       exec_result_map_def, gas_events_step_plain]
  >> gvs[lower_history_count_def, run_inst_seq_def, step_inst_base_opcode_eqs, AllCaseEqs()]
QED

Theorem embedded_send_exhausted_cut:
  !H fn ce cx es s sf sm s3 sb ao vo aw vw out D lo explicit ctx p h marks q.
    state_rel H fn ce cx es s /\ es.outcomes = SOME [] /\ ~cx.txn.is_static /\
    precompile_result (w2w aw) [] = NONE /\
    emit_op CALL [Lit 0w;ao;vo;Lit 0w;Lit 0w;Lit 0w;Lit 0w] sm = (Var out,s3) /\
    emit_void ASSERT [Var out] s3 = ((),sb) /\
    fn_has_code sf sb fn /\ ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
    s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
    eval_operand ao s = SOME aw /\ eval_operand vo s = SOME vw /\ ~s.vs_halted /\
    p.bp_fn = fn /\ p.bp_state = s /\
    lower_budget_path F (D,lo,explicit,ctx) p h marks q ==>
    eval_send cx F [AddressV (w2w aw);IntV (&w2n vw)] es =
      (INR (Error (RuntimeError "send failed")),
       es with <|outcomes := SOME [];
         requests := record_request (call_outcome_request (w2w aw) [] (SOME (w2n vw)) es) es.requests;
         storage_trace := es.storage_trace ++
           [StorageOutcome (call_outcome_request (w2w aw) [] (SOME (w2n vw)) es)
             (failed_outcome (call_outcome_request (w2w aw) [] (SOME (w2n vw)) es))]|>) /\
    request_agree H cx (call_outcome_request (w2w aw) [] (SOME (w2n vw)) es)
      (venom_call_request s aw vw 0w 0w F) /\
    q.bp_fn = fn /\ q.bp_stack = p.bp_stack /\ marks = [] /\
    q.bp_state.vs_current_bb = s.vs_current_bb /\
    (?n. n < 2 /\ q.bp_state.vs_inst_idx = s.vs_inst_idx + n /\ lower_history_count h <= n) /\
    (q.bp_state.vs_inst_idx = s.vs_inst_idx + 1 ==>
      !h' marks' q'. lower_budget_path F (D,lo,explicit,ctx) q h' marks' q' ==>
        h' = [] /\ marks' = [] /\ q' = q)
Proof
  rpt gen_tac >> strip_tac >>
  conj_tac >- (irule send_source_exhausted >> simp[]) >>
  `s.vs_outcomes = [] /\ ~s.vs_call_ctx.cc_static /\ accounts_rel H cx es s` by
    gvs[state_rel_def, call_ctx_rel_def] >>
  conj_tac
  >- (irule (venom_call_request_source |> SPEC_ALL |>
      Q.INST [`ao` |-> `0w`, `az` |-> `0w`] |> SRULE [read_memory_def]) >> simp[]) >>
  drule_all send_tail_shape >> strip_tac >>
  `out = out'` by gvs[] >> qpat_x_assum `Var out = Var out'` kall_tac >>
  qpat_x_assum `out = out'` (SUBST_ALL_TAC o SYM) >>
  qabbrev_tac `ci = mk_inst sm.cs_next_id CALL
    [Lit 0w;ao;vo;Lit 0w;Lit 0w;Lit 0w;Lit 0w] [out]` >>
  qabbrev_tac `ai = mk_inst (sm.cs_next_id+1) ASSERT [Var out] []` >>
  `!st i. st.vs_current_bb = s.vs_current_bb /\
    st.vs_inst_idx < s.vs_inst_idx + 2 /\ s.vs_inst_idx <= st.vs_inst_idx /\
    active_inst fn i st ==> i = EL (st.vs_inst_idx - s.vs_inst_idx) [ci;ai]` by
    (rpt strip_tac >>
     drule embedded_current_active_inst >>
     disch_then (qspecl_then [`st`,`i`] mp_tac) >>
     gvs[EL_APPEND, Abbr `ci`, Abbr `ai`]) >>
  `?u. run_inst_seq [ci;ai] s = Abort Revert_abort u` by
    (simp[Abbr `ci`, Abbr `ai`, run_inst_seq_def, step_inst_base_opcode_eqs,
      eval_operand_def, exec_ext_call_def, consume_call_outcome_eq,
      take_outcome_def, failed_outcome_def, adopt_outcome_def,
      adopt_outcome_deletions_def, computed_precompile_def,
      venom_call_request_def, write_memory_with_expansion_def, read_memory_def,
      update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE, mk_inst_def]) >>
  drule two_instruction_send_abort_prefix >>
  disch_then (qspecl_then [`fn`,`s`,`ci`,`ai`,`Var out`] mp_tac) >>
  (impl_tac >- gvs[Abbr `ci`, Abbr `ai`, mk_inst_def]) >> strip_tac >>
  rpt conj_tac >- simp[] >- simp[] >- simp[] >- simp[]
  >- metis_tac[] >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  `n = 1` by decide_tac >> gvs[] >>
  irule lower_budget_path_assert_zero >>
  conj_tac >- (qexistsl_tac [`ai`,`Var out`] >> simp[Abbr `ai`, mk_inst_def]) >>
  `?i. active_inst q.bp_fn i q.bp_state` by metis_tac[lower_budget_path_cases] >>
  metis_tac[]
QED
