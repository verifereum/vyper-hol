Theory loweringBudgetPrecompilePrefix
Ancestors
  loweringBudgetAbortFrontier loweringCallBudgetHistory exprSimPrecompiles fragExec
  instIdxIndep exprLoweringProps entrySinkExtraction venomInstProofs1 venomInstProofs venomExecSemantics venomInst contextCodegenRel list rich_list

Theorem three_instruction_abort_prefix[local]:
  !checked cfg p h marks q.
    lower_budget_path checked cfg p h marks q ==>
    !fn s gi ci ai op.
      p.bp_fn = fn /\ p.bp_state = s /\
      gi.inst_opcode = GAS /\ ci.inst_opcode = STATICCALL /\
      ai.inst_opcode = ASSERT /\ ai.inst_operands = [op] /\
      (?u. run_inst_seq [gi;ci;ai] s = Abort Revert_abort u) /\
      (!st i. st.vs_current_bb = s.vs_current_bb /\
        st.vs_inst_idx < s.vs_inst_idx + 3 /\
        s.vs_inst_idx <= st.vs_inst_idx /\ active_inst fn i st ==>
        i = EL (st.vs_inst_idx - s.vs_inst_idx) [gi;ci;ai]) ==>
      q.bp_fn = fn /\ q.bp_stack = p.bp_stack /\
      q.bp_state.vs_current_bb = s.vs_current_bb /\
      ?n. n < 3 /\ q.bp_state.vs_inst_idx = s.vs_inst_idx + n /\
        lower_history_count h <= (if n = 2 then 1 else 0) /\
        (?u. run_inst_seq (DROP n [gi;ci;ai]) q.bp_state = Abort Revert_abort u) /\
        (n = 2 ==> eval_operand op q.bp_state = SOME 0w)
Proof
  ho_match_mp_tac lower_budget_path_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac
  >- (gvs[lower_history_count_def] >> qexists_tac `0` >> simp[])
  >> first_x_assum (qspecl_then [`fn`,`s`,`gi`,`ci`,`ai`,`op`] mp_tac)
  >> (impl_tac >- metis_tac[]) >> strip_tac >> gvs[]
  >> qpat_x_assum `!st i. _` (qspec_then `q.bp_state` assume_tac)
  >> gvs[]
  >> `n = 0 \/ n = 1 \/ n = 2` by decide_tac
  >> gvs[is_terminator_def]
  >> imp_res_tac step_preserves_control_flow
  >> gvs[Once step_inst_def]
  >> imp_res_tac step_inst_base_nonterminator_no_exit
  >> gvs[is_terminator_def]
  >> qpat_x_assum `run_inst_seq _ p.bp_state = _` kall_tac
  >> gvs[Once run_inst_seq_def]
  >> gvs[cj 1 run_inst_seq_def]
  >- (qexists_tac `1` >> simp[lower_history_count_def, FILTER_APPEND,
        lower_event_consumes_def, run_inst_seq_inst_idx, is_terminator_def,
        exec_result_map_def] >> gvs[lower_history_count_def])
  >> qexists_tac `2` >> simp[lower_history_count_def, FILTER_APPEND,
       lower_event_consumes_def, run_inst_seq_inst_idx, is_terminator_def,
       exec_result_map_def]
  >> gvs[lower_history_count_def, run_inst_seq_def, step_inst_base_opcode_eqs, AllCaseEqs()]
QED

Theorem budget_path_endpoint_active[local]:
  !checked cfg p h marks q.
    lower_budget_path checked cfg p h marks q ==>
    ?i. active_inst q.bp_fn i q.bp_state
Proof
  ho_match_mp_tac lower_budget_path_ind >> rpt strip_tac >> metis_tac[]
QED

Theorem computed_failure_budget_prefix:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL [gas; Lit target; ip; Lit insz; op; Lit outsz];
      emit_void ASSERT [success]; return op od) sm = (res,sb) /\
  eval_operand ip s = SOME wi /\ eval_operand op s = SOME wo /\
  (!x. ip = Var x ==> not_fresh_at sm x) /\
  (!x. op = Var x ==> not_fresh_at sm x) /\
  precompile_result (venom_call_request s target 0w wi insz T).cr_target
    (venom_call_request s target 0w wi insz T).cr_data = SOME NONE /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  (!st i. st.vs_current_bb = s.vs_current_bb /\
    st.vs_inst_idx < s.vs_inst_idx + 3 /\
    s.vs_inst_idx <= st.vs_inst_idx /\ active_inst fn i st ==>
    i = EL (st.vs_inst_idx - s.vs_inst_idx) (emitted_insts sm sb)) /\
  p.bp_state = s /\ p.bp_fn = fn /\
  lower_budget_path F (D,lo,explicit,ctx) p h marks q ==>
  lower_history_count h <= 1 /\ q.bp_fn = fn /\
  q.bp_stack = p.bp_stack /\ q.bp_state.vs_current_bb = s.vs_current_bb /\
  ?n. n < 3 /\ q.bp_state.vs_inst_idx = s.vs_inst_idx + n /\
    active_inst fn (EL n (emitted_insts sm sb)) q.bp_state /\
    (!i. active_inst fn i q.bp_state ==> i = EL n (emitted_insts sm sb)) /\
    (n = 2 ==>
      (EL n (emitted_insts sm sb)).inst_opcode = ASSERT /\
      eval_operand (Var (STRING #"%" (toString (sm.cs_next_var+1))))
        q.bp_state = SOME 0w)
Proof
  strip_tac >> drule_all computed_suffix_failure >> strip_tac >>
  drule computed_suffix_shape >> strip_tac >>
  drule three_instruction_abort_prefix >>
  disch_then (qspecl_then [`fn`,`s`,
    `EL 0 (emitted_insts sm sb)`,`EL 1 (emitted_insts sm sb)`,
    `EL 2 (emitted_insts sm sb)`,
    `Var (STRING #"%" (toString (sm.cs_next_var+1)))`] mp_tac) >>
  (impl_tac >- gvs[mk_inst_def]) >> strip_tac >>
  `?i. active_inst q.bp_fn i q.bp_state` by
    metis_tac[budget_path_endpoint_active] >>
  gvs[] >> `lower_history_count h <= 1` by (Cases_on `n = 2` >> gvs[]) >>
  simp[] >>
  qpat_x_assum `!st i. _` (qspec_then `q.bp_state` assume_tac) >>
  gvs[] >> metis_tac[]
QED

Theorem computed_failure_budget_terminal:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL [gas; Lit target; ip; Lit insz; op; Lit outsz];
      emit_void ASSERT [success]; return op od) sm = (res,sb) /\
  eval_operand ip s = SOME wi /\ eval_operand op s = SOME wo /\
  (!x. ip = Var x ==> not_fresh_at sm x) /\
  (!x. op = Var x ==> not_fresh_at sm x) /\
  precompile_result (venom_call_request s target 0w wi insz T).cr_target
    (venom_call_request s target 0w wi insz T).cr_data = SOME NONE /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  (!st i. st.vs_current_bb = s.vs_current_bb /\
    st.vs_inst_idx < s.vs_inst_idx + 3 /\
    s.vs_inst_idx <= st.vs_inst_idx /\ active_inst fn i st ==>
    i = EL (st.vs_inst_idx - s.vs_inst_idx) (emitted_insts sm sb)) /\
  p.bp_state = s /\ p.bp_fn = fn /\
  lower_budget_path F (D,lo,explicit,ctx) p h marks q /\
  q.bp_state.vs_inst_idx = s.vs_inst_idx + 2 /\
  lower_budget_path F (D,lo,explicit,ctx) q h' marks' q' ==>
  h' = [] /\ marks' = [] /\ q' = q
Proof
  strip_tac >> drule_all computed_failure_budget_prefix >> strip_tac >>
  `n = 2` by decide_tac >> gvs[] >>
  drule computed_suffix_shape >> strip_tac >>
  irule lower_budget_path_assert_zero >>
  conj_tac >- (
    qexistsl_tac [`EL 2 (emitted_insts sm sb)`,
      `Var (STRING #"%" (toString (sm.cs_next_var+1)))`] >>
    gvs[mk_inst_def]) >>
  metis_tac[]
QED
