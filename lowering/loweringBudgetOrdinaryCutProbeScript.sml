Theory loweringBudgetOrdinaryCutProbe
Ancestors
  sourceCallCount sourceCallCountEntryReplay extCallOracleStep
  loweringBudgetCallOracleTransport loweringBudgetCreateOracleTransport
  builtinSystem builtinCreate venomExecSemantics venomCallOracleDefs
  accountsRelProps vyperCallOutcome vyperState list pair
  venomState venomInst extCallOracle emitHelper vyperInterpreter vyperValue
  exprSimSend exprSimWordArgs exprLowering compileEnv valueEncoding
  loweringRuntimeNoCreate vyperAST words loweringStateRelDefs
  loweringCallBudgetHistory loweringBudgetAbortFrontier instIdxIndep
  venomInstProofs venomInstProofs1 frameGasEvents fragExec contextCodegenRel rich_list
  entrySinkExtraction exprLoweringProps
Libs wordsLib

(* The CALL emitted by send has no private return buffer.  An exhausted
   outcome and the counter's ordinary failed marker execute identically. *)
Theorem probe_send_empty_marker:
  !s aw vw gas out rest t.
    s.vs_outcomes = [] /\
    exec_ext_call (mk_inst 0 CALL [] [out])
      s gas aw vw 0w 0w 0w 0w F = OK t ==>
    exec_ext_call (mk_inst 0 CALL [] [out])
      (s with vs_outcomes := empty_failed_outcome::rest)
      gas aw vw 0w 0w 0w 0w F = OK (t with vs_outcomes := rest)
Proof
  rpt strip_tac >> Cases_on `vw = 0w` >>
  Cases_on `precompile_result (w2w aw) []` >>
  gvs[exec_ext_call_def, mk_inst_def, consume_call_outcome_eq,
      take_outcome_def, failed_outcome_def, adopt_outcome_def,
      adopt_outcome_deletions_def, write_memory_with_expansion_def,
      empty_failed_outcome_def, update_var_def,
      venom_call_request_def, read_memory_def, computed_precompile_def,
      venom_state_component_equality] >>
  Cases_on `x` >> simp[]
QED

Theorem probe_send_source_exhausted:
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

(* A real well-typed send with literal operands: no operand code precedes
   the CALL/ASSERT cut, and no oracle fact is assumed for its requests. *)
Theorem probe_literal_send_code:
  !ce sa vv sb.
    compile_expr ce NoneT
      (Call NoneT (Send F)
        [Literal (BaseT AddressT) (BytesL (REPLICATE 19 0w ++ [42w]));
         Literal (BaseT (UintT 256)) (IntL 0)] NONE) sa = (vv,sb) ==>
    ?out.
      sb.cs_current_insts = sa.cs_current_insts ++
        [mk_inst sa.cs_next_id CALL
          [Lit 0w; Lit 42w; Lit 0w; Lit 0w; Lit 0w; Lit 0w; Lit 0w] [out];
         mk_inst (sa.cs_next_id + 1) ASSERT [Var out] []]
Proof
  rpt strip_tac >>
  qpat_assum `compile_expr _ _ _ _ = _`
    (mp_then Any mp_tac compile_expr_send) >>
  simp[expr_type_def] >> strip_tac >>
  qpat_x_assum `compile_expr _ _ _ _ = _` kall_tac >>
  gvs[lower_word_args_cons, lower_word_args_nil, lower_value_def,
      expr_type_def, compile_literal_vv_def, comp_bind_def, comp_return_def] >>
  gvs[CONJUNCT1 compile_expr_raw_def, compile_expr_body_def,
      expr_type_def, compile_literal_vv_def, comp_return_def,
      unwrap_value_def] >>
  `typed_val_to_w256 (BaseTV AddressT)
      (BytesV (REPLICATE 19 0w ++ [42w])) = 42w /\
    (i2w (0:int):bytes32) = 0w` by EVAL_TAC >>
  gvs[] >> drule_all send_tail_shape >> metis_tac[]
QED

Theorem probe_literal_send_exhausted_cut:
  !H fn ce cx es s out rest.
    state_rel H fn ce cx es s /\ es.outcomes = SOME [] /\
    ~cx.txn.is_static ==>
    request_agree H cx (call_outcome_request 42w [] (SOME 0) es)
      (venom_call_request s 42w 0w 0w 0w F) /\
    ?t.
      step_inst_base (mk_inst 0 CALL
        [Lit 0w; Lit 42w; Lit 0w; Lit 0w; Lit 0w; Lit 0w; Lit 0w] [out]) s = OK t /\
      step_inst_base (mk_inst 0 CALL
        [Lit 0w; Lit 42w; Lit 0w; Lit 0w; Lit 0w; Lit 0w; Lit 0w] [out])
        (s with vs_outcomes := empty_failed_outcome::rest) =
        OK (t with vs_outcomes := rest) /\
      t.vs_outcomes = [] /\ t.vs_gas_readings = s.vs_gas_readings /\
      step_inst_base (mk_inst 1 ASSERT [Var out] []) t =
        Abort Revert_abort (revert_state (set_returndata [] t))
Proof
  rpt gen_tac >> strip_tac >>
  `s.vs_outcomes = [] /\ ~s.vs_call_ctx.cc_static /\ accounts_rel H cx es s` by
    gvs[state_rel_def, call_ctx_rel_def] >>
  conj_tac
  >- (irule (venom_call_request_source |> SPEC_ALL |>
      Q.INST [`ao` |-> `0w`, `az` |-> `0w`] |> SRULE [read_memory_def]) >> simp[]) >>
  `precompile_result 42w [] = NONE /\ (w2w (42w:bytes32):address) = 42w` by EVAL_TAC >>
  qexists_tac `update_var out 0w (s with
    <|vs_outcomes := []; vs_requests := record_request
       (venom_call_request s 42w 0w 0w 0w F) s.vs_requests;
      vs_returndata := []|>)` >>
  simp[step_inst_base_opcode_eqs, eval_operand_def, exec_ext_call_def,
       consume_call_outcome_eq, take_outcome_def, failed_outcome_def,
       adopt_outcome_def, adopt_outcome_deletions_def, computed_precompile_def,
       venom_call_request_def, empty_failed_outcome_def,
       write_memory_with_expansion_def, read_memory_def,
       update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
       mk_inst_def, venom_state_component_equality]
QED

Theorem probe_send_evaluated_cut:
  !H fn ce cx es s out rest to_v amount_v.
    state_rel H fn ce cx es s /\ es.outcomes = SOME [] /\
    ~cx.txn.is_static /\ dest_AddressV to_v = SOME 42w /\
    dest_NumV amount_v = SOME 0 ==>
    eval_send cx F [to_v;amount_v] es =
      (INR (Error (RuntimeError "send failed")),
       es with <| outcomes := SOME [];
         requests := record_request
           (call_outcome_request 42w [] (SOME 0) es) es.requests;
         storage_trace := es.storage_trace ++
           [StorageOutcome (call_outcome_request 42w [] (SOME 0) es)
             (failed_outcome (call_outcome_request 42w [] (SOME 0) es))] |>) /\
    request_agree H cx (call_outcome_request 42w [] (SOME 0) es)
      (venom_call_request s 42w 0w 0w 0w F) /\
    ?t.
      step_inst_base (mk_inst 0 CALL
        [Lit 0w; Lit 42w; Lit 0w; Lit 0w; Lit 0w; Lit 0w; Lit 0w] [out]) s = OK t /\
      step_inst_base (mk_inst 0 CALL
        [Lit 0w; Lit 42w; Lit 0w; Lit 0w; Lit 0w; Lit 0w; Lit 0w] [out])
        (s with vs_outcomes := empty_failed_outcome::rest) =
        OK (t with vs_outcomes := rest) /\
      t.vs_outcomes = [] /\ t.vs_gas_readings = s.vs_gas_readings /\
      step_inst_base (mk_inst 1 ASSERT [Var out] []) t =
        Abort Revert_abort (revert_state (set_returndata [] t))
Proof
  rpt gen_tac >> strip_tac >> reverse conj_tac
  >- (irule probe_literal_send_exhausted_cut >> metis_tac[]) >>
  simp[eval_send_def, frame_call_value_def, ext_call_kwarg_def,
       vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       type_check_def, check_def, assert_def, lift_option_type_def,
       vyperStateTheory.return_def, vyperStateTheory.raise_def,
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

Theorem probe_send_budget_prefix:
  !cfg p h marks q fn s id out ci ai.
    ci = mk_inst id CALL
      [Lit 0w; Lit 42w; Lit 0w; Lit 0w; Lit 0w; Lit 0w; Lit 0w] [out] /\
    ai = mk_inst (id+1) ASSERT [Var out] [] /\
    p.bp_fn = fn /\ p.bp_state = s /\
    s.vs_outcomes = [] /\ ~s.vs_call_ctx.cc_static /\
    (!st i. st.vs_current_bb = s.vs_current_bb /\
      st.vs_inst_idx < s.vs_inst_idx + 2 /\
      s.vs_inst_idx <= st.vs_inst_idx /\ active_inst fn i st ==>
      i = EL (st.vs_inst_idx - s.vs_inst_idx) [ci;ai]) /\
    lower_budget_path F cfg p h marks q ==>
    q.bp_fn = fn /\ q.bp_stack = p.bp_stack /\ marks = [] /\
    q.bp_state.vs_current_bb = s.vs_current_bb /\
    ?n. n < 2 /\ q.bp_state.vs_inst_idx = s.vs_inst_idx + n /\
      lower_history_count h <= n /\
      active_inst fn (EL n [ci;ai]) q.bp_state /\
      (!i. active_inst fn i q.bp_state ==> i = EL n [ci;ai]) /\
      (n = 1 ==> eval_operand (Var out) q.bp_state = SOME 0w)
Proof
  rpt gen_tac >> strip_tac >>
  `?u. run_inst_seq [ci;ai] s = Abort Revert_abort u` by (
    `precompile_result 42w [] = NONE /\ (w2w (42w:bytes32):address) = 42w` by EVAL_TAC >>
    simp[run_inst_seq_def, step_inst_base_opcode_eqs, eval_operand_def,
      exec_ext_call_def, consume_call_outcome_eq, take_outcome_def,
      failed_outcome_def, adopt_outcome_def, adopt_outcome_deletions_def,
      computed_precompile_def, venom_call_request_def,
      write_memory_with_expansion_def, read_memory_def,
      update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
      mk_inst_def]) >>
  drule two_instruction_send_abort_prefix >>
  disch_then (qspecl_then [`fn`,`s`,`ci`,`ai`,`Var out`] mp_tac) >>
  (impl_tac >- gvs[mk_inst_def]) >> strip_tac >>
  `?i. active_inst q.bp_fn i q.bp_state` by
    metis_tac[lower_budget_path_cases] >>
  gvs[] >>
  qpat_x_assum `!st i. _` (qspec_then `q.bp_state` assume_tac) >>
  gvs[] >> metis_tac[]
QED

Theorem probe_send_budget_terminal:
  !D lo explicit ctx p h marks q fn s id out ci ai h' marks' q'.
    ci = mk_inst id CALL
      [Lit 0w; Lit 42w; Lit 0w; Lit 0w; Lit 0w; Lit 0w; Lit 0w] [out] /\
    ai = mk_inst (id+1) ASSERT [Var out] [] /\
    p.bp_fn = fn /\ p.bp_state = s /\
    s.vs_outcomes = [] /\ ~s.vs_call_ctx.cc_static /\
    (!st i. st.vs_current_bb = s.vs_current_bb /\
      st.vs_inst_idx < s.vs_inst_idx + 2 /\
      s.vs_inst_idx <= st.vs_inst_idx /\ active_inst fn i st ==>
      i = EL (st.vs_inst_idx - s.vs_inst_idx) [ci;ai]) /\
    lower_budget_path F (D,lo,explicit,ctx) p h marks q /\
    q.bp_state.vs_inst_idx = s.vs_inst_idx + 1 /\
    lower_budget_path F (D,lo,explicit,ctx) q h' marks' q' ==>
    h' = [] /\ marks' = [] /\ q' = q
Proof
  rpt gen_tac >> strip_tac >>
  drule_all probe_send_budget_prefix >> strip_tac >>
  `n = 1` by decide_tac >> gvs[] >>
  irule lower_budget_path_assert_zero >>
  conj_tac >- (qexistsl_tac [`mk_inst (id+1) ASSERT [Var out] []`,`Var out`] >>
    gvs[mk_inst_def]) >>
  metis_tac[]
QED
