Theory entryValueRejectFacts
Ancestors
  vyperLoweringCorrect e2eBoundaryTest entryDispatchProps supportedProgram
  supportedNames supportedDecls vyperTypeContractSoundness
  vyperInterpreter vyperState compileEnv words e2eDefs list

Theorem send_call_value_rejects_only_nonpayable:
  value_transfer_ok tx am.accounts /\
  send_call_value mut
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am [env] with
      <| outcomes := SOME outs; requests := [] |>) = (INR e, st) ==>
  mut <> Payable /\ tx.value <> 0
Proof
  strip_tac >>
  qabbrev_tac `s = initial_state am [env] with
    <| outcomes := SOME outs; requests := [] |>` >>
  `value_transfer_ok tx s.accounts` by simp[Abbr `s`, initial_state_def] >>
  drule entry_transfer_source_effect >> strip_tac >>
  gvs[send_call_value_def, initial_evaluation_context_def] >>
  Cases_on `tx.value = 0` >- gvs[return_def] >>
  Cases_on `mut = Payable` >>
  gvs[ignore_bind_def, check_def, assert_def, return_def, bind_def]
QED

Theorem entry_value_reject_callvalue:
  source_typing_ok tops am tx /\ initial_venom_state_rel tops am tx vs /\
  send_call_value mut
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am [env] with
      <| outcomes := SOME vs.vs_outcomes; requests := [] |>) = (INR e, st) ==>
  mut <> Payable /\ vs.vs_call_ctx.cc_callvalue <> 0w
Proof
  strip_tac >>
  `value_transfer_ok tx am.accounts` by
    gvs[initial_venom_state_rel_def] >>
  drule_all send_call_value_rejects_only_nonpayable >> strip_tac >>
  gvs[source_typing_ok_def, initial_venom_state_rel_def, venom_env_rel_def,
      call_ctx_rel_def, call_tx_well_typed_def, dimword_def]
QED

Theorem valid_call_linear_dispatch_target:
  supported_program tops /\ valid_vyper_call tops tx cd ret ==>
  linear_dispatch_target cd
    (MAP (\(sel, lbl, _). (sel, lbl))
      (build_selectors (type_env tops) (FST (classify_functions tops)))) fb =
    "fn_" ++ tx.function_name
Proof
  strip_tac >>
  `EVERY (supported_declaration_header tops) tops` by
    gvs[supported_program_def, supported_declaration_headers_def] >>
  `!nr mut ty slot. ~MEM (VariableDecl (Public nr) mut tx.function_name ty slot) tops` by
    (fs[EVERY_MEM] >> metis_tac[supported_public_variables_rejected]) >>
  `!nr tr kt vt slot. ~MEM (HashMapDecl (Public nr) tr tx.function_name kt vt slot) tops` by
    (rpt strip_tac >> fs[EVERY_MEM] >>
     first_x_assum drule >> simp[supported_hashmap_header_contract]) >>
  gvs[valid_vyper_call_def] >>
  `ALL_DISTINCT (MAP FST (build_selectors (type_env tops)
     (FST (classify_functions tops))))` by
    gvs[supported_program_def, supported_declaration_names_def,
        supported_selectors_distinct_def] >>
  drule_all linear_dispatch_selects_function >> simp[]
QED
