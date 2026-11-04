(* Independent executable CALL reset probe; no dependency on the open contract. *)
Theory lowerDloadResetProbe
Ancestors
  ptrDiscipline venomExecSemantics venomCallOracleDefs extCallOracle
  venomState venomInst vfmState vfmTypes words finite_map pred_set list

(* Parser abbreviations only, not logical definitions. *)
val _ = temp_overload_on ("reset_probe_inst",
  ``mk_inst 0 CALL [Lit 0w; Lit 256w; Lit 0w; Lit 0w; Lit 0w; Lit 0w; Lit 0w] ["ok"]``);
val _ = temp_overload_on ("reset_probe_outcome",
  ``<| co_success := T; co_returnData := [];
       co_accounts := K empty_account_state;
       co_tStorage := K (K (0w:bytes32)); co_logs := []; co_toDelete := [] |>``);
val _ = temp_overload_on ("reset_probe_target",
  ``(init_venom_state "entry") with
     <|vs_outcomes := [reset_probe_outcome];
       vs_accounts := K empty_account_state|>``);
val _ = temp_overload_on ("reset_probe_source",
  ``reset_probe_target with vs_accounts :=
      K (empty_account_state with storage := (0w =+ 1w) (K (0w:bytes32)))``);
val _ = temp_overload_on ("reset_probe_post",
  ``\s. update_var "ok" 1w
     (SND (consume_call_outcome (venom_call_request s 256w 0w 0w 0w F) 0 0 s))``);

Theorem reset_probe_ordinary:
  !s st. ~computed_precompile (venom_call_request s 256w 0w 0w 0w st)
Proof
  simp[computed_precompile_addresses, venom_call_request_def, w2w_n2w] >>
  CONV_TAC wordsLib.WORD_GROUND_CONV
QED

Theorem reset_probe_call_step:
  !s fuel C.
  ~s.vs_call_ctx.cc_static /\ s.vs_outcomes = [reset_probe_outcome] ==>
  step_inst fuel C reset_probe_inst s = OK (reset_probe_post s)
Proof
  rpt strip_tac >>
  simp[Once step_inst_def, step_inst_base_def, mk_inst_def,
       eval_operand_def, exec_ext_call_def, Excl "consume_call_outcome_eq"] >>
  simp[consume_call_outcome_def, reset_probe_ordinary, take_outcome_def,
       adopt_outcome_def, venom_call_request_def]
QED

Theorem reset_probe_actual_call:
  !fuel C.
  step_inst fuel C reset_probe_inst reset_probe_source =
    OK (reset_probe_post reset_probe_source) /\
  step_inst fuel C reset_probe_inst reset_probe_target =
    OK (reset_probe_post reset_probe_target)
Proof
  rpt gen_tac >> conj_tac >> irule reset_probe_call_step >>
  simp[init_venom_state_def, empty_call_context_def]
QED

Theorem reset_probe_post_accounts:
  !s. ~s.vs_call_ctx.cc_static /\ s.vs_outcomes = [reset_probe_outcome] ==>
  (reset_probe_post s).vs_accounts = K empty_account_state
Proof
  rpt strip_tac >>
  simp[update_var_def, consume_call_outcome_def, reset_probe_ordinary,
       take_outcome_def, Excl "consume_call_outcome_eq"] >>
  simp[adopt_outcome_def, venom_call_request_def]
QED

Theorem reset_probe_account_changes:
  (reset_probe_post reset_probe_source).vs_accounts <>
    reset_probe_source.vs_accounts /\
  (reset_probe_post reset_probe_target).vs_accounts =
    reset_probe_target.vs_accounts
Proof
  `~reset_probe_source.vs_call_ctx.cc_static /\
   ~reset_probe_target.vs_call_ctx.cc_static` by
    simp[init_venom_state_def, empty_call_context_def] >>
  simp[reset_probe_post_accounts, init_venom_state_def, empty_accounts_def] >>
  simp[FUN_EQ_THM, empty_account_state_def] >>
  qexists_tac `0w` >> EVAL_TAC
QED

Theorem reset_probe_taint_asymmetry:
  !tn. tn.t_stor = {(0w,0)} ==>
  (step_taint reset_probe_inst reset_probe_source
    (reset_probe_post reset_probe_source) tn).t_stor = {} /\
  (step_taint reset_probe_inst reset_probe_target
    (reset_probe_post reset_probe_target) tn).t_stor = {(0w,0)} /\
  tn.t_stor <> {}
Proof
  gen_tac >> disch_tac >>
  mp_tac reset_probe_account_changes >> strip_tac >>
  simp[step_taint_def, adopt_reset_def, store_taint_def, mk_inst_def,
       Excl "consume_call_outcome_eq"]
QED
