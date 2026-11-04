Theory dftCreateErrorProbe
Ancestors
  o1PassContract venomExecSemantics vfmContextLength vfmDomainCollection

Definition create_probe_state_def:
  create_probe_state = (init_venom_state "entry") with
    <| vs_labels := FEMPTY |+ ("code_end",0w);
       vs_call_ctx := empty_call_context with cc_gas := 1000 |>
End

Theorem create_probe_state_ok:
  o1_run_state_ok create_probe_state
Proof
  simp[o1_run_state_ok_def, unitTransformDefsTheory.o1_initial_state_ok_def,
       lowerDloadDefsTheory.code_layout_valid_def, create_probe_state_def,
       venomStateTheory.init_venom_state_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem create_probe_empty_extract:
  extract_venom_result create_probe_state 0w 0 0
    (run (make_venom_create_state create_probe_state 1w 100 0 [])) <> NONE
Proof
  simp[Once vfmExecutionTheory.run_def, Once WhileTheory.OWHILE_THM] >>
  EVAL_TAC >> simp[Once WhileTheory.OWHILE_THM] >> EVAL_TAC
QED

Theorem create_probe_extract_none_iff:
  extract_venom_result s output off len rr = NONE <=>
  rr = NONE \/
  ?result fs. rr = SOME (result,fs) /\ LENGTH fs.contexts <> 1
Proof
  Cases_on `rr` >- simp[extract_venom_result_def] >>
  PairCases_on `x` >>
  Cases_on `x1.contexts` >> simp[extract_venom_result_def] >>
  Cases_on `t` >> simp[] >> PairCases_on `h` >> simp[] >>
  Cases_on `x0` >> simp[] >> Cases_on `y` >> simp[]
QED

Theorem create_probe_nonabort_extract:
  run es = SOME (r,fs) /\ vfmExecutionProp$wf_state es /\
  (!e. r = INR e ==> ~vfm_abort e) ==>
  extract_venom_result s output off len (run es) <> NONE
Proof
  strip_tac >>
  `LENGTH fs.contexts = 1` by
    (irule vfmContextLengthTheory.run_contexts_length_1 >> metis_tac[]) >>
  simp[create_probe_extract_none_iff]
QED

Theorem create_probe_constructor_wf_iff:
  vfmExecutionProp$wf_state (make_venom_create_state s a gas value code) <=>
  wf_accounts (transfer_value s.vs_call_ctx.cc_address a value s.vs_accounts)
Proof
  rewrite_tac[vfmExecutionPropTheory.wf_state_def] >>
  simp[make_venom_create_state_def,
       vfmExecutionPropTheory.all_accounts_def,
       vfmExecutionPropTheory.stack_room_ok_def,
       vfmExecutionPropTheory.gas_stack_ok_def,
       vfmExecutionPropTheory.outputTo_consistent_stack_def,
       vfmExecutionPropTheory.outputTo_consistent_ctx_def,
       make_rollback_def, vfmContextTheory.initial_msg_params_def]
QED

Theorem create_probe_fatal_keeps_state:
  vfm_abort e ==> handle_step e es = (INR e,es)
Proof
  simp[vfmExecutionTheory.handle_step_def, vfmExecutionTheory.reraise_def]
QED

Theorem create_probe_collect_domain_check:
  domain_check err check upd_dom cont (s with msdomain := Collect d) =
  cont (s with msdomain := Collect (upd_dom d))
Proof
  simp[vfmExecutionTheory.domain_check_def, vfmExecutionTheory.set_domain_def,
       vfmExecutionTheory.ignore_bind_def, vfmExecutionTheory.return_def,
       vfmExecutionTheory.bind_def]
QED

Theorem create_probe_minimal_no_outside:
  computes_minimal_domain m /\ m s = (r,t) /\ s.msdomain = Collect d ==>
  !x. r <> INR (SOME (OutsideDomain x))
Proof
  simp[vfmDomainCollectionTheory.computes_minimal_domain_def] >> metis_tac[]
QED

Theorem create_probe_collect_step_no_outside:
  s.msdomain = Collect d /\ step s = (r,t) ==>
  !x. r <> INR (SOME (OutsideDomain x))
Proof
  metis_tac[create_probe_minimal_no_outside,
            vfmDomainCollectionTheory.step_computes_minimal_domain]
QED
