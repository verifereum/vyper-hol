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

Theorem create_probe_run_not_none:
  run es <> NONE
Proof
  simp[vfmDecreasesGasTheory.run_eq_tr] >>
  Cases_on `vfmDecreasesGas$run_tr (step es)` >> simp[]
QED

Theorem create_probe_extract_run_none_iff:
  extract_venom_result s output off len (run es) = NONE <=>
  ?result fs. run es = SOME (result,fs) /\ LENGTH fs.contexts <> 1
Proof
  simp[create_probe_extract_none_iff, create_probe_run_not_none]
QED

Definition create_frame_safe_def:
  create_frame_safe s <=>
  s.contexts <> [] /\ LENGTH s.contexts <= SUC context_limit /\
  EVERY (wf_context o FST) s.contexts /\
  stack_room_ok s /\ gas_stack_ok s /\ outputTo_consistent_stack s
End

Theorem create_probe_constructor_frame_safe:
  create_frame_safe (make_venom_create_state s a gas value code)
Proof
  simp[create_frame_safe_def, make_venom_create_state_def,
       vfmExecutionPropTheory.wf_context_def,
       vfmExecutionPropTheory.stack_room_ok_def,
       vfmExecutionPropTheory.gas_stack_ok_def,
       vfmExecutionPropTheory.outputTo_consistent_stack_def,
       vfmExecutionPropTheory.outputTo_consistent_ctx_def,
       make_rollback_def, vfmContextTheory.initial_msg_params_def]
QED

Theorem create_probe_refund_bound:
  create_frame_safe s /\ LENGTH s.contexts >= 2 ==>
  (FST (HD s.contexts)).msgParams.gasLimit - (FST (HD s.contexts)).gasUsed <=
  (FST (EL 1 s.contexts)).gasUsed
Proof
  simp[create_frame_safe_def] >> rpt strip_tac >>
  drule_all vfmHandleStepTheory.gas_stack_ok_parent_has_child_unused >> simp[]
QED

Theorem create_probe_run_tr_singleton[local]:
  (!s r t. P s /\ step s = (r,t) ==> P t) /\
  (!s e t. P s /\ step s = (INR e,t) ==> LENGTH t.contexts = 1) ==>
  !r s. P s /\ (!e. r = INR e ==> LENGTH s.contexts = 1) ==>
  LENGTH (SND (vfmDecreasesGas$run_tr (r,s))).contexts = 1
Proof
  strip_tac >> recInduct vfmDecreasesGasTheory.run_tr_ind >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  Cases_on `r`
  >- (first_x_assum (qspec_then `x` mp_tac) >> simp[] >>
      Cases_on `step s` >> simp[] >>
      `P r /\ (!e. q = INR e ==> LENGTH r.contexts = 1)` by metis_tac[] >>
      strip_tac >>
      pure_once_rewrite_tac[vfmDecreasesGasTheory.run_tr_def] >>
      simp[]) >>
  pure_once_rewrite_tac[vfmDecreasesGasTheory.run_tr_def] >> gvs[]
QED

Theorem create_probe_run_singleton:
  (!s r t. P s /\ step s = (r,t) ==> P t) /\
  (!s e t. P s /\ step s = (INR e,t) ==> LENGTH t.contexts = 1) /\
  P es /\ run es = SOME (r,fs) ==> LENGTH fs.contexts = 1
Proof
  strip_tac >>
  `!rr ss. P ss /\ (!e. rr = INR e ==> LENGTH ss.contexts = 1) ==>
    LENGTH (SND (vfmDecreasesGas$run_tr (rr,ss))).contexts = 1` by
    (match_mp_tac create_probe_run_tr_singleton >> metis_tac[]) >>
  first_x_assum (qspecl_then [`FST (step es)`, `SND (step es)`] mp_tac) >>
  Cases_on `step es` >> gvs[] >>
  `P r' /\ (!e. q = INR e ==> LENGTH r'.contexts = 1)` by metis_tac[] >>
  gvs[vfmDecreasesGasTheory.run_eq_tr] >>
  Cases_on `vfmDecreasesGas$run_tr (q,r')` >> gvs[]
QED

Theorem create_probe_frame_safe_extract:
  (!s r t. create_frame_safe s /\ step s = (r,t) ==> create_frame_safe t) /\
  (!s e t. create_frame_safe s /\ step s = (INR e,t) ==> LENGTH t.contexts = 1) ==>
  extract_venom_result s output off len
    (run (make_venom_create_state s a gas value code)) <> NONE
Proof
  strip_tac >> simp[create_probe_extract_run_none_iff] >>
  rpt strip_tac >>
  `create_frame_safe (make_venom_create_state s a gas value code)` by
    simp[create_probe_constructor_frame_safe] >>
  drule_all create_probe_run_singleton >> simp[]
QED

