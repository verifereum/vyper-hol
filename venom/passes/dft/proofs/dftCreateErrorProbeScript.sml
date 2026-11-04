Theory dftCreateErrorProbe
Ancestors
  o1PassContract venomExecSemantics vfmContextLength

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
