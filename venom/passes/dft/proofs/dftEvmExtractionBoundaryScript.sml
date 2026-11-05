Theory dftEvmExtractionBoundary
Ancestors
  venomExecSemantics vfmDecreasesGas vfmContextLength list arithmetic

Theorem dft_evm_run_total:
  !es. ?e es'. run es = SOME (INR e, es')
Proof
  gen_tac >> rewrite_tac[run_eq_tr] >>
  Cases_on `run_tr (step es)` >> simp[]
QED

Theorem dft_evm_extraction_failure:
  run es = SOME (r, es') ==>
  (extract_venom_result s out off sz (run es) = NONE <=>
   LENGTH es'.contexts <> 1)
Proof
  strip_tac >> simp[extract_venom_result_def] >>
  Cases_on `es'.contexts` >- simp[] >>
  Cases_on `t` >> simp[] >> PairCases_on `h` >> simp[] >>
  pairarg_tac >> simp[]
QED

Theorem dft_evm_extraction_failure_abort:
  wf_state es /\ extract_venom_result s out off sz (run es) = NONE ==>
  ?e es'. run es = SOME (INR e, es') /\ vfm_abort e /\
    LENGTH es'.contexts <> 1
Proof
  strip_tac >> qspec_then `es` strip_assume_tac dft_evm_run_total >>
  drule dft_evm_extraction_failure >> strip_tac >>
  `LENGTH es'.contexts <> 1` by metis_tac[] >>
  `vfm_abort e` by
    (spose_not_then assume_tac >>
     drule run_contexts_length_1 >> simp[]) >>
  qexistsl_tac [`e`, `es'`] >> simp[]
QED

Theorem dft_evm_extraction_success:
  wf_state es /\
  (!e es'. run es = SOME (INR e, es') ==> ~vfm_abort e) ==>
  ?v t. extract_venom_result s out off sz (run es) = SOME (v,t)
Proof
  strip_tac >>
  Cases_on `extract_venom_result s out off sz (run es)`
  >- (drule_all dft_evm_extraction_failure_abort >> metis_tac[]) >>
  PairCases_on `x` >> metis_tac[]
QED
