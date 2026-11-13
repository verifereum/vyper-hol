Theory rawCallOutcomeLengthPtr
Ancestors
  extCallOracle vyperCallOutcome exprSimHypsDefs exprSimPrecompiles
  vyperTypeBuiltins

(* Computed precompiles never inherit the supplied outcome's returndata.
   The affine output bounds are needed because PAD_LEFT does not truncate. *)
Theorem raw_call_ecadd_bounds[local]:
  vfmExecution$ecadd a b = SOME (x,y) ==>
  x < 2 ** 256 /\ y < 2 ** 256
Proof
  simp[vfmExecutionTheory.ecadd_def, AllCaseEqs()] >> strip_tac >>
  qspecl_then [`a`,`b`] mp_tac vyperTypeBuiltinsTheory.addAffine_bounded >>
  simp[]
QED

Theorem raw_call_ecmul_bounds[local]:
  vfmExecution$ecmul a n = SOME (x,y) ==>
  x < 2 ** 256 /\ y < 2 ** 256
Proof
  simp[vfmExecutionTheory.ecmul_def, AllCaseEqs()] >> strip_tac >>
  qspecl_then [`a`,`n`] mp_tac vyperTypeBuiltinsTheory.mulAffine_bounded >>
  PairCases_on `a` >> gvs[bn254Theory.validAffine_def]
QED

Theorem raw_call_precompile_length_probe:
  precompile_result target input = SOME (SOME bs) ==>
  LENGTH bs <= 64
Proof
  simp[extCallOracleTheory.precompile_result_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
  >- simp[listTheory.PAD_LEFT, byteTheory.LENGTH_word_to_bytes,
          SF wordsLib.SIZES_ss]
  >- (PairCases_on `z` >> drule raw_call_ecadd_bounds >> strip_tac >>
      simp[exprSimPrecompilesTheory.padded_num_to_be_bytes_word32,
           byteTheory.LENGTH_word_to_bytes, SF wordsLib.SIZES_ss]) >>
  PairCases_on `z` >> drule raw_call_ecmul_bounds >> strip_tac >>
  simp[exprSimPrecompilesTheory.padded_num_to_be_bytes_word32,
       byteTheory.LENGTH_word_to_bytes, SF wordsLib.SIZES_ss]
QED

Theorem raw_call_computed_outcome_length_probe:
  computed_precompile rq /\ take_outcome rq os = (oc,rest) ==>
  LENGTH oc.co_returnData <= 64
Proof
  Cases_on `os` >> simp[extCallOracleTheory.take_outcome_def,
    extCallOracleTheory.failed_outcome_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), extCallOracleTheory.failed_outcome_def] >>
  drule raw_call_precompile_length_probe >> simp[]
QED

Theorem take_outcome_returnData_length:
  EVERY (\oc. LENGTH oc.co_returnData < dimword(:256)) os /\
  take_outcome rq os = (outcome,rest) ==>
  LENGTH outcome.co_returnData < dimword(:256)
Proof
  Cases_on `computed_precompile rq`
  >- (strip_tac >> drule_all raw_call_computed_outcome_length_probe >>
      simp[wordsTheory.dimword_def] >> decide_tac) >>
  Cases_on `os` >>
  simp[extCallOracleTheory.take_outcome_def, extCallOracleTheory.failed_outcome_def,
    wordsTheory.dimword_def] >> rpt strip_tac >> gvs[]
QED

Theorem take_call_outcome_returnData_length:
  outcomes_accounts_typed es.outcomes /\
  take_call_outcome target data value_opt es = (INL (rq,outcome),es1) ==>
  LENGTH outcome.co_returnData < dimword(:256)
Proof
  Cases_on `es.outcomes` >>
  simp[vyperCallOutcomeTheory.take_call_outcome_def,
    vyperCallOutcomeTheory.take_request_outcome_def] >>
  pairarg_tac >> rpt strip_tac >> gvs[AllCaseEqs()] >>
  irule (SRULE [wordsTheory.dimword_def] take_outcome_returnData_length) >>
  goal_assum (drule_at Any) >>
  fs[exprSimHypsDefsTheory.outcomes_accounts_typed_def, listTheory.EVERY_MEM]
QED
