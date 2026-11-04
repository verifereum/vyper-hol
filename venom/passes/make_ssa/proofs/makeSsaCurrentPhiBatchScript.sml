Theory makeSsaCurrentPhiBatch
Ancestors
  venomExecSemantics venomState stateFrame venomInst list alist finite_map

Theorem current_eval_phis_batch:
  !prefix suffix.
  EVERY (\i. i.inst_opcode = PHI) prefix /\
  (suffix = [] \/ (HD suffix).inst_opcode <> PHI) ==>
  eval_phis st (prefix ++ suffix) =
    if EVERY IS_SOME (MAP (eval_one_phi st) prefix) then
      OK (FOLDR (\(out,value) t. update_var out value t) st
        (MAP (THE o eval_one_phi st) prefix))
    else Error "phi evaluation failed"
Proof
  Induct
  >- (Cases >> simp[eval_phis_def]) >>
  rpt gen_tac >> strip_tac >>
  first_x_assum (qspec_then `suffix` mp_tac) >>
  impl_tac >- fs[] >> strip_tac >> gvs[] >>
  fs[listTheory.EVERY_DEF] >> simp[eval_phis_def] >>
  Cases_on `eval_one_phi st h` >> simp[] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `EVERY IS_SOME (MAP (eval_one_phi st) prefix)` >>
  full_simp_tac std_ss [listTheory.APPEND_NIL] >>
  asm_simp_tac std_ss [exec_result_case_def]
QED

Theorem current_phi_writes_lookup:
  !writes. lookup_var v
    (FOLDR (\(out,value) t. update_var out value t) st writes) =
    case ALOOKUP writes v of NONE => lookup_var v st | SOME value => SOME value
Proof
  Induct >> simp[] >> gen_tac >> PairCases_on `h` >>
  fs[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  Cases_on `v = h0` >> simp[]
QED

Theorem current_phi_writes_frame:
  !writes. execution_frame
    (FOLDR (\(out,value) t. update_var out value t) st writes) =
    execution_frame st
Proof
  Induct >> simp[] >> gen_tac >> PairCases_on `h` >>
  fs[update_var_def, execution_frame_def]
QED

Theorem current_phi_writes_first_priority:
  lookup_var out
    (FOLDR (\(name,value) t. update_var name value t) st
      [(out,first); (out,second)]) = SOME first
Proof
  simp[current_phi_writes_lookup]
QED

Theorem current_eval_phis_batch_lookup:
  EVERY (\i. i.inst_opcode = PHI) prefix /\
  (suffix = [] \/ (HD suffix).inst_opcode <> PHI) /\
  eval_phis st (prefix ++ suffix) = OK post ==>
  lookup_var v post =
    case ALOOKUP (MAP (THE o eval_one_phi st) prefix) v of
      NONE => lookup_var v st | SOME value => SOME value
Proof
  strip_tac >> drule current_eval_phis_batch >>
  disch_then (qspecl_then [`st`, `suffix`] mp_tac) >>
  impl_tac >- simp[] >>
  Cases_on `EVERY IS_SOME (MAP (eval_one_phi st) prefix)` >>
  asm_simp_tac std_ss [] >> strip_tac >>
  gvs[current_phi_writes_lookup]
QED

Theorem current_eval_phis_batch_frame:
  EVERY (\i. i.inst_opcode = PHI) prefix /\
  (suffix = [] \/ (HD suffix).inst_opcode <> PHI) /\
  eval_phis st (prefix ++ suffix) = OK post ==>
  execution_frame post = execution_frame st
Proof
  strip_tac >> drule current_eval_phis_batch >>
  disch_then (qspecl_then [`st`, `suffix`] mp_tac) >>
  impl_tac >- simp[] >>
  Cases_on `EVERY IS_SOME (MAP (eval_one_phi st) prefix)` >>
  asm_simp_tac std_ss [] >> strip_tac >>
  gvs[current_phi_writes_frame]
QED
