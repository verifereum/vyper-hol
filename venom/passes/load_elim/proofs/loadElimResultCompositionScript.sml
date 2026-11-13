Theory loadElimResultComposition
Ancestors
  loadElimMemoryRel loadElimPaddedNoncall stateEquiv stateFrame
  passSimulationProps venomState venomExecSemantics pred_set

Theorem le_padded_exec_widen:
  A SUBSET B /\ padded_exec_equiv A s t ==> padded_exec_equiv B s t
Proof
  simp[padded_exec_equiv_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem le_padded_control_widen:
  A SUBSET B /\ le_padded_control A s t ==> le_padded_control B s t
Proof
  simp[le_padded_control_def] >> metis_tac[le_padded_exec_widen]
QED

Theorem le_padded_control_trans:
  le_padded_control B s t /\ le_padded_control B t u ==>
  le_padded_control B s u
Proof
  simp[le_padded_control_def] >> metis_tac[padded_exec_equiv_trans]
QED

Theorem le_padded_result_widen:
  A SUBSET B /\
  lift_result (le_padded_control A) (padded_exec_equiv A) (padded_exec_equiv A) r t ==>
  lift_result (le_padded_control B) (padded_exec_equiv B) (padded_exec_equiv B) r t
Proof
  strip_tac >> irule lift_result_mono >>
  goal_assum (drule_at Any) >> metis_tac[le_padded_control_widen, le_padded_exec_widen]
QED

Theorem le_padded_result_trans:
  lift_result (le_padded_control B) (padded_exec_equiv B) (padded_exec_equiv B) r s /\
  lift_result (le_padded_control B) (padded_exec_equiv B) (padded_exec_equiv B) s t ==>
  lift_result (le_padded_control B) (padded_exec_equiv B) (padded_exec_equiv B) r t
Proof
  strip_tac >> irule lift_result_trans >>
  metis_tac[le_padded_control_trans, padded_exec_equiv_trans]
QED

Theorem le_padded_result_error_target:
  lift_result (le_padded_control B) (padded_exec_equiv B) (padded_exec_equiv B) r (Error e) ==>
  ?e'. r = Error e'
Proof
  Cases_on `r` >> simp[lift_result_def]
QED

Theorem le_padded_result_or_error_trans:
  ((?e. r = Error e) \/
   lift_result (le_padded_control B) (padded_exec_equiv B) (padded_exec_equiv B) r s) /\
  ((?e. s = Error e) \/
   lift_result (le_padded_control B) (padded_exec_equiv B) (padded_exec_equiv B) s t) ==>
  (?e. r = Error e) \/
   lift_result (le_padded_control B) (padded_exec_equiv B) (padded_exec_equiv B) r t
Proof
  metis_tac[le_padded_result_error_target, le_padded_result_trans]
QED

Theorem le_exact_exec_padded:
  execution_equiv A s t ==> padded_exec_equiv A s t
Proof
  gvs[execution_equiv_def, execution_frame_eq_reconstruct] >>
  simp[padded_exec_equiv_def, execution_frame_def, read_memory_def] >>
  simp[venom_state_component_equality]
QED

Theorem le_exact_state_padded:
  state_equiv A s t ==> le_padded_control A s t
Proof
  simp[state_equiv_def, le_padded_control_def] >> metis_tac[le_exact_exec_padded]
QED

Theorem le_exact_result_padded:
  result_equiv {} r t ==>
  lift_result (le_padded_control B) (padded_exec_equiv B) (padded_exec_equiv B) r t
Proof
  Cases_on `r` >> Cases_on `t` >>
  simp[result_equiv_def, lift_result_def] >>
  metis_tac[le_exact_exec_padded, le_exact_state_padded,
            le_padded_exec_widen, le_padded_control_widen, EMPTY_SUBSET]
QED
