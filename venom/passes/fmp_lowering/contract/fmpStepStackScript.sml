(* Syntactic provenance, independent of alias-analysis correctness. *)
Theory fmpStepStack
Ancestors
  fmpReclaimProps fmpReclaimDefs fmpAliasDefs list pair

Definition fmp_stack_valid_def:
  fmp_stack_valid P NONE = T /\
  fmp_stack_valid P (SOME st) = EVERY P st.frs_stack
End

Definition fmp_dalloca_output_def:
  fmp_dalloca_output fn v <=>
    ?inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = DALLOCA /\
           MEM v inst.inst_outputs
End

Theorem fmp_common_top_every:
  !xs ys. EVERY P xs ==> EVERY P (fmp_common_top xs ys)
Proof
  Induct >> Cases_on `ys` >> simp[fmp_common_top_def] >>
  rpt strip_tac >> IF_CASES_TAC >> gvs[]
QED

Theorem fmp_pop_prefix_every:
  EVERY P xs ==>
  EVERY P (FST (fmp_pop_prefix dead xs)) /\
  EVERY P (SND (fmp_pop_prefix dead xs))
Proof
  mp_tac (Q.SPECL [`xs`,`dead`] fmp_pop_prefix_decomposition) >>
  metis_tac[EVERY_APPEND]
QED

Theorem fmp_pop_at_every:
  EVERY P st.frs_stack ==>
  EVERY P (FST (fmp_pop_at infos fn live env p inst st)) /\
  EVERY P (SND (fmp_pop_at infos fn live env p inst st))
Proof
  simp[fmp_pop_at_def] >> IF_CASES_TAC >> simp[fmp_pop_prefix_every]
QED

Theorem fmp_stack_valid_join:
  fmp_stack_valid P x /\ fmp_stack_valid P y ==>
  fmp_stack_valid P (fmp_reclaim_option_join x y)
Proof
  Cases_on `x` >> Cases_on `y` >>
  simp[fmp_stack_valid_def, fmp_reclaim_option_join_def,
       fmp_reclaim_join_def, fmp_common_top_every]
QED

Theorem fmp_single_output_member:
  fmp_single_output inst = SOME v ==> MEM v inst.inst_outputs
Proof
  simp[fmp_single_output_def, AllCaseEqs()] >> rpt strip_tac >> simp[]
QED

Theorem fmp_apply_effect_stack:
  EVERY P st.frs_stack /\
  (inst.inst_opcode = DALLOCA ==>
    !v. fmp_single_output inst = SOME v ==> P v) ==>
  EVERY P (fmp_apply_effect infos inst st).frs_stack
Proof
  strip_tac >> simp[fmp_apply_effect_def] >>
  Cases_on `fmp_clears_marks infos inst`
  >- simp[fmp_empty_reclaim_state_def]
  >> simp[] >> Cases_on `inst.inst_opcode = DALLOCA` >> simp[] >>
  Cases_on `fmp_single_output inst` >> simp[]
QED

Theorem fmp_transfer_stack:
  fmp_stack_valid P s /\
  (inst.inst_opcode = DALLOCA ==>
    !v. fmp_single_output inst = SOME v ==> P v) ==>
  fmp_stack_valid P (fmp_transfer infos fn live env p inst s)
Proof
  Cases_on `s` >- simp[fmp_transfer_def, fmp_reclaim_step_def,
                           fmp_stack_valid_def]
  >> simp[fmp_stack_valid_def] >> strip_tac >>
  drule (cj 2 fmp_pop_at_every) >> strip_tac >>
  simp[fmp_transfer_def, fmp_reclaim_step_def] >>
  pairarg_tac >> gvs[] >>
  simp[fmp_stack_valid_def] >>
  irule fmp_apply_effect_stack >> simp[] >> metis_tac[SND]
QED

Theorem fmp_transfer_dalloca_output:
  fmp_stack_valid (fmp_dalloca_output fn) s /\
  MEM inst (fn_insts fn) ==>
  fmp_stack_valid (fmp_dalloca_output fn)
    (fmp_transfer infos fn live env p inst s)
Proof
  strip_tac >> irule fmp_transfer_stack >> simp[] >>
  rpt strip_tac >> simp[fmp_dalloca_output_def] >>
  metis_tac[fmp_single_output_member]
QED

Theorem fmp_reclaim_target_stack:
  fmp_stack_valid P s /\
  FST (fmp_reclaim_step infos fn live env p inst s) = SOME v ==>
  P v
Proof
  Cases_on `s` >- simp[fmp_reclaim_step_def] >>
  simp[fmp_stack_valid_def, fmp_reclaim_step_def] >>
  pairarg_tac >> gvs[] >> strip_tac >>
  drule fmp_pop_target_mem >> strip_tac >>
  drule (cj 1 fmp_pop_at_every) >>
  simp[EVERY_MEM] >> metis_tac[FST]
QED
