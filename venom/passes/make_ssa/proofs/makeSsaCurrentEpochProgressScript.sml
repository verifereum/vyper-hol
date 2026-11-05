Theory makeSsaCurrentEpochProgress
Ancestors makeSsaCurrentEpochSplit makeSsaCurrentExecutionHistory
  makeSsaCurrentSemanticHistory venomExecProofs venomInstProps
  venomExecSemantics venomInst venomState list

Definition current_epoch_lower_bound_def:
  (current_epoch_lower_bound h n (CurrentEntry fuel) st <=> T) /\
  (current_epoch_lower_bound h n (CurrentBody fuel bb) st <=>
    (st.vs_current_bb = h ==> n <= st.vs_inst_idx))
End

Theorem current_epoch_edge_indices[local]:
  current_execution_edge fn ctx loc st phases next result after /\
  current_epoch_lower_bound h n loc st /\
  (!phis. ~MEM (CurrentBatch h phis) phases) ==>
  !i inst. MEM (CurrentOrdinary h i inst) phases ==> n <= i
Proof
  simp[current_execution_edge_cases] >> rpt strip_tac >>
  gvs[current_epoch_lower_bound_def]
QED

Theorem current_epoch_edge_successor[local]:
  current_execution_edge fn ctx loc st phases (SOME loc') (OK after) after /\
  current_epoch_lower_bound h n loc st /\
  (!phis. ~MEM (CurrentBatch h phis) phases) ==>
  current_epoch_lower_bound h n loc' after
Proof
  simp[current_execution_edge_cases] >> rpt strip_tac >>
  gvs[current_epoch_lower_bound_def, AllCaseEqs()] >>
  metis_tac[eval_phis_preserves_current_bb, step_preserves_control_flow,
    arithmeticTheory.LESS_EQ_SUC_REFL, arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem current_epoch_prefix_indices[local]:
  !loc st phases next result after.
  current_actual_prefix fn ctx loc st phases next result after ==>
  !h n. current_epoch_lower_bound h n loc st /\
    (!phis. ~MEM (CurrentBatch h phis) phases) ==>
    !i inst. MEM (CurrentOrdinary h i inst) phases ==> n <= i
Proof
  ho_match_mp_tac current_actual_prefix_ind >> rpt strip_tac
  >- gvs[]
  >- metis_tac[current_epoch_edge_indices]
  >- (gvs[MEM_APPEND] >> metis_tac[current_epoch_edge_indices,
        current_epoch_edge_successor]) >>
  gvs[current_epoch_lower_bound_def]
QED

Theorem current_header_epoch_index_progress:
  current_actual_prefix fn ctx (CurrentBody fuel bb) st phases next result after /\
  st.vs_current_bb = h /\ st.vs_inst_idx = n /\
  (!phis. ~MEM (CurrentBatch h phis) phases) ==>
  !i inst. MEM (CurrentOrdinary h i inst) phases ==> n <= i
Proof
  strip_tac >> drule current_epoch_prefix_indices >>
  disch_then (qspecl_then [`h`, `n`] mp_tac) >>
  simp[current_epoch_lower_bound_def]
QED

Theorem current_header_epoch_after_instruction_indices:
  current_actual_prefix fn ctx (CurrentBody fuel bb)
    (post with vs_inst_idx := SUC j) phases next result after /\
  post.vs_current_bb = h /\
  (!phis. ~MEM (CurrentBatch h phis) phases) ==>
  !i inst. MEM (CurrentOrdinary h i inst) phases ==> j < i
Proof
  strip_tac >> drule current_epoch_prefix_indices >>
  disch_then (qspecl_then [`h`, `SUC j`] mp_tac) >>
  simp[current_epoch_lower_bound_def] >>
  metis_tac[arithmeticTheory.LESS_EQ]
QED
