Theory dftPositionalOrdinaryBoundary
Ancestors
  dftPositionalStep dftPositionalReturn dftPositionalPhase dftPositionalRoot
  dftPositionalRuntime dftOriginalScheduleRuntime dftOpenMachine
  dftOccurrenceMachine list arithmetic

(* Only the selected two positions are delegated to the local crossing.
   In particular, neither parameter is required to be an INVOKE. *)
Definition dft_pos_unaffected_def:
  dft_pos_unaffected C D fi bi pre l r <=>
    (?f g s ls rs nL nR.
      l.dft_occ_core = DftOpen (DftEnter f 0 s) ls nL /\
      r.dft_occ_core = DftOpen (DftEnter g 0 s) rs nR) \/
    (?result ls rs nL nR.
      l.dft_occ_core = DftOpen (DftDone result) ls nL /\
      r.dft_occ_core = DftOpen (DftDone result) rs nR) \/
    (?f g b b' s ls rs nL nR j k.
      l.dft_occ_core = DftOpen (DftAt f 0 b s) ls nL /\
      r.dft_occ_core = DftOpen (DftAt g 0 b' s) rs nR /\
      dft_pos_slot C D j k f g b b' /\
      (j <> fi \/ k <> bi \/
        (s.vs_inst_idx <> LENGTH pre /\ s.vs_inst_idx <> SUC (LENGTH pre))))
End

Theorem dft_pos_unaffected_next:
  D = dft_pos_edit_ctx fi bi pre x y post C /\
  dft_pos_runtime_ready C fi bi pre x y post /\
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  dft_pos_phase C D fi bi pre x y post l r /\
  dft_pos_unaffected C D fi bi pre l r ==>
  ?b. (b = 1 \/ b = 2) /\
    dft_pos_phase C D fi bi pre x y post
      (dft_occ_oracle_next w C l) (FUNPOW (dft_occ_oracle_next w D) b r)
Proof
  simp[dft_pos_unaffected_def] >> rpt strip_tac
  >- (qexists `1` >> simp[] >> irule dft_pos_enter_next >>
      goal_assum (drule_at Any) >> metis_tac[])
  >- (irule dft_pos_done_next >> metis_tac[]) >>
  qexists `1` >> simp[] >> irule dft_pos_at_outside_next >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem dft_pos_unaffected_memory_backward:
  D = dft_pos_edit_ctx fi bi pre x y post C /\
  dft_pos_runtime_ready C fi bi pre x y post /\
  dft_pos_unaffected C D fi bi pre l r /\
  dft_open_observe h' inst t' r.dft_occ_core ==>
  ?h t. dft_open_observe h inst t l.dft_occ_core /\
    dft_pos_functions C D h h' /\ t.vs_memory = t'.vs_memory /\
    inst_mem_ranges inst t = inst_mem_ranges inst t'
Proof
  simp[dft_pos_unaffected_def] >> rpt strip_tac
  >- gvs[dft_open_observe_def]
  >- gvs[dft_open_observe_def] >>
  irule dft_pos_at_outside_memory_backward >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem dft_pos_ordinary_entry:
  dft_original_context Corig C /\ dft_original_context Corig D /\
  j < LENGTH C.ctx_functions /\
  fn_entry_label (EL j C.ctx_functions) = SOME s.vs_current_bb ==>
  dft_pos_phase C D fi bi pre x y post
    (dft_occ_init (DftOpen (DftEnter (EL j C.ctx_functions) 0 s) [] nL))
    (dft_occ_init (DftOpen (DftEnter (EL j D.ctx_functions) 0 s) [] nR)) /\
  dft_pos_unaffected C D fi bi pre
    (dft_occ_init (DftOpen (DftEnter (EL j C.ctx_functions) 0 s) [] nL))
    (dft_occ_init (DftOpen (DftEnter (EL j D.ctx_functions) 0 s) [] nR))
Proof
  strip_tac >> conj_tac
  >- metis_tac[dft_pos_original_entry_roots] >>
  simp[dft_pos_unaffected_def, dft_occ_init_def]
QED

Theorem dft_pos_unaffected_memory_forward:
  D = dft_pos_edit_ctx fi bi pre x y post C /\
  dft_pos_runtime_ready C fi bi pre x y post /\
  dft_pos_unaffected C D fi bi pre l r /\
  dft_open_observe h inst t l.dft_occ_core ==>
  ?h' t'. dft_open_observe h' inst t' r.dft_occ_core /\
    dft_pos_functions C D h h' /\ t.vs_memory = t'.vs_memory /\
    inst_mem_ranges inst t = inst_mem_ranges inst t'
Proof
  simp[dft_pos_unaffected_def] >> rpt strip_tac
  >- gvs[dft_open_observe_def]
  >- gvs[dft_open_observe_def] >>
  irule dft_pos_at_outside_memory_forward >>
  goal_assum (drule_at Any) >> metis_tac[]
QED
