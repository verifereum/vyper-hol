Theory fmpStageFmpStepsRetFresh
Ancestors
  fmpStepAnalysis fmpStepStack fmpReclaimProps fmpReclaimDefs
  venomWf venomFnInstsProofs venomInst list pair

Theorem fmp_return_popped_outputs_fresh:
  ssa_form fn /\ MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
  fmp_reclaim_states infos fn = SOME states /\
  df_at NONE states lbl idx = SOME st ==>
  !v. MEM v (SND (fmp_pop_at infos fn live env (lbl,idx) inst st)) ==>
      ~MEM v inst.inst_outputs
Proof
  strip_tac >> drule_all fmp_reclaim_states_stack >> strip_tac >>
  `!v. MEM v (SND (fmp_pop_at infos fn live env (lbl,idx) inst st)) ==>
       MEM v st.frs_stack` by
    (simp[fmp_pop_at_def] >> rw[] >>
     metis_tac[fmp_pop_prefix_decomposition, MEM_APPEND]) >>
  rpt strip_tac >>
  `MEM v st.frs_stack` by metis_tac[] >>
  `fmp_dalloca_output fn v` by gvs[EVERY_MEM] >>
  gvs[fmp_dalloca_output_def, ssa_form_def] >>
  `inst = inst'` by metis_tac[all_distinct_flat_map_unique] >> gvs[]
QED
