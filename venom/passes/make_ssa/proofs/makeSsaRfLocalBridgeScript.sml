Theory makeSsaRfLocalBridge
Ancestors makeSsaRfRenameTrace makeSsaRfAllocation makeSsaRfAssign
  makeSsaCurrentDefs venomInst list pair

Theorem current_outputs_trace_nonoutput:
  !anns s rs H E names s' rs' H' E' w.
  current_outputs_trace anns s rs H E names s' rs' H' E' /\
  ~MEM w (MAP SND anns) ==>
  latest_current_name rs' w = latest_current_name rs w
Proof
  Induct >> simp[current_outputs_trace_def] >>
  gen_tac >> PairCases_on `h` >> simp[current_outputs_trace_def] >>
  rpt strip_tac >> first_x_assum drule >> simp[] >>
  metis_tac[current_push_latest]
QED

Theorem current_outputs_trace_final_names:
  !anns s rs H E names s' rs' H' E'.
  current_outputs_trace anns s rs H E names s' rs' H' E' /\
  ALL_DISTINCT (MAP SND anns) ==>
  names = MAP (latest_current_name rs') (MAP SND anns)
Proof
  Induct >> simp[current_outputs_trace_def] >>
  gen_tac >> PairCases_on `h` >> simp[current_outputs_trace_def] >>
  rpt strip_tac >> gvs[] >> conj_tac
  >- (drule_all current_outputs_trace_nonoutput >>
      metis_tac[current_push_latest]) >>
  metis_tac[]
QED

Theorem rename_current_operands_rf:
  !ops. rename_current_operands rs ops = MAP (rf_map_operand (latest_current_name rs)) ops
Proof
  Induct >> simp[rename_current_operands_def] >>
  Cases_on `h` >> simp[rename_current_operands_def, rf_map_operand_def]
QED

Theorem current_inst_trace_rf_step:
  current_inst_trace anns inst s rs H E inst' s' rs' H' E' /\
  current_annotations_ok V H anns /\
  current_allocation_consistent V H s rs /\ current_env_realizes H E rs V /\
  current_env_owned V H E /\ ALL_DISTINCT inst.inst_outputs ==>
  rf_local_step V (latest_current_name rs) (latest_current_name rs') inst inst'
Proof
  strip_tac >>
  `current_allocation_consistent V H' s' rs' /\ current_env_realizes H' E' rs' V` by
    metis_tac[current_inst_trace_preserves] >>
  `current_env_owned V H' E'` by metis_tac[current_inst_trace_owned] >>
  gvs[current_inst_trace_def] >>
  `names = MAP (latest_current_name rs') (MAP SND anns)` by
    metis_tac[current_outputs_trace_final_names] >>
  `!v. ~MEM v (MAP SND anns) ==>
      latest_current_name rs' v = latest_current_name rs v` by
    metis_tac[current_outputs_trace_nonoutput] >>
  `!w. MEM w inst.inst_outputs ==> MEM w V` by
    (qpat_assum `MAP SND anns = _` (fn th => rewrite_tac[GSYM th]) >>
     rpt strip_tac >> fs[MEM_MAP] >>
     rename1 `MEM y anns` >> PairCases_on `y` >> gvs[] >>
     fs[current_annotations_ok_def, EVERY_MEM] >>
     first_x_assum drule >> simp[]) >>
  `!v w. MEM v V /\ MEM w V /\ v <> w ==>
      latest_current_name rs' v <> latest_current_name rs' w` by
    (fs[current_allocation_consistent_def] >>
     metis_tac[current_latest_name_separation]) >>
  `!v. MEM v V /\ ~MEM v inst.inst_outputs ==>
      latest_current_name rs' v = latest_current_name rs v /\
      ~MEM (latest_current_name rs' v)
        (MAP (latest_current_name rs') inst.inst_outputs)` by
    (rpt strip_tac
     >- metis_tac[] >>
     fs[MEM_MAP] >>
     `MEM y V` by metis_tac[] >>
     `v <> y` by metis_tac[] >>
     metis_tac[]) >>
  Cases_on `inst.inst_opcode = PHI` >>
  simp[rf_local_step_def, rename_current_operands_rf] >>
  rpt strip_tac >>
  qpat_x_assum `!v. MEM v V /\ ~MEM v inst.inst_outputs ==> _` drule_all >>
  metis_tac[]
QED
