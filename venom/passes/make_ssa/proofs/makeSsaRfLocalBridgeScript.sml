Theory makeSsaRfLocalBridge
Ancestors makeSsaRfRenameTrace makeSsaRfAllocation makeSsaRfAssign makeSsaRfWitness
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

Theorem current_outputs_trace_nonoutput_avoids:
  !anns s rs H E names s' rs' H' E'.
  current_outputs_trace anns s rs H E names s' rs' H' E' /\
  current_annotations_ok V H anns /\
  current_allocation_consistent V H s rs /\ current_env_realizes H E rs V /\
  current_env_owned V H E /\ MEM w V /\ ~MEM w (MAP SND anns) ==>
  ~MEM (latest_current_name rs' w) names
Proof
  Induct >> simp[current_outputs_trace_def] >>
  gen_tac >> PairCases_on `h` >> simp[current_outputs_trace_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  `current_annotations_ok V (H ++ [(h0,h1,n)]) anns` by
    metis_tac[current_annotations_tail] >>
  `(!v. h0 <> CurrentDefault v) /\ ~MEM h0 (MAP FST H) /\ MEM h1 V` by
    fs[current_annotations_ok_def] >>
  `current_allocation_consistent V (H ++ [(h0,h1,n)]) s1 rs1` by
    (irule current_push_consistent >> metis_tac[]) >>
  `current_env_realizes (H ++ [(h0,h1,n)]) ((h1 =+ h0) E) rs1 V` by
    (irule current_push_env_realizes >> metis_tac[]) >>
  `current_env_owned V (H ++ [(h0,h1,n)]) ((h1 =+ h0) E)` by
    metis_tac[current_env_owned_push] >>
  `latest_current_name rs' w = latest_current_name rs1 w` by
    metis_tac[current_outputs_trace_nonoutput] >>
  `latest_current_name rs1 w = latest_current_name rs w` by
    metis_tac[current_push_latest] >>
  conj_tac
  >- metis_tac[current_push_nonowner_separation] >>
  first_x_assum irule >> metis_tac[]
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

Theorem current_local_trace_rf_back_trace:
  !annss insts s rs H E insts' s' rs' H' E'.
  current_local_trace annss insts s rs H E insts' s' rs' H' E' /\
  current_annotations_ok V H (FLAT annss) /\
  current_allocation_consistent V H s rs /\ current_env_realizes H E rs V /\
  current_env_owned V H E /\
  EVERY (\i. ALL_DISTINCT i.inst_outputs /\
    EVERY (rf_operand_in V) i.inst_operands) insts ==>
  rf_back_trace V (latest_current_name rs) (latest_current_name rs')
    (REVERSE insts) (REVERSE insts')
Proof
  Induct >> simp[current_local_trace_def, rf_back_trace_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  `current_annotations_ok V H h` by
    metis_tac[current_annotations_split, FLAT] >>
  `current_allocation_consistent V H1 s1 rs1 /\ current_env_realizes H1 E1 rs1 V` by
    (irule current_inst_trace_preserves >> metis_tac[]) >>
  `current_env_owned V H1 E1` by metis_tac[current_inst_trace_owned] >>
  `current_annotations_ok V H1 (FLAT annss)` by
    (fs[current_inst_trace_def] >>
     irule current_outputs_trace_remaining >> metis_tac[FLAT]) >>
  `rf_back_trace V (latest_current_name rs1) (latest_current_name rs')
     (REVERSE rest) (REVERSE rest1)` by
    (first_x_assum irule >> metis_tac[]) >>
  `rf_local_step V (latest_current_name rs) (latest_current_name rs1) inst inst1` by
    (irule current_inst_trace_rf_step >> metis_tac[]) >>
  simp[REVERSE_DEF] >> irule rf_back_trace_append >>
  qexists_tac `latest_current_name rs1` >>
  simp[rf_back_trace_def] >> metis_tac[]
QED
