Theory makeSsaCurrentInsertedPersistence
Ancestors makeSsaCurrentInsertedWriteSite makeSsaCurrentRestrictedRuntime
  makeSsaCurrentRuntimeTransport makeSsaCurrentExecutionHistory
  makeSsaCurrentSemanticHistory makeSsaCurrentTemporalWrites
  makeSsaCurrentSourceCuts makeSsaCurrentAllocation
  venomInst venomWf cfgWf list pair

Theorem current_inserted_avoiding_phase_output[local]:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  current_token_name H (CurrentInserted v h) = SOME x /\
  current_phase_occurs fn' phase /\
  (!i inst. phase <> CurrentOrdinary h i inst) /\
  (!phis. phase <> CurrentBatch h phis) ==>
  ~MEM x (current_phase_outputs phase)
Proof
  strip_tac >> strip_tac >>
  drule_all current_phase_occurs_output_block >> strip_tac >>
  `l = h` by metis_tac[current_certificate_inserted_write_site] >>
  Cases_on `phase` >> gvs[]
QED

Theorem current_inserted_avoiding_history_outputs[local]:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  current_token_name H (CurrentInserted v h) = SOME x /\
  EVERY (current_phase_occurs fn') phases /\
  (!i inst. ~MEM (CurrentOrdinary h i inst) phases) /\
  (!phis. ~MEM (CurrentBatch h phis) phases) ==>
  !phase. MEM phase phases ==> ~MEM x (current_phase_outputs phase)
Proof
  simp[EVERY_MEM] >> rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  irule current_inserted_avoiding_phase_output >> metis_tac[]
QED

Theorem current_inserted_avoiding_history_writes:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  current_token_name H (CurrentInserted v h) = SOME x /\
  EVERY (current_phase_occurs fn') phases /\
  current_semantic_history k ctx phases b writes raw b' /\
  (!i inst. ~MEM (CurrentOrdinary h i inst) phases) /\
  (!phis. ~MEM (CurrentBatch h phis) phases) ==>
  !value. ~MEM (x,value) writes
Proof
  strip_tac >>
  `!phase. MEM phase phases ==> ~MEM x (current_phase_outputs phase)` by
    metis_tac[current_inserted_avoiding_history_outputs] >>
  drule_all current_semantic_history_output_exclusion >>
  simp[EVERY_MEM] >> metis_tac[FST]
QED

Theorem current_inserted_avoiding_history_lookup:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  current_token_name H (CurrentInserted v h) = SOME x /\
  EVERY (current_phase_occurs fn') phases /\
  current_semantic_history k ctx phases b writes raw b' /\
  (!i inst. ~MEM (CurrentOrdinary h i inst) phases) /\
  (!phis. ~MEM (CurrentBatch h phis) phases) ==>
  lookup_var x b' = lookup_var x b
Proof
  strip_tac >>
  `!phase. MEM phase phases ==> ~MEM x (current_phase_outputs phase)` by
    metis_tac[current_inserted_avoiding_history_outputs] >>
  metis_tac[current_semantic_history_output_no_write]
QED

Theorem current_inserted_avoiding_actual_prefix_lookup:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  current_token_name H (CurrentInserted v h) = SOME x /\
  current_actual_prefix fn' ctx loc b phases next result b' /\
  (!i inst. ~MEM (CurrentOrdinary h i inst) phases) /\
  (!phis. ~MEM (CurrentBatch h phis) phases) ==>
  lookup_var x b' = lookup_var x b
Proof
  strip_tac >>
  drule_then assume_tac current_actual_prefix_occurs >>
  drule current_actual_prefix_history >>
  disch_then (qspec_then `0` strip_assume_tac) >>
  irule current_inserted_avoiding_history_lookup >> metis_tac[]
QED
