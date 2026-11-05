Theory makeSsaCurrentInsertedWriteSite
Ancestors makeSsaCurrentRestrictedRuntime makeSsaCurrentAllocation
  makeSsaCurrentCertificate makeSsaCurrentOutputNames
  makeSsaCurrentReinsertionNames makeSsaCurrentReinsertionSlots
  makeSsaCurrentProps makeSsaCurrentSourceCuts venomExecProps
  makeSsaCurrentRuntimeOwners venomInst venomWf cfgWf alist list pair

Theorem current_original_outputs_no_inserted[local]:
  !vs j. ~MEM (CurrentInserted v h,w) (current_original_outputs l i j vs)
Proof
  Induct >> simp[current_original_outputs_def]
QED

Theorem current_original_annotations_no_inserted[local]:
  !insts i. ~MEM (CurrentInserted v h,w)
    (FLAT (current_original_annotations l i insts))
Proof
  Induct >> simp[current_original_annotations_def,
    current_original_outputs_no_inserted]
QED

Theorem current_block_annotation_inserted_label:
  MEM (CurrentInserted v h,w) (FLAT (current_block_annotations old pre)) ==>
  h = old.bb_label /\ w = v
Proof
  rewrite_tac[current_block_annotations_def, FLAT_APPEND, MEM_APPEND,
    current_original_annotations_no_inserted] >>
  simp[current_inserted_annotations_def, MEM_FLAT, MEM_MAP] >>
  rpt strip_tac >> gvs[MEM_MAP]
QED

Theorem current_certificate_inserted_annotation_label:
  current_structural_certificate s fn fn' s' A H events /\
  lookup_block l fn.fn_blocks = SOME old /\
  MEM (CurrentInserted v h,w) (FLAT (A l)) ==> l = h /\ w = v
Proof
  simp[current_structural_certificate_def] >> rpt strip_tac >>
  `LENGTH fn.fn_blocks = LENGTH ins` by
    (drule current_add_phi_nodes_unique_prefix >> metis_tac[LIST_REL_LENGTH]) >>
  drule_all current_provenance_annotation_lookup >> strip_tac >>
  gvs[current_block_provenance_def] >>
  metis_tac[current_block_annotation_inserted_label, lookup_block_label]
QED

Theorem current_history_member_token_name[local]:
  current_history_valid V H /\ MEM (t,w,n) H ==>
  (!v. t <> CurrentDefault v) /\ current_token_name H t = SOME n
Proof
  strip_tac >>
  `!v. t <> CurrentDefault v` by
    (fs[current_history_valid_def, EVERY_MEM] >>
     first_x_assum drule >> simp[]) >>
  `ALOOKUP H t = SOME (w,n)` by
    (irule ALOOKUP_ALL_DISTINCT_MEM >> fs[current_history_valid_def]) >>
  Cases_on `t` >> gvs[current_token_name_def]
QED

Theorem current_certificate_inserted_write_site:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  current_token_name H (CurrentInserted v h) = SOME x /\
  lookup_block l fn'.fn_blocks = SOME out /\
  MEM x (FLAT (MAP (\i. i.inst_outputs) out.bb_instructions)) ==> l = h
Proof
  strip_tac >>
  `MEM l (fn_labels fn')` by
    (simp[fn_labels_def, MEM_MAP] >>
     metis_tac[lookup_block_MEM, lookup_block_label]) >>
  `MEM l (fn_labels fn)` by metis_tac[current_certificate_output_labels] >>
  `?old. lookup_block l fn.fn_blocks = SOME old` by
    (gvs[fn_labels_def, MEM_MAP] >>
     metis_tac[MEM_lookup_block, wf_function_def, fn_labels_def]) >>
  drule_all current_certificate_event_at >> strip_tac >>
  drule_all current_certificate_events_valid >> strip_tac >>
  `?t w. MEM (t,w,x) H /\ MEM (t,w) (FLAT (A l))` by
    metis_tac[current_certificate_event_output_annotation] >>
  drule_all current_history_member_token_name >> strip_tac >>
  `t = CurrentInserted v h` by
    (irule current_allocated_name_injective >> simp[] >> metis_tac[]) >>
  gvs[] >> metis_tac[current_certificate_inserted_annotation_label]
QED

Theorem current_certificate_inserted_other_block_nonwrite:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  current_token_name H (CurrentInserted v h) = SOME x /\
  lookup_block l fn'.fn_blocks = SOME out /\ l <> h ==>
  ~MEM x (FLAT (MAP (\i. i.inst_outputs) out.bb_instructions))
Proof
  metis_tac[current_certificate_inserted_write_site]
QED
