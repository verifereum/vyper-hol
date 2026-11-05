Theory makeSsaCurrentCollapsedOrigin
Ancestors makeSsaCurrentInsertedValue makeSsaCurrentCleanupClassify
  makeSsaCurrentPhiRuntime makeSsaCurrentInsertedNonself venomExecProofs
  makeSsaCurrentAllocation makeSsaCurrentDefaultAudit makeSsaCurrentFinalSlots
  makeSsaCurrentReinsertionNames makeSsaCurrentReinsertionSlots
  makeSsaCurrentTraceCertificate makeSsaCurrentAnalysis cfgAnalysisProps
  makeSsaCurrentPlacementCut makeSsaCurrentCertificate makeSsaCurrentMergeSeed
  makeSsaCurrentDefaultOrigin venomInst venomWf list

(* Implementation boundary: every incoming spelling of a collapsed PHI is
   either its self name or its unique nonself source. *)
Theorem current_collapsed_slot_names:
  i.inst_opcode = PHI /\ i.inst_outputs = [x] /\
  i.inst_operands = current_phi_slots slots /\
  (simplify_current_phi i).inst_opcode = ASSIGN /\
  (simplify_current_phi i).inst_operands = [Var y] ==>
  x <> y /\ !p n. MEM (p,n) slots ==> n = x \/ n = y
Proof
  strip_tac >>
  `FILTER (\n. n <> x) (MAP SND slots) =
   FILTER (\n. n <> x) (MAP SND slots)` by simp[] >>
  drule_all current_phi_slots_classify >>
  simp[] >>
  Cases_on `FILTER (\n. n <> x) (MAP SND slots)` >> simp[]
  >- (strip_tac >> gvs[]) >>
  IF_CASES_TAC >> strip_tac >> gvs[] >>
  `MEM h (FILTER (\n. n <> x) (MAP SND slots))` by simp[] >>
  `x <> h` by gvs[MEM_FILTER] >>
  simp[] >> rpt strip_tac >>
  Cases_on `n = x` >- simp[] >>
  `MEM n (FILTER (\n. n <> x) (MAP SND slots))` by
    (simp[MEM_FILTER, MEM_MAP] >> metis_tac[pairTheory.SND]) >>
  gvs[EVERY_MEM]
QED

Theorem current_collapsed_selected_name:
  i.inst_opcode = PHI /\ i.inst_outputs = [x] /\
  i.inst_operands = current_phi_slots slots /\
  (simplify_current_phi i).inst_opcode = ASSIGN /\
  (simplify_current_phi i).inst_operands = [Var y] /\
  resolve_phi p i.inst_operands = SOME (Var n) ==>
  x <> y /\ (n = x \/ n = y)
Proof
  strip_tac >> drule_all current_collapsed_slot_names >> strip_tac >>
  gvs[current_resolve_phi_slots, optionTheory.OPTION_MAP_EQ_SOME] >>
  drule FIND_MEM >> strip_tac >>
  PairCases_on `z` >> gvs[] >> metis_tac[]
QED

Theorem current_certificate_collapsed_exit_names:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM ev events /\ fn_cfg_edge fn (current_event_label ev) h /\
  ps = (case ALOOKUP (current_pred_map fn) h of NONE => [] | SOME ps0 => ps0) /\
  i.inst_opcode = PHI /\ i.inst_outputs = [x] /\
  i.inst_operands =
    FOLDL (\ops ev. current_event_operand_action (current_succ_map fn) h ev ops)
      (current_phi_slots (MAP (\p. (p,v)) ps)) events /\
  (simplify_current_phi i).inst_opcode = ASSIGN /\
  (simplify_current_phi i).inst_operands = [Var y] ==>
  x <> y /\
  (latest_current_name (current_event_exit_rs ev) v = x \/
   latest_current_name (current_event_exit_rs ev) v = y)
Proof
  strip_tac >>
  `current_event_label ev = current_event_label ev` by simp[] >>
  drule_all current_certificate_inserted_edge_resolve >> strip_tac >>
  `i.inst_operands = current_phi_slots
    (MAP (\slot. FOLDL (\slot ev.
      current_event_pair_action (current_succ_map fn) h ev slot) slot events)
      (MAP (\p. (p,v)) ps))` by simp[current_event_fold_slots] >>
  irule current_collapsed_selected_name >>
  qexistsl_tac [`i`, `current_event_label ev`,
    `MAP (\slot. FOLDL (\slot ev.
      current_event_pair_action (current_succ_map fn) h ev slot) slot events)
      (MAP (\p. (p,v)) ps)`] >>
  simp[GSYM current_event_fold_slots] >>
  qpat_x_assum `!v. resolve_phi _ _ = _` (qspec_then `v` mp_tac) >>
  simp[]
QED

Theorem current_certificate_inserted_exit_token_name:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ first_block_no_preds fn /\
  entry_block fn = SOME eb /\ current_actual_inserted fn v h /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\ MEM ev events ==>
  current_token_name H (current_event_exit_env ev v) =
    SOME (latest_current_name (current_event_exit_rs ev) v)
Proof
  strip_tac >> drule_all current_certificate_events_valid >> strip_tac >>
  `MEM h (fn_labels fn)` by metis_tac[current_actual_inserted_support] >>
  `?old. lookup_block h fn.fn_blocks = SOME old` by
    (gvs[fn_labels_def, MEM_MAP] >>
     `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
       gvs[wf_function_def, fn_labels_def] >> metis_tac[MEM_lookup_block]) >>
  drule_all current_certificate_inserted_prefix >> strip_tac >>
  drule_all current_certificate_event_at >> strip_tac >>
  `MEM (CurrentInserted v h,v) (FLAT (A h))` by
    (simp[current_block_annotations_def, FLAT_APPEND] >>
     metis_tac[current_inserted_annotation_member, lookup_block_label]) >>
  `MEM v V` by
    (`current_event_valid A V ev'` by metis_tac[EVERY_MEM] >>
     drule current_event_annotation_owner_covered >> simp[] >>
     disch_then (qspecl_then [`v`, `CurrentInserted v h`] mp_tac) >> gvs[]) >>
  irule (cj 2 current_event_names_accessors) >>
  metis_tac[EVERY_MEM]
QED

Theorem current_certificate_collapsed_origin:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ first_block_no_preds fn /\
  entry_block fn = SOME eb /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  current_actual_inserted fn v h /\
  current_token_name H (CurrentInserted v h) = SOME x /\
  ps = (case ALOOKUP (current_pred_map fn) h of NONE => [] | SOME ps0 => ps0) /\
  i.inst_opcode = PHI /\ i.inst_outputs = [x] /\
  i.inst_operands =
    FOLDL (\ops ev. current_event_operand_action (current_succ_map fn) h ev ops)
      (current_phi_slots (MAP (\p. (p,v)) ps)) events /\
  (simplify_current_phi i).inst_opcode = ASSIGN /\
  (simplify_current_phi i).inst_operands = [Var y] ==>
  x <> y /\ ?t ev.
    MEM ev events /\ fn_cfg_edge fn (current_event_label ev) h /\
    current_event_exit_env ev v = t /\
    t <> CurrentDefault v /\ t <> CurrentInserted v h /\
    current_token_name H t = SOME y
Proof
  strip_tac >>
  drule_all current_certificate_inserted_exit_seed >> strip_tac >>
  drule_all current_certificate_collapsed_exit_names >> strip_tac >>
  drule_all current_certificate_inserted_exit_token_name >> strip_tac >>
  drule_all current_certificate_events_valid >> strip_tac >>
  drule_all current_certificate_static_env >> strip_tac >>
  `latest_current_name (current_event_exit_rs ev) v <> x` by
    (qpat_assum `!v. current_event_exit_env ev v = _` (fn th => fs[th]) >>
     drule_all current_exit_name_alias_residual >> simp[]) >>
  conj_tac >- simp[] >>
  qexistsl_tac [`current_event_exit_env ev v`, `ev`] >> gvs[]
QED

Theorem current_certificate_exit_default_owner:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  MEM ev events /\ current_event_exit_env ev v = CurrentDefault w ==> w = v
Proof
  strip_tac >> drule_all current_certificate_static_env >> strip_tac >>
  qpat_assum `!v. current_event_exit_env ev v = _` (fn th => fs[th]) >>
  metis_tac[current_exit_default_owner]
QED

Theorem current_certificate_collapsed_origin_unique:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM ev events /\ current_event_exit_env ev v = t /\ t <> CurrentDefault v /\
  current_token_name H t = SOME y /\ (!w. u <> CurrentDefault w) /\
  current_token_name H u = SOME y ==> u = t
Proof
  strip_tac >> drule_all current_certificate_events_valid >> strip_tac >>
  `!w. t <> CurrentDefault w` by
    metis_tac[current_certificate_exit_default_owner] >>
  irule current_allocated_name_injective >> metis_tac[]
QED

Theorem current_certificate_collapsed_predecessor_tokens:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ first_block_no_preds fn /\
  entry_block fn = SOME eb /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  current_actual_inserted fn v h /\
  current_token_name H (CurrentInserted v h) = SOME x /\
  ps = (case ALOOKUP (current_pred_map fn) h of NONE => [] | SOME ps0 => ps0) /\
  i.inst_opcode = PHI /\ i.inst_outputs = [x] /\
  i.inst_operands =
    FOLDL (\ops ev. current_event_operand_action (current_succ_map fn) h ev ops)
      (current_phi_slots (MAP (\p. (p,v)) ps)) events /\
  (simplify_current_phi i).inst_opcode = ASSIGN /\
  (simplify_current_phi i).inst_operands = [Var y] /\
  MEM ev events /\ current_event_exit_env ev v = t /\ t <> CurrentDefault v /\
  current_token_name H t = SOME y /\
  MEM ep events /\ fn_cfg_edge fn (current_event_label ep) h ==>
  (current_event_exit_env ep v = CurrentInserted v h \/
   current_event_exit_env ep v = t \/
   current_event_exit_env ep v = CurrentDefault v) /\
  (current_event_exit_env ep v = CurrentDefault v ==> v = x \/ v = y)
Proof
  strip_tac >>
  `current_token_name H (current_event_exit_env ep v) =
    SOME (latest_current_name (current_event_exit_rs ep) v)` by
    (irule current_certificate_inserted_exit_token_name >> metis_tac[]) >>
  drule_all current_certificate_collapsed_exit_names >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `current_event_exit_env ep v = CurrentDefault v`
  >- (gvs[current_token_name_def]) >>
  `!w. current_event_exit_env ep v <> CurrentDefault w` by
    metis_tac[current_certificate_exit_default_owner] >>
  `!w. t <> CurrentDefault w` by
    metis_tac[current_certificate_exit_default_owner] >>
  drule_all current_certificate_events_valid >> strip_tac >>
  `current_event_exit_env ep v = CurrentInserted v h \/
   current_event_exit_env ep v = t` by
    (Cases_on `latest_current_name (current_event_exit_rs ep) v = x`
     >- (disj1_tac >> irule current_allocated_name_injective >> simp[] >> metis_tac[]) >>
     disj2_tac >> irule current_allocated_name_injective >> metis_tac[]) >>
  simp[]
QED
