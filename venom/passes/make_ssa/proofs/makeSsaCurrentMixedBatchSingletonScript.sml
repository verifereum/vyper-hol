Theory makeSsaCurrentMixedBatchSingleton
Ancestors makeSsaCurrentRetainedProjection makeSsaCurrentInsertedSeparation
  makeSsaCurrentMixedBatchWrites makeSsaCurrentPhaseShape
  makeSsaCurrentReinsertionOrder makeSsaCurrentCleanupShape
  makeSsaCurrentCleanupBoundary makeSsaCurrentDefs livenessDefs venomInst list
  makeSsaCurrentOriginalFinalSlots makeSsaCurrentAllocation cfgHelpers venomWf venomExecProps
  makeSsaCurrentReinsertionSlots makeSsaCurrentReinsertionNames
  makeSsaCurrentSemanticHistory alist venomExecSemantics
  makeSsaCurrentValueInvariant venomState

Theorem current_collect_phis_no_id:
  !xs. collect_phis (MAP current_inst_no_id xs) =
    MAP current_inst_no_id (collect_phis xs)
Proof
  Induct >> simp[collect_phis_def, current_inst_no_id_def] >>
  Cases_on `h.inst_opcode = PHI` >> simp[current_inst_no_id_def]
QED

Theorem current_collect_phis_split:
  !pre tail. EVERY (\i. i.inst_opcode = PHI) pre /\
    (tail = [] \/ (HD tail).inst_opcode <> PHI) ==>
    collect_phis (pre ++ tail) = pre
Proof
  Induct >> simp[collect_phis_def] >> rpt strip_tac
  >- (Cases_on `tail` >> gvs[collect_phis_def]) >>
  simp[collect_phis_def] >> metis_tac[]
QED

Theorem current_cleanup_leading_no_id:
  EVERY (\i. i.inst_opcode = PHI) pre /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) ==>
  MAP current_inst_no_id (collect_phis (simplify_current_phi_prefix (pre ++ tail))) =
  MAP current_inst_no_id
    (FILTER (\i. i.inst_opcode = PHI) (MAP simplify_current_phi pre))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all current_cleanup_partition >> strip_tac >>
  `LENGTH (MAP instruction_inst_id (pre ++ tail)) =
    LENGTH (FILTER (\i. i.inst_opcode = PHI) (MAP simplify_current_phi pre) ++
      FILTER (\i. i.inst_opcode <> PHI) (MAP simplify_current_phi pre) ++ tail)` by
    (simp[] >> qspec_then `MAP simplify_current_phi pre` mp_tac
      current_cleanup_partition_length >> simp[]) >>
  `MAP current_inst_no_id (simplify_current_phi_prefix (pre ++ tail)) =
    MAP current_inst_no_id
      (FILTER (\i. i.inst_opcode = PHI) (MAP simplify_current_phi pre) ++
       FILTER (\i. i.inst_opcode <> PHI) (MAP simplify_current_phi pre) ++ tail)` by
    (pure_rewrite_tac[simplify_current_phi_prefix_def] >>
     asm_rewrite_tac[] >> simp_tac std_ss [LET_THM] >>
     pure_rewrite_tac[GSYM MAP_APPEND, APPEND_ASSOC] >>
     irule current_reassign_no_id >> gvs[] >> decide_tac) >>
  qpat_x_assum `MAP current_inst_no_id _ = _`
    (mp_tac o Q.AP_TERM `collect_phis`) >>
  rewrite_tac[current_collect_phis_no_id] >>
  `collect_phis
      (FILTER (\i. i.inst_opcode = PHI) (MAP simplify_current_phi pre) ++
       FILTER (\i. i.inst_opcode <> PHI) (MAP simplify_current_phi pre) ++ tail) =
    FILTER (\i. i.inst_opcode = PHI) (MAP simplify_current_phi pre)` suffices_by simp[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  irule current_collect_phis_split >> simp[EVERY_FILTER] >>
  Cases_on `FILTER (\i. i.inst_opcode <> PHI) (MAP simplify_current_phi pre)` >>
  gvs[] >>
  `EVERY (\i. i.inst_opcode <> PHI)
    (FILTER (\i. i.inst_opcode <> PHI) (MAP simplify_current_phi pre))` by
    simp[EVERY_FILTER] >> gvs[]
QED

Theorem current_simplify_phi_still_phi:
  (simplify_current_phi inst).inst_opcode = PHI ==>
  simplify_current_phi inst = inst
Proof
  simp[simplify_current_phi_def, keep_current_phi_vars_def] >>
  IF_CASES_TAC >> simp[] >>
  simp[simplify_current_phi_raw_def] >>
  Cases_on `inst.inst_opcode = PHI` >> simp[] >>
  Cases_on `current_phi_output inst.inst_outputs` >> simp[] >>
  Cases_on `current_phi_values (remove_current_phi_self x inst.inst_operands)` >> simp[] >>
  Cases_on `x'` >> simp[] >> IF_CASES_TAC >> simp[]
QED

Theorem current_cleanup_leading_inverse:
  EVERY (\i. i.inst_opcode = PHI) pre /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\
  MEM inst (collect_phis (simplify_current_phi_prefix (pre ++ tail))) ==>
  ?original. MEM original pre /\
    current_inst_no_id inst = current_inst_no_id original
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all current_cleanup_leading_no_id >> strip_tac >>
  `MEM (current_inst_no_id inst)
    (MAP current_inst_no_id
      (collect_phis (simplify_current_phi_prefix (pre ++ tail))))` by
    (simp[MEM_MAP] >> metis_tac[]) >>
  qpat_x_assum `MAP _ _ = _` (fn th => fs[th]) >>
  gvs[MEM_MAP, MEM_FILTER] >>
  drule current_simplify_phi_still_phi >> strip_tac >>
  metis_tac[]
QED

Theorem current_singleton_original_phi_inverse:
  current_history_valid U H /\ wf_function fn /\
  lookup_block h fn.fn_blocks = SOME old /\
  i < LENGTH old.bb_instructions /\
  (EL i old.bb_instructions).inst_outputs = [dst] /\
  current_token_name H (CurrentOriginal h i 0) = SOME n /\
  MEM (v,n) (current_instruction_singleton_table fn H) ==> dst = v
Proof
  strip_tac >> drule current_singleton_member_final_site >> strip_tac >>
  `CurrentOriginal h i 0 = CurrentOriginal (EL b fn.fn_blocks).bb_label i' j` by
    (irule current_allocated_name_injective >> simp[] >> metis_tac[]) >>
  gvs[] >>
  `old = EL b fn.fn_blocks` by
    (`lookup_block (EL b fn.fn_blocks).bb_label fn.fn_blocks =
        SOME (EL b fn.fn_blocks)` by
       (irule MEM_lookup_block >>
        fs[wf_function_def, fn_labels_def] >> metis_tac[EL_MEM]) >>
     metis_tac[optionTheory.SOME_11]) >>
  gvs[]
QED

Theorem current_cleanup_block_leading_inverse:
  bb.bb_instructions = pre ++ tail /\
  EVERY (\i. i.inst_opcode = PHI) pre /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\
  MEM inst (collect_phis (simplify_current_phi_block bb).bb_instructions) ==>
  ?original. MEM original pre /\
    current_inst_no_id inst = current_inst_no_id original
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `pre`
  >- (Cases_on `tail` >> gvs[simplify_current_phi_block_def, collect_phis_def]) >>
  `MEM inst (collect_phis (simplify_current_phi_prefix ((h::t) ++ tail)))` by
    gvs[simplify_current_phi_block_def] >>
  drule current_cleanup_leading_inverse >>
  disch_then (qspecl_then [`tail`, `inst`] mp_tac) >> simp[] >> metis_tac[]
QED

Theorem current_cleanup_if_leading_inverse:
  lookup_block h bbs = SOME bb /\
  bb.bb_instructions = pre ++ tail /\
  EVERY (\i. i.inst_opcode = PHI) pre /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\
  lookup_block h (simplify_current_phis_if enabled bbs) = SOME out /\
  MEM inst (collect_phis out.bb_instructions) ==>
  ?original. MEM original pre /\
    current_inst_no_id inst = current_inst_no_id original
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  gvs[current_cleanup_if_lookup] >> Cases_on `enabled` >> gvs[]
  >- (irule current_cleanup_block_leading_inverse >> metis_tac[]) >>
  `collect_phis (pre ++ tail) = pre` by
    (irule current_collect_phis_split >> metis_tac[]) >>
  gvs[] >> metis_tac[]
QED

Theorem current_certificate_leading_canonical_inverse:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  lookup_block h fn.fn_blocks = SOME old /\ old.bb_instructions = phis ++ tail /\
  EVERY (\j. j.inst_opcode = PHI) phis /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\
  lookup_block h fn'.fn_blocks = SOME out /\
  MEM inst (collect_phis out.bb_instructions) /\ MEM n inst.inst_outputs /\
  MEM (v,n) (current_instruction_singleton_table fn H) ==>
  ?i. i < LENGTH phis /\ (EL i phis).inst_outputs = [v]
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all current_certificate_block_replay >> strip_tac >>
  `EVERY (\i. i.inst_opcode = PHI) pre` by
    (gvs[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >>
     simp[build_phi_inst_supply_def] >> rpt strip_tac >> gvs[]) >>
  `?pp tt. final.bb_instructions = pp ++ tt /\
    LENGTH pp = LENGTH pre + LENGTH phis /\ LENGTH tt = LENGTH tail /\
    EVERY (\i. i.inst_opcode = PHI) pp /\
    (tt = [] \/ (HD tt).inst_opcode <> PHI)` by
    (`current_phi_view final.bb_instructions =
       FOLDL (\view ev. current_event_slot_action (current_succ_map fn) h ev view)
         (current_phi_view ((pre ++ phis) ++ tail)) events` by
       gvs[APPEND_ASSOC] >>
     drule current_replay_phase_split >> simp[EVERY_APPEND] >>
     disch_then (qspec_then `tail` mp_tac) >> simp[] >> metis_tac[]) >>
  `?original. MEM original pp /\ current_inst_no_id inst = current_inst_no_id original` by
    (irule current_cleanup_if_leading_inverse >> metis_tac[]) >>
  `?k. k < LENGTH pp /\ original = EL k pp` by metis_tac[MEM_EL] >>
  `k < LENGTH final.bb_instructions /\
   MEM n (EL k final.bb_instructions).inst_outputs` by
    (gvs[current_inst_no_id_def, instruction_component_equality] >>
     simp[EL_APPEND_EQN]) >>
  (Cases_on `k < LENGTH pre`
  >- (`?dst. (EL k pre).inst_outputs = [dst]` by
        (qpat_x_assum `EVERY (\inst. ?id v. _) pre`
           (mp_tac o REWRITE_RULE [EVERY_EL]) >>
         disch_then (qspec_then `k` mp_tac) >> simp[build_phi_inst_supply_def] >>
         strip_tac >> gvs[]) >>
      qpat_x_assum `!k v. k < LENGTH pre /\ _ ==> _`
        (qspecl_then [`k`, `dst`] mp_tac) >> simp[] >> strip_tac >>
      `n' = n` by gvs[] >>
      drule_all current_certificate_inserted_singleton_separate >> simp[]) >>
  `?i. k = LENGTH pre + i /\ i < LENGTH phis` by
    (qexists_tac `k - LENGTH pre` >> decide_tac) >>
  `i < LENGTH old.bb_instructions /\
   (EL i old.bb_instructions).inst_opcode = PHI` by
    (simp[EL_APPEND_EQN] >> fs[EVERY_EL]) >>
  `inst_wf (EL i old.bb_instructions)` by
    (fs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[lookup_block_MEM, EL_MEM]) >>
  `?dst. (EL i old.bb_instructions).inst_outputs = [dst]` by
    (qpat_x_assum `inst_wf _` mp_tac >>
     simp[inst_wf_def, listTheory.LENGTH_EQ_NUM_compute] >> metis_tac[]) >>
  qpat_x_assum `!i v. i < LENGTH old.bb_instructions /\ _ ==> _`
    (qspecl_then [`i`, `dst`] mp_tac) >> simp[] >> strip_tac >>
  `src = n` by gvs[] >>
  drule_all current_certificate_events_valid >> strip_tac >>
  `dst = v` by (irule current_singleton_original_phi_inverse >> metis_tac[]) >>
  qexists_tac `i` >> gvs[EL_APPEND_EQN])
QED

Theorem current_phi_pairs_member_index:
  LIST_REL (\inst dv. eval_one_phi st inst = SOME dv) phis pairs /\
  MEM dv pairs ==>
  ?i. i < LENGTH phis /\ eval_one_phi st (EL i phis) = SOME dv
Proof
  simp[MEM_EL, LIST_REL_EL_EQN] >> metis_tac[]
QED

Theorem current_phi_pairs_index_member:
  LIST_REL (\inst dv. eval_one_phi st inst = SOME dv) phis pairs /\
  i < LENGTH phis /\ eval_one_phi st (EL i phis) = SOME dv ==> MEM dv pairs
Proof
  simp[LIST_REL_EL_EQN] >> rpt strip_tac >>
  `dv = EL i pairs` by metis_tac[optionTheory.SOME_11] >>
  metis_tac[EL_MEM]
QED

Theorem current_eval_one_phi_exact_output:
  eval_one_phi st inst = SOME (v,value) ==> inst.inst_outputs = [v]
Proof
  simp[eval_one_phi_def] >> strip_tac >> gvs[AllCaseEqs()]
QED

Theorem current_phi_pairs_only_lookup:
  LIST_REL (\inst dv. eval_one_phi st inst = SOME dv) phis pairs /\
  r < LENGTH phis /\ eval_one_phi st (EL r phis) = SOME (n,value) /\
  (!q. q < LENGTH phis /\ MEM n (EL q phis).inst_outputs ==> q = r) ==>
  ALOOKUP pairs n = SOME value
Proof
  rpt strip_tac >>
  `MEM (n,value) pairs` by metis_tac[current_phi_pairs_index_member] >>
  Cases_on `ALOOKUP pairs n`
  >- (fs[ALOOKUP_FAILS] >> metis_tac[MEM_MAP, pairTheory.FST]) >>
  drule ALOOKUP_MEM >> strip_tac >>
  drule_all current_phi_pairs_member_index >> strip_tac >>
  `MEM n (EL i phis).inst_outputs` by
    (drule current_eval_one_phi_output >> simp[]) >>
  `i = r` by metis_tac[] >> gvs[]
QED

Theorem current_maximal_phi_prefix_bound:
  insts = phis ++ tail /\ (tail = [] \/ (HD tail).inst_opcode <> PHI) /\
  batch <= LENGTH insts /\ EVERY (\j. j.inst_opcode = PHI) (TAKE batch insts) ==>
  batch <= LENGTH phis
Proof
  rpt strip_tac >> Cases_on `tail = []` >- gvs[] >>
  Cases_on `batch <= LENGTH phis` >> simp[] >>
  `LENGTH phis < LENGTH (TAKE batch insts)` by simp[] >>
  `((EL (LENGTH phis) insts).inst_opcode = PHI)` by
    (qpat_x_assum `EVERY _ _` (mp_tac o REWRITE_RULE [EVERY_EL]) >>
     disch_then (qspec_then `LENGTH phis` mp_tac) >>
     simp[EL_TAKE]) >>
  Cases_on `tail` >> gvs[EL_APPEND_EQN]
QED

Theorem current_certificate_mixed_batch_singleton:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  first_block_no_preds fn /\ blocks_have_leading_phi fn.fn_blocks /\
  fn_defs_reach_uses fn /\ fn_phi_operands_single_def fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\ fn_phis_non_degenerate fn /\
  fn_phi_outputs_single_def fn /\
  lookup_block h fn.fn_blocks = SOME old /\ old.bb_instructions = phis ++ tail /\
  EVERY (\j. j.inst_opcode = PHI) phis /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\
  MEM ev events /\ current_event_label ev = p /\ fn_cfg_edge fn p h /\
  lookup_block p fn.fn_blocks = SOME pred /\
  st.vs_prev_bb = SOME p /\ st'.vs_prev_bb = SOME p /\
  current_singleton_agree (current_instruction_singleton_table fn H) st st' /\
  lookup_block h fn'.fn_blocks = SOME out /\
  out.bb_instructions = target_phis ++ target_tail /\
  EVERY (\j. j.inst_opcode = PHI) target_phis /\
  (target_tail = [] \/ (HD target_tail).inst_opcode <> PHI) /\
  eval_phis st phis = OK post /\ eval_phis st' target_phis = OK post' ==>
  current_singleton_agree (current_instruction_singleton_table fn H) post post'
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?pairs. LIST_REL (\inst dv. eval_one_phi st inst = SOME dv) phis pairs /\
    post.vs_vars = FOLDL (\m dv. m |+ dv) st.vs_vars (REVERSE pairs)` by
    (irule current_eval_phis_witness >> metis_tac[]) >>
  `?pairs'. LIST_REL (\inst dv. eval_one_phi st' inst = SOME dv) target_phis pairs' /\
    post'.vs_vars = FOLDL (\m dv. m |+ dv) st'.vs_vars (REVERSE pairs')` by
    (irule current_eval_phis_witness >> metis_tac[]) >>
  `!v n. MEM (v,n) (current_instruction_singleton_table fn H) ==>
    ALOOKUP pairs v = ALOOKUP pairs' n` by
    (rpt strip_tac >> Cases_on `ALOOKUP pairs v`
     >- suspend "absent"
     >> suspend "present") >>
  drule_all current_singleton_agree_mixed_reverse_pairs >>
  simp[current_singleton_agree_def, lookup_var_def]
QED

Resume current_certificate_mixed_batch_singleton[present]:
  drule ALOOKUP_MEM >> strip_tac >>
  drule_all current_phi_pairs_member_index >> strip_tac >>
  `i < LENGTH old.bb_instructions /\
   eval_one_phi st (EL i old.bb_instructions) = SOME (v,x) /\
   (EL i old.bb_instructions).inst_opcode = PHI` by
    (simp[EL_APPEND_EQN] >> fs[EVERY_EL]) >>
  drule_all current_certificate_retained_projected_eval >> strip_tac >>
  `out' = out` by metis_tac[optionTheory.SOME_11] >> gvs[] >>
  `batch <= LENGTH target_phis` by
    (irule current_maximal_phi_prefix_bound >>
     qexistsl_tac [`target_phis ++ target_tail`, `target_tail`] >> simp[] >> metis_tac[]) >>
  `r < LENGTH target_phis` by decide_tac >>
  `eval_one_phi st' (EL r target_phis) = SOME (n,x)` by
    (qpat_x_assum `eval_one_phi st' _ = SOME (n,x)` mp_tac >> simp[EL_APPEND_EQN]) >>
  sym_tac >> irule current_phi_pairs_only_lookup >>
  qexistsl_tac [`target_phis`, `r`, `st'`] >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> simp[EL_APPEND_EQN]
QED

Resume current_certificate_mixed_batch_singleton[absent]:
  Cases_on `ALOOKUP pairs' n` >> simp[] >>
  drule ALOOKUP_MEM >> strip_tac >>
  drule_all current_phi_pairs_member_index >> strip_tac >>
  `MEM (EL i target_phis) (collect_phis out.bb_instructions)` by
    (drule_all current_collect_phis_split >> strip_tac >> gvs[] >> metis_tac[EL_MEM]) >>
  `MEM n (EL i target_phis).inst_outputs` by
    (drule current_eval_one_phi_output >> simp[]) >>
  drule_all current_certificate_leading_canonical_inverse >> strip_tac >>
  `eval_one_phi st (EL i' phis) = SOME (EL i' pairs)` by
    (qpat_x_assum `LIST_REL _ phis pairs` (mp_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
     metis_tac[]) >>
  `MEM (FST (EL i' pairs)) (EL i' phis).inst_outputs` by
    metis_tac[current_eval_one_phi_output] >>
  `FST (EL i' pairs) = v` by gvs[] >>
  `MEM v (MAP FST pairs)` by
    (simp[MEM_MAP] >> qexists_tac `EL i' pairs` >> simp[] >>
     metis_tac[LIST_REL_LENGTH, EL_MEM]) >>
  fs[ALOOKUP_FAILS, MEM_MAP] >>
  PairCases_on `y` >> gvs[] >> metis_tac[]
QED

Finalise current_certificate_mixed_batch_singleton
