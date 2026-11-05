Theory makeSsaCurrentMixedBatchReady
Ancestors makeSsaCurrentMixedBatchSingleton makeSsaCurrentInsertedValue
  makeSsaCurrentRetainedNonclobber makeSsaCurrentBatchWrites
  makeSsaCurrentPhaseShape makeSsaCurrentReinsertionSlots
  makeSsaCurrentReinsertionNames makeSsaCurrentCleanupShape
  makeSsaCurrentCleanupBoundary makeSsaCurrentDefs livenessDefs venomInst list
  venomWf venomExecSemantics venomExecProps cfgHelpers makeSsaCurrentValueInvariant
  makeSsaCurrentFinalSlots makeSsaCurrentEdgeTrace
  makeSsaCurrentRetainedValue makeSsaCurrentRetainedProjection
  makeSsaCurrentSemanticHistory makeSsaCurrentSimDefs venomState finite_map

Theorem current_eval_one_phi_no_id:
  current_inst_no_id a = current_inst_no_id b ==>
  eval_one_phi st a = eval_one_phi st b
Proof
  simp[current_inst_no_id_def, instruction_component_equality, eval_one_phi_def]
QED

Theorem current_phi_slots_well_formed:
  !slots. phi_well_formed (current_phi_slots slots)
Proof
  Induct >> simp[current_phi_slots_def, phi_well_formed_def] >>
  gen_tac >> PairCases_on `h` >> fs[current_phi_slots_def, phi_well_formed_def]
QED

Theorem current_event_fold_phi_well_formed:
  phi_well_formed ops ==>
  phi_well_formed (FOLDL (\ops ev. current_event_operand_action sm h ev ops) ops events)
Proof
  strip_tac >> drule current_wf_phi_slots >> disch_then SUBST1_TAC >>
  simp[current_event_fold_slots, current_phi_slots_well_formed]
QED

Theorem current_certificate_leading_slot:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  lookup_block h fn.fn_blocks = SOME old /\ old.bb_instructions = phis ++ tail /\
  EVERY (\j. j.inst_opcode = PHI) phis /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\
  lookup_block h fn'.fn_blocks = SOME out /\
  MEM inst (collect_phis out.bb_instructions) ==>
  (?v n. current_actual_inserted fn v h /\
    current_token_name H (CurrentInserted v h) = SOME n /\
    inst.inst_outputs = [n] /\ inst.inst_opcode = PHI /\
    inst.inst_operands =
      FOLDL (\ops ev. current_event_operand_action (current_succ_map fn) h ev ops)
        (current_phi_slots (MAP (\p. (p,v))
          (case ALOOKUP (current_pred_map fn) h of NONE => [] | SOME ps => ps))) events) \/
  (?i dst n. i < LENGTH phis /\ (EL i old.bb_instructions).inst_outputs = [dst] /\
    current_token_name H (CurrentOriginal h i 0) = SOME n /\
    inst.inst_outputs = [n] /\ inst.inst_opcode = PHI /\
    inst.inst_operands =
      FOLDL (\ops ev. current_event_operand_action (current_succ_map fn) h ev ops)
        (EL i old.bb_instructions).inst_operands events)
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
         (current_phi_view ((pre ++ phis) ++ tail)) events` by gvs[APPEND_ASSOC] >>
     drule current_replay_phase_split >> simp[EVERY_APPEND] >>
     disch_then (qspec_then `tail` mp_tac) >> simp[] >> metis_tac[]) >>
  `?original. MEM original pp /\ current_inst_no_id inst = current_inst_no_id original` by
    (irule current_cleanup_if_leading_inverse >> metis_tac[]) >>
  `?k. k < LENGTH pp /\ original = EL k pp` by metis_tac[MEM_EL] >>
  `k < LENGTH final.bb_instructions /\
    current_inst_no_id inst = current_inst_no_id (EL k final.bb_instructions)` by
    (gvs[] >> simp[EL_APPEND_EQN]) >>
  (Cases_on `k < LENGTH pre`
  >- (disj1_tac >>
    `?id v. EL k pre = build_phi_inst_supply id v
      (case ALOOKUP (current_pred_map fn) h of NONE => [] | SOME ps => ps)` by
      (qpat_x_assum `EVERY (\inst. ?id v. _) pre`
         (mp_tac o REWRITE_RULE [EVERY_EL]) >>
       disch_then (qspec_then `k` mp_tac) >> simp[]) >>
    `current_actual_inserted fn v h` by
      (qpat_x_assum `!v. current_actual_inserted _ _ _ <=> _`
         (qspec_then `v` mp_tac) >>
       strip_tac >> first_x_assum (irule o iffRL) >>
       qexists_tac `EL k pre` >> simp[EL_MEM, build_phi_inst_supply_def]) >>
    qpat_x_assum `!k v. k < LENGTH pre /\ _ ==> _`
      (qspecl_then [`k`, `v`] mp_tac) >> simp[build_phi_inst_supply_def] >> strip_tac >>
    `k < LENGTH (pre ++ old.bb_instructions) /\
      (EL k (pre ++ old.bb_instructions)).inst_opcode = PHI` by
      simp[EL_APPEND_EQN, build_phi_inst_supply_def] >>
    drule_all current_phi_view_fold_instruction >> strip_tac >>
    qexistsl_tac [`v`, `n`] >>
    gvs[current_inst_no_id_def, instruction_component_equality,
        EL_APPEND_EQN, build_phi_inst_supply_def] >>
    simp[current_phi_slots_def, MAP_MAP_o, combinTheory.o_DEF] >>
    metis_tac[EL_MEM]) >>
  disj2_tac >>
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
  `k < LENGTH (pre ++ old.bb_instructions) /\
   (EL k (pre ++ old.bb_instructions)).inst_opcode = PHI` by
    (simp[EL_APPEND_EQN] >> fs[EVERY_EL]) >>
  drule_all current_phi_view_fold_instruction >> strip_tac >>
  qexistsl_tac [`i`, `dst`, `src`] >>
  gvs[current_inst_no_id_def, instruction_component_equality, EL_APPEND_EQN])
QED

Theorem current_phi_batch_ready:
  !phis. EVERY (\inst. inst.inst_opcode = PHI) phis /\
    EVERY (\inst. ?dv. eval_one_phi before inst = SOME dv) phis ==>
    ?after. eval_phis before phis = OK after
Proof
  Induct >> simp[eval_phis_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >> PairCases_on `dv` >>
  simp[eval_phis_def]
QED

Theorem current_certificate_mixed_batch_ready:
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
  eval_phis st phis = OK post /\
  (!v n. current_actual_inserted fn v h /\
    current_token_name H (CurrentInserted v h) = SOME n /\
    MEM n (FLAT (MAP (\j. j.inst_outputs) target_phis)) ==>
    current_name_agree (current_event_exit_rs ev) [v] st st' /\
    ?value. lookup_var v st = SOME value) ==>
  ?post'. eval_phis st' target_phis = OK post' /\
    current_singleton_agree (current_instruction_singleton_table fn H) post post'
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `collect_phis out.bb_instructions = target_phis` by
    (asm_rewrite_tac[] >> irule current_collect_phis_split >> metis_tac[]) >>
  `EVERY (\inst. ?dv. eval_one_phi st' inst = SOME dv) target_phis` by
    (rewrite_tac[EVERY_MEM] >> qx_gen_tac `inst` >> strip_tac >>
     `MEM inst (collect_phis out.bb_instructions)` by metis_tac[] >>
     drule_all current_certificate_leading_slot >> strip_tac
     >- suspend "inserted"
     >> suspend "original") >>
  `?post'. eval_phis st' target_phis = OK post'` by
    (irule current_phi_batch_ready >> metis_tac[]) >>
  qexists_tac `post'` >> simp[] >>
  irule current_certificate_mixed_batch_singleton >> metis_tac[]
QED

Resume current_certificate_mixed_batch_ready[inserted]:
  `MEM n (FLAT (MAP (\j. j.inst_outputs) target_phis))` by
    (simp[MEM_FLAT, MEM_MAP] >> metis_tac[MEM]) >>
  qpat_x_assum `!v n. current_actual_inserted _ _ _ /\ _ ==> _`
    (qspecl_then [`v`, `n`] mp_tac) >> simp[] >> strip_tac >>
  `resolve_phi p inst.inst_operands =
    SOME (Var (latest_current_name (current_event_exit_rs ev) v))` by
    (asm_rewrite_tac[] >> irule current_certificate_inserted_edge_resolve >> metis_tac[]) >>
  `lookup_var (latest_current_name (current_event_exit_rs ev) v) st' = SOME value` by
    fs[current_name_agree_def] >>
  qexists_tac `(n,value)` >>
  gvs[eval_one_phi_def, eval_operand_def]
QED

Resume current_certificate_mixed_batch_ready[original]:
  `?pairs. LIST_REL (\inst dv. eval_one_phi st inst = SOME dv) phis pairs /\
    post.vs_vars = FOLDL (\m dv. m |+ dv) st.vs_vars (REVERSE pairs)` by
    (irule current_eval_phis_witness >> metis_tac[]) >>
  `?value. eval_one_phi st (EL i old.bb_instructions) = SOME (dst,value)` by
    (qpat_x_assum `LIST_REL _ _ _` (mp_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
     strip_tac >> first_x_assum (qspec_then `i` mp_tac) >>
     simp[EL_APPEND_EQN] >> strip_tac >>
     Cases_on `EL i pairs` >>
     drule current_eval_one_phi_exact_output >> strip_tac >>
     gvs[EL_APPEND_EQN]) >>
  `(EL i old.bb_instructions).inst_opcode = PHI` by
    (simp[EL_APPEND_EQN] >> fs[EVERY_EL]) >>
  drule_all current_certificate_retained_eval >> strip_tac >>
  `out' = out /\ name = n` by metis_tac[optionTheory.SOME_11] >> gvs[] >>
  `?q. q < LENGTH out.bb_instructions /\ inst = EL q out.bb_instructions` by
    (metis_tac[MEM_EL, MEM_APPEND]) >>
  `ALL_DISTINCT (FLAT (MAP (\j. j.inst_outputs) out.bb_instructions))` by
    (irule current_certificate_block_outputs_distinct >> metis_tac[]) >>
  `q = r` by
    (irule current_distinct_flat_output_index >> qexistsl_tac [`out.bb_instructions`, `n`] >>
     conj_tac >- (asm_rewrite_tac[]) >>
     conj_tac >- decide_tac >>
     conj_tac >- (asm_rewrite_tac[] >> simp[] >> decide_tac) >>
     conj_tac >- metis_tac[MEM] >> asm_rewrite_tac[] >> simp[]) >>
  metis_tac[]
QED

Finalise current_certificate_mixed_batch_ready

Theorem current_certificate_leading_phi_wf:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  lookup_block h fn.fn_blocks = SOME old /\ old.bb_instructions = phis ++ tail /\
  EVERY (\j. j.inst_opcode = PHI) phis /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\
  lookup_block h fn'.fn_blocks = SOME out ==>
  EVERY inst_wf (collect_phis out.bb_instructions)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rewrite_tac[EVERY_MEM] >> qx_gen_tac `inst` >> strip_tac >>
  drule_all current_certificate_leading_slot >> strip_tac
  >- (simp[inst_wf_def] >>
      irule current_event_fold_phi_well_formed >> simp[current_phi_slots_well_formed]) >>
  `i < LENGTH old.bb_instructions` by simp[] >>
  `inst_wf (EL i old.bb_instructions)` by
    (fs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[lookup_block_MEM, EL_MEM]) >>
  `(EL i old.bb_instructions).inst_opcode = PHI` by
    (simp[EL_APPEND_EQN] >> fs[EVERY_EL]) >>
  `phi_well_formed (EL i old.bb_instructions).inst_operands` by fs[inst_wf_def] >>
  simp[inst_wf_def] >> irule current_event_fold_phi_well_formed >> metis_tac[]
QED

Theorem current_certificate_target_phi_prefix_wf:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  lookup_block h fn.fn_blocks = SOME old /\ old.bb_instructions = phis ++ tail /\
  EVERY (\j. j.inst_opcode = PHI) phis /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\
  lookup_block h fn'.fn_blocks = SOME out /\
  out.bb_instructions = target_phis ++ target_tail /\
  EVERY (\j. j.inst_opcode = PHI) target_phis /\
  (target_tail = [] \/ (HD target_tail).inst_opcode <> PHI) ==>
  EVERY (\j. j.inst_opcode = PHI /\ inst_wf j) target_phis
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all current_certificate_leading_phi_wf >> strip_tac >>
  `collect_phis out.bb_instructions = target_phis` by
    (asm_rewrite_tac[] >> irule current_collect_phis_split >> metis_tac[]) >>
  fs[EVERY_MEM]
QED
