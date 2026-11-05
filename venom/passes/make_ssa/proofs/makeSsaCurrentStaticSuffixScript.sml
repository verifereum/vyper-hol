Theory makeSsaCurrentStaticSuffix
Ancestors makeSsaCurrentStaticGraph makeSsaCurrentStaticDemandProbe makeSsaCurrentCompletedOrdinary
  makeSsaCurrentReinsertionSlots makeSsaCurrentOriginalFinalSlots
  makeSsaCurrentCompletedBatch makeSsaCurrentSourceCuts makeSsaCurrentTreeTrace
  makeSsaCurrentFinalBlock makeSsaCurrentTreePaths makeSsaCurrentCleanupShape
  makeSsaCurrentOrdinaryJoint makeSsaCurrentDefs makeSsaCurrentOrdinary
  makeSsaCurrentOutputNames makeSsaCurrentCertificate makeSsaCurrentReinsertionNames
  venomExecSemantics venomWf venomExecProofs venomInst list rich_list

Theorem current_graph_event_length[local]:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  MEM (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2) events /\
  current_event_trace A H (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2) /\
  current_edge_shape (old with bb_instructions := ip ++ old.bb_instructions) bb ==>
  ?out. lookup_block l fn'.fn_blocks = SOME out /\
    LENGTH out.bb_instructions = LENGTH ip + LENGTH old.bb_instructions
Proof
  strip_tac >>
  `?before after. events = before ++ (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2)::after` by
    metis_tac[MEM_SPLIT] >>
  `LENGTH ren = LENGTH bb.bb_instructions` by
    (fs[current_event_trace_def] >> metis_tac[current_local_trace_lengths]) >>
  `LENGTH bb.bb_instructions = LENGTH ip + LENGTH old.bb_instructions` by
    fs[current_edge_shape_def, LIST_REL_EL_EQN] >>
  drule_all current_structural_certificate_final_event >>
  simp[current_event_label_def, current_event_renamed_block_def] >> strip_tac >>
  Cases_on `blocks_have_leading_phi fn.fn_blocks` >>
  gvs[current_cleanup_block_length, current_replay_edges_length]
QED

Theorem current_graph_certificate_length:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  lookup_block h fn.fn_blocks = SOME old ==>
  ?ip out. EVERY (\inst. inst.inst_opcode = PHI) ip /\
    lookup_block h fn'.fn_blocks = SOME out /\
    LENGTH out.bb_instructions = LENGTH ip + LENGTH old.bb_instructions /\
    current_static_body_start old.bb_instructions out.bb_instructions =
      LENGTH ip + phi_prefix_length old.bb_instructions
Proof
  strip_tac >>
  `MEM h (fn_labels fn)` by
    metis_tac[lookup_block_MEM, lookup_block_label, fn_labels_def, MEM_MAP] >>
  drule_all current_certificate_event_at >> strip_tac >>
  qpat_x_assum `current_event_label ev = h` (SUBST_ALL_TAC o SYM) >>
  drule_all current_certificate_source_shape >> strip_tac >>
  PairCases_on `ev` >>
  fs[current_event_label_def, current_event_input_block_def] >>
  drule_all current_graph_event_length >> strip_tac >>
  qexistsl_tac [`pre`, `out`] >> simp[current_static_body_start_def] >>
  `phi_prefix_length old.bb_instructions <= LENGTH old.bb_instructions` by
    metis_tac[phi_prefix_length_le] >> decide_tac
QED

Theorem current_graph_event_ordinary_fields[local]:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  MEM (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2) events /\
  lookup_block l fn.fn_blocks = SOME old /\
  old.bb_instructions = phis ++ tail /\
  EVERY (\inst. inst.inst_opcode = PHI) phis /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\
  j < LENGTH tail /\ (EL j tail).inst_opcode <> PHI /\ i = LENGTH phis + j ==>
  ?ip out. EVERY (\inst. inst.inst_opcode = PHI) ip /\
    lookup_block l fn'.fn_blocks = SOME out /\
    LENGTH out.bb_instructions = LENGTH ip + LENGTH old.bb_instructions /\
    LENGTH ip + i < LENGTH out.bb_instructions /\
    (EL (LENGTH ip+i) out.bb_instructions).inst_opcode =
      (EL i old.bb_instructions).inst_opcode /\
    LENGTH (EL (LENGTH ip+i) out.bb_instructions).inst_operands =
      LENGTH (EL i old.bb_instructions).inst_operands /\
    LENGTH (EL (LENGTH ip+i) out.bb_instructions).inst_outputs =
      LENGTH (EL i old.bb_instructions).inst_outputs
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?before after. events = before ++ (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2)::after` by
    metis_tac[MEM_SPLIT] >>
  drule_all current_certificate_ordinary_position >> strip_tac >>
  `(EL i old.bb_instructions).inst_opcode <> PHI` by
    simp[EL_APPEND_EQN] >>
  drule_all current_inst_trace_base_fields >> strip_tac >>
  `MEM (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2) events` by simp[] >>
  `current_event_trace A H (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2)` by
    metis_tac[current_certificate_source_shape, current_event_label_def] >>
  drule_all current_graph_event_length >> strip_tac >>
  `out' = out` by metis_tac[optionTheory.SOME_11] >> gvs[] >>
  qexists_tac `ip` >> simp[] >>
  qpat_x_assum `current_inst_no_id _ = current_inst_no_id _`
    (mp_tac o Q.AP_TERM `\inst. (inst.inst_opcode, inst.inst_operands, inst.inst_outputs)`) >>
  simp[current_inst_no_id_def] >> strip_tac >>
  gvs[current_rename_operands_map]
QED

Theorem current_graph_phi_partition[local]:
  !xs. (!i j. i < j /\ j < LENGTH xs /\ (EL j xs).inst_opcode = PHI ==>
            (EL i xs).inst_opcode = PHI) ==>
  ?phis tail. xs = phis ++ tail /\
    EVERY (\inst. inst.inst_opcode = PHI) phis /\
    EVERY (\inst. inst.inst_opcode <> PHI) tail
Proof
  Induct >- (simp[] >> qexistsl_tac [`[]`, `[]`] >> simp[]) >>
  rpt gen_tac >> strip_tac >> Cases_on `h.inst_opcode = PHI`
  >- (`!i j. i < j /\ j < LENGTH xs /\ (EL j xs).inst_opcode = PHI ==>
            (EL i xs).inst_opcode = PHI` by
        (rpt strip_tac >> first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[]) >>
      first_x_assum drule >> strip_tac >>
      qexistsl_tac [`h::phis`, `tail`] >> simp[]) >>
  qexistsl_tac [`[]`, `h::xs`] >> simp[EVERY_EL] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`0`, `SUC n`] mp_tac) >> simp[]
QED

Theorem current_graph_certificate_ordinary_fields:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  lookup_block h fn.fn_blocks = SOME old /\
  phi_prefix_length old.bb_instructions <= i /\ i < LENGTH old.bb_instructions ==>
  ?out. lookup_block h fn'.fn_blocks = SOME out /\
    current_static_body_start old.bb_instructions out.bb_instructions +
      (i - phi_prefix_length old.bb_instructions) < LENGTH out.bb_instructions /\
    (EL (current_static_body_start old.bb_instructions out.bb_instructions +
      (i - phi_prefix_length old.bb_instructions)) out.bb_instructions).inst_opcode =
      (EL i old.bb_instructions).inst_opcode /\
    LENGTH (EL (current_static_body_start old.bb_instructions out.bb_instructions +
      (i - phi_prefix_length old.bb_instructions)) out.bb_instructions).inst_operands =
      LENGTH (EL i old.bb_instructions).inst_operands /\
    LENGTH (EL (current_static_body_start old.bb_instructions out.bb_instructions +
      (i - phi_prefix_length old.bb_instructions)) out.bb_instructions).inst_outputs =
      LENGTH (EL i old.bb_instructions).inst_outputs
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `bb_well_formed old` by metis_tac[wf_function_def, lookup_block_MEM] >>
  `?phis tail. old.bb_instructions = phis ++ tail /\
    EVERY (\inst. inst.inst_opcode = PHI) phis /\
    EVERY (\inst. inst.inst_opcode <> PHI) tail` by
    (irule current_graph_phi_partition >> fs[bb_well_formed_def]) >>
  `phi_prefix_length old.bb_instructions = LENGTH phis` by
    (`tail = [] \/ (HD tail).inst_opcode <> PHI` by
       (Cases_on `tail` >> gvs[]) >>
     metis_tac[current_phi_prefix_maximal_length]) >>
  `?j. j < LENGTH tail /\ i = LENGTH phis+j /\ (EL j tail).inst_opcode <> PHI` by
    (qexists_tac `i-LENGTH phis` >> fs[EVERY_EL] >> simp[]) >>
  Cases_on `tail = []` >- fs[] >>
  `(HD tail).inst_opcode <> PHI` by (Cases_on `tail` >> gvs[]) >>
  `MEM h (fn_labels fn)` by
    metis_tac[lookup_block_MEM, lookup_block_label, fn_labels_def, MEM_MAP] >>
  drule_all current_certificate_event_at >> strip_tac >>
  PairCases_on `ev` >>
  qpat_x_assum `current_event_label _ = h`
    (SUBST_ALL_TAC o PURE_REWRITE_RULE [current_event_label_def]) >>
  drule_all (cj 2 (REWRITE_RULE
    [RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR, DISJ_IMP_THM]
    current_graph_event_ordinary_fields)) >> strip_tac >>
  goal_assum $ drule_at Any >>
  simp[current_static_body_start_def] >>
  `LENGTH phis <= LENGTH old.bb_instructions` by simp[] >>
  `LENGTH out.bb_instructions - (LENGTH old.bb_instructions - LENGTH phis) +
    (i - LENGTH phis) = LENGTH ip + i` by decide_tac >>
  qpat_x_assum `old.bb_instructions = phis ++ tail`
    (fn th => pure_rewrite_tac [GSYM th]) >>
  `j + (LENGTH ip + LENGTH phis) = LENGTH ip + i` by decide_tac >>
  `j + LENGTH phis = i` by decide_tac >>
  qpat_x_assum `j + (LENGTH ip + LENGTH phis) = _`
    (fn th => pure_rewrite_tac [th]) >>
  qpat_x_assum `j + LENGTH phis = i`
    (fn th => pure_rewrite_tac [th]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem current_graph_event_ordinary_output[local]:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  MEM (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2) events /\
  current_event_valid A V (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2) /\
  A l = current_block_annotations old pre /\
  lookup_block l fn.fn_blocks = SOME old /\
  old.bb_instructions = phis ++ tail /\
  EVERY (\inst. inst.inst_opcode = PHI) phis /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\
  j < LENGTH tail /\ (EL j tail).inst_opcode <> PHI /\ i = LENGTH phis + j /\
  k < LENGTH (EL i old.bb_instructions).inst_outputs ==>
  ?out. lookup_block l fn'.fn_blocks = SOME out /\
    current_token_name H (CurrentOriginal old.bb_label i k) =
      SOME (EL k (EL (current_static_body_start old.bb_instructions out.bb_instructions +
        (i - phi_prefix_length old.bb_instructions)) out.bb_instructions).inst_outputs)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?before after. events = before ++ (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2)::after` by
    metis_tac[MEM_SPLIT] >>
  drule_all current_certificate_ordinary_position >> strip_tac >>
  `current_event_trace A H (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2)` by
    metis_tac[current_certificate_source_shape, current_event_label_def] >>
  `LENGTH pre = LENGTH ip` by
    (fs[current_event_trace_def] >> drule current_local_trace_lengths >>
     fs[current_block_annotations_def, current_inserted_annotations_def,
        current_edge_shape_def, LIST_REL_EL_EQN] >>
     rpt strip_tac >>
     qpat_x_assum `LENGTH ip + LENGTH old.bb_instructions = _` mp_tac >>
     simp[] >> decide_tac) >>
  `i < LENGTH old.bb_instructions` by simp[] >>
  drule_all current_event_original_output_name >> strip_tac >>
  drule_all current_graph_event_length >> strip_tac >>
  `out' = out` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `out' = out` SUBST_ALL_TAC >>
  `phi_prefix_length old.bb_instructions = LENGTH phis` by
    metis_tac[current_phi_prefix_maximal_length] >>
  `current_static_body_start old.bb_instructions out.bb_instructions +
      (i - phi_prefix_length old.bb_instructions) = LENGTH pre + i` by
    (simp[current_static_body_start_def] >>
     qpat_x_assum `LENGTH out.bb_instructions = _` mp_tac >>
     simp[] >> decide_tac) >>
  qexists_tac `out` >> simp[] >>
  qpat_x_assum `current_inst_no_id _ = current_inst_no_id _`
    (mp_tac o Q.AP_TERM `\inst. inst.inst_outputs`) >>
  simp[current_inst_no_id_def] >> metis_tac[]
QED

Theorem current_graph_certificate_ordinary_output:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  fn_inst_wf fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  lookup_block h fn.fn_blocks = SOME old /\
  phi_prefix_length old.bb_instructions <= i /\ i < LENGTH old.bb_instructions /\
  k < LENGTH (EL i old.bb_instructions).inst_outputs ==>
  ?out. lookup_block h fn'.fn_blocks = SOME out /\
    current_token_name H (CurrentOriginal old.bb_label i k) =
      SOME (EL k (EL (current_static_body_start old.bb_instructions out.bb_instructions +
        (i - phi_prefix_length old.bb_instructions)) out.bb_instructions).inst_outputs)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all current_certificate_events_valid >> strip_tac >>
  drule_all current_certificate_block_replay >> strip_tac >>
  `bb_well_formed old` by metis_tac[wf_function_def, lookup_block_MEM] >>
  `?phis tail. old.bb_instructions = phis ++ tail /\
    EVERY (\inst. inst.inst_opcode = PHI) phis /\
    EVERY (\inst. inst.inst_opcode <> PHI) tail` by
    (irule current_graph_phi_partition >> fs[bb_well_formed_def]) >>
  `phi_prefix_length old.bb_instructions = LENGTH phis` by
    (`tail = [] \/ (HD tail).inst_opcode <> PHI` by
       (Cases_on `tail` >> gvs[]) >>
     metis_tac[current_phi_prefix_maximal_length]) >>
  `?j. j < LENGTH tail /\ i = LENGTH phis+j /\ (EL j tail).inst_opcode <> PHI` by
    (qexists_tac `i-LENGTH phis` >> fs[EVERY_EL] >> simp[]) >>
  Cases_on `tail = []` >- fs[] >>
  `(HD tail).inst_opcode <> PHI` by (Cases_on `tail` >> gvs[]) >>
  `MEM h (fn_labels fn)` by
    metis_tac[lookup_block_MEM, lookup_block_label, fn_labels_def, MEM_MAP] >>
  drule_all current_certificate_event_at >> strip_tac >>
  `current_event_valid A V ev` by metis_tac[EVERY_MEM] >>
  PairCases_on `ev` >>
  qpat_x_assum `current_event_label _ = h`
    (SUBST_ALL_TAC o PURE_REWRITE_RULE [current_event_label_def]) >>
  drule_all (cj 2 (REWRITE_RULE
    [RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR, DISJ_IMP_THM]
    current_graph_event_ordinary_output)) >> strip_tac >>
  goal_assum $ drule_at Any >> simp[]
QED
