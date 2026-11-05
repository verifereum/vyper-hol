Theory makeSsaCurrentRetainedProjection
Ancestors makeSsaCurrentRetainedValue makeSsaCurrentOriginalFinalSlots
  makeSsaCurrentRetainedNonclobber makeSsaCurrentInstructionSingleton
  makeSsaCurrentSingletonSelectors venomExecProps venomWf venomInst list rich_list

Theorem current_singleton_phi_output_name:
  wf_function fn /\ lookup_block h fn.fn_blocks = SOME old /\
  i < LENGTH old.bb_instructions /\ (EL i old.bb_instructions).inst_outputs = [dst] /\
  MEM (dst,n) (current_instruction_singleton_table fn H) /\
  current_token_name H (CurrentOriginal h i 0) = SOME name ==> name = n
Proof
  strip_tac >>
  `MEM old fn.fn_blocks /\ old.bb_label = h` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `?b. b < LENGTH fn.fn_blocks /\ old = EL b fn.fn_blocks` by metis_tac[MEM_EL] >>
  `MEM (b,i) (current_defining_sites fn dst)` by
    gvs[current_defining_sites_member] >>
  drule current_singleton_member_final_site >> strip_tac >>
  `b = b' /\ i = i'` by metis_tac[MEM, pairTheory.PAIR_EQ] >>
  gvs[] >> `j = 0` by simp[] >> gvs[]
QED

Theorem current_distinct_flat_output_index:
  !insts q r. ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs) insts)) /\
  q < LENGTH insts /\ r < LENGTH insts /\
  MEM n (EL q insts).inst_outputs /\ MEM n (EL r insts).inst_outputs ==> q = r
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `q` >> Cases_on `r` >>
  simp[ALL_DISTINCT_APPEND, MEM_FLAT, MEM_MAP] >> rpt strip_tac >>
  metis_tac[EL_MEM]
QED

Theorem current_certificate_retained_projected_eval:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  first_block_no_preds fn /\ blocks_have_leading_phi fn.fn_blocks /\
  fn_defs_reach_uses fn /\ fn_phi_operands_single_def fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\ fn_phis_non_degenerate fn /\
  lookup_block h fn.fn_blocks = SOME old /\ old.bb_instructions = phis ++ tail /\
  EVERY (\j. j.inst_opcode = PHI) phis /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\ i < LENGTH phis /\
  (EL i old.bb_instructions).inst_opcode = PHI /\
  MEM ev events /\ current_event_label ev = p /\ fn_cfg_edge fn p h /\
  lookup_block p fn.fn_blocks = SOME pred /\
  st.vs_prev_bb = SOME p /\ st'.vs_prev_bb = SOME p /\
  current_singleton_agree (current_instruction_singleton_table fn H) st st' /\
  eval_one_phi st (EL i old.bb_instructions) = SOME (dst,value) /\
  MEM (dst,n) (current_instruction_singleton_table fn H) ==>
  ?out r batch. lookup_block h fn'.fn_blocks = SOME out /\
    r < batch /\ batch <= LENGTH out.bb_instructions /\
    EVERY (\j. j.inst_opcode = PHI) (TAKE batch out.bb_instructions) /\
    (EL r out.bb_instructions).inst_opcode = PHI /\
    (EL r out.bb_instructions).inst_outputs = [n] /\
    eval_one_phi st' (EL r out.bb_instructions) = SOME (n,value) /\
    !q. q < LENGTH out.bb_instructions /\
      MEM n (EL q out.bb_instructions).inst_outputs ==> q = r
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `i < LENGTH old.bb_instructions` by simp[] >>
  `inst_wf (EL i old.bb_instructions)` by
    (fs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[lookup_block_MEM, EL_MEM]) >>
  drule_all current_eval_one_phi_selected >> strip_tac >>
  drule_all current_certificate_retained_eval >> strip_tac >>
  drule_all current_singleton_phi_output_name >> disch_then SUBST_ALL_TAC >>
  drule_all current_certificate_block_outputs_distinct >> strip_tac >>
  qexistsl_tac [`out`, `r`, `batch`] >> asm_rewrite_tac[] >>
  rpt strip_tac >> irule current_distinct_flat_output_index >>
  metis_tac[MEM, arithmeticTheory.LESS_LESS_EQ_TRANS]
QED
