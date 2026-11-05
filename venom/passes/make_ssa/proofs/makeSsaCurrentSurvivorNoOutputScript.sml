Theory makeSsaCurrentSurvivorNoOutput
Ancestors makeSsaCurrentReinsertionOrder makeSsaCurrentReinsertionNames
  venomExecProps makeSsaCurrentLiveTransport makeSsaCurrentRetainedNonclobber
  makeSsaCurrentRetainedProjection makeSsaCurrentInsertedValue
  makeSsaCurrentDemandDominance makeSsaCurrentDefs venomWf venomInst list

Theorem current_certificate_survivor_no_phi_output:
  current_structural_certificate s fn fn' s' A H events /\
  fn_defs_reach_uses fn /\ fn_phi_operands_single_def fn /\
  fn_phis_cover_preds fn /\ fn_phi_outputs_single_def fn /\ fn_phis_non_degenerate fn /\
  all_reachable fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\ entry_block fn = SOME eb /\
  lookup_block h fn.fn_blocks = SOME old /\ lookup_block h fn'.fn_blocks = SOME out /\
  current_actual_inserted fn v h /\ current_token_name H (CurrentInserted v h) = SOME n /\
  MEM n (FLAT (MAP (\j. j.inst_outputs) (collect_phis out.bb_instructions))) ==>
  !i. i < LENGTH (collect_phis old.bb_instructions) ==>
    ~MEM v (inst_defs (EL i old.bb_instructions))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  gen_tac >> strip_tac >> strip_tac >>
  `i < LENGTH old.bb_instructions` by
    metis_tac[current_collect_phis_length, arithmeticTheory.LESS_LESS_EQ_TRANS] >>
  qspec_then `old.bb_instructions` (map_every assume_tac o CONJUNCTS)
    current_collect_phi_split >>
  `(EL i old.bb_instructions).inst_opcode = PHI` by
    (fs[EVERY_EL] >> metis_tac[EL_APPEND_EQN]) >>
  `(EL i old.bb_instructions).inst_outputs = [v]` by
    (`inst_wf (EL i old.bb_instructions)` by
      (fs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[lookup_block_MEM, EL_MEM]) >>
     qpat_x_assum `inst_wf _` mp_tac >>
     simp[inst_wf_def, LENGTH_EQ_NUM_compute] >>
     strip_tac >> gvs[inst_defs_def]) >>
  `blocks_have_leading_phi fn.fn_blocks` by
    (spose_not_then assume_tac >> drule_all current_no_leading_phi_cut >> simp[] >>
     strip_tac >> gvs[]) >>
  `n = v` by
    (drule_all current_certificate_reinserted_first_name >> simp[]) >>
  qpat_x_assum `n = v` SUBST_ALL_TAC >>
  drule_all current_certificate_reinsertion_order >> strip_tac >>
  `out' = out` by metis_tac[optionTheory.SOME_11] >> gvs[] >>
  `ALL_DISTINCT (FLAT (MAP (\j. j.inst_outputs) out.bb_instructions))` by
    (irule current_certificate_block_outputs_distinct >> metis_tac[]) >>
  `?inst. MEM inst (collect_phis out.bb_instructions) /\ MEM v inst.inst_outputs` by
    (fs[MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  `?q. q < LENGTH out.bb_instructions /\ inst = EL q out.bb_instructions` by
    (qspec_then `out.bb_instructions` strip_assume_tac current_collect_phi_split >>
     metis_tac[MEM_EL, MEM_APPEND]) >>
  `q = c` by
    (irule current_distinct_flat_output_index >>
     qexistsl_tac [`out.bb_instructions`, `v`] >> gvs[]) >>
  `inst.inst_opcode = PHI` by
    (qspec_then `out.bb_instructions` strip_assume_tac current_collect_phi_split >>
     gvs[EVERY_MEM] >> metis_tac[]) >>
  gvs[]
QED
