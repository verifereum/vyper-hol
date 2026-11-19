Theory requestCutCfgFrontierGuard
Ancestors
  o1ContractCfgNormJointCursors o1ContractCfgNormCursorProjection
  o1ContractCfgNormCursors o1ContractCfgNorm o1PassLift cfgNormSupplySim
  unitMemInv contextCodegenRel frameJointTransition venomInst list pair

Theorem cfg_norm_cursors_nonadmin_opcode[local]:
  !C rounds cells. cfg_norm_cursors C rounds cells ==>
    ~MEM (FST (FST (LAST cells))).inst_opcode [ASSIGN; JMP; JNZ] ==>
    (FST (FST (HD cells))).inst_opcode = (FST (FST (LAST cells))).inst_opcode
Proof
  ho_match_mp_tac cfg_norm_cursors_ind >> simp[LAST_CONS_cond] >>
  rpt conj_tac >> rpt strip_tac >> gvs[]
  >- metis_tac[supply_block_image_index] >>
  `ir_supply_inst_ok s /\ ir_supply_covers_fn s fn` by gvs[supply_norm_inv_def] >>
  `MEM (EL v.vs_inst_idx split.bb_instructions).inst_opcode [ASSIGN; JMP; JNZ]` by
    (drule_all supply_split_index_shape >> simp[]) >>
  metis_tac[MEM]
QED

(* A cursor without an executable edge still carries the memory comparison. *)
Theorem request_cut_cfg_guard_projection:
  cfg_norm_joint_cursors C8 C9 (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9) /\
  inst_mem_ranges inst9 s9 <> [] /\ ~in_revert_forward fn9 s9 ==>
  inst8.inst_opcode = inst9.inst_opcode /\
  inst_mem_ranges inst8 s8 = inst_mem_ranges inst9 s9 /\
  s8.vs_initial_fmp = s9.vs_initial_fmp /\ ~in_revert_forward fn8 s8
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~MEM inst9.inst_opcode [ASSIGN; JMP; JNZ]` by
    (strip_tac >> `MEM inst9.inst_opcode [PHI; JMP; JNZ; ASSIGN]` by fs[] >>
     drule supply_inst_mem_ranges_empty >> metis_tac[]) >>
  PairCases_on `current` >> gvs[cfg_norm_joint_cursors_def] >>
  qpat_assum `EVERY _ schedules` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
  disch_then drule >> simp[] >> strip_tac >>
  `inst8.inst_opcode = inst9.inst_opcode` by
    (drule cfg_norm_cursors_nonadmin_opcode >> simp[]) >>
  drule_all cfg_norm_cursors_projection >> simp[mem_corr_def]
QED

Theorem request_cut_cfg_disjoint_guard:
  cfg_norm_joint_cursors C8 C9 (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9) /\
  ~in_revert_forward fn9 s9 /\
  (inst_mem_ranges inst9 s9 <> [] ==>
    source_memory_reads_disjoint cpl inst8 s8 /\
    context_source_memory_writes_disjoint cpl inst8 s8) ==>
  source_memory_reads_disjoint cpl inst9 s9 /\
  context_source_memory_writes_disjoint cpl inst9 s9
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `inst_mem_ranges inst9 s9 = []`
  >- fs[inst_mem_ranges_def, source_memory_reads_disjoint_def,
        context_source_memory_writes_disjoint_def] >>
  drule_all request_cut_cfg_guard_projection >> strip_tac >>
  qpat_x_assum `inst_mem_ranges inst9 s9 <> [] ==> _` drule >>
  simp_tac bool_ss [source_memory_reads_disjoint_def,
    context_source_memory_writes_disjoint_def, GSYM EVERY_APPEND,
    GSYM inst_mem_ranges_def] >> metis_tac[]
QED
