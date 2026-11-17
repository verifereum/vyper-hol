Theory dftPacketPreterminalOracle
Ancestors
  dftPacketSuccessfulSchedule dftGasInvLookupBlock dftGasInvFixedTrace
  dftGasInvExtraction dftRunRel dftScheduleOrder dftStructural dftCorrectness
  venomWf venomInst venomState list sorting

Theorem preterminal_body_ids[local]:
  dft_block_rel bb bt /\
  bb.bb_instructions = ps ++ ordered ++ [term] /\
  bt.bb_instructions = ps ++ executed ++ [term] /\
  ps = FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions /\
  EVERY (\i. ~is_pseudo i.inst_opcode) ordered /\
  ~is_pseudo term.inst_opcode ==>
  PERM (MAP (\i. i.inst_id) executed) (MAP (\i. i.inst_id) ordered)
Proof
  strip_tac >>
  `EVERY (\i. is_pseudo i.inst_opcode) ps` by
    (qpat_x_assum `ps = _` SUBST1_TAC >> simp[EVERY_FILTER, EVERY_MEM]) >>
  `FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions = ordered ++ [term]` by
    (qpat_x_assum `ps = FILTER _ _` kall_tac >>
     simp[FILTER_APPEND_DISTRIB] >>
     `FILTER (\i. ~is_pseudo i.inst_opcode) ps = []` by
       (simp[FILTER_EQ_NIL, EVERY_MEM] >> gvs[EVERY_MEM]) >>
     `FILTER (\i. ~is_pseudo i.inst_opcode) ordered = ordered` by
       simp[FILTER_EQ_ID] >> simp[]) >>
  qpat_x_assum `ps = FILTER _ _` (assume_tac o SYM) >>
  qpat_x_assum `dft_block_rel _ _` mp_tac >>
  simp[dft_block_rel_def] >> strip_tac >> gvs[MAP_APPEND, PERM_APPEND_IFF]
QED

Theorem preterminal_body_replay[local]:
  dft_fn_rel sf tf /\
  lookup_block name sf.fn_blocks = SOME bb /\
  lookup_block name tf.fn_blocks = SOME bt /\
  bb.bb_instructions = ps ++ ordered ++ [term] /\
  bt.bb_instructions = ps ++ executed ++ [term] /\
  ps = FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions /\
  EVERY (\i. ~is_pseudo i.inst_opcode) ordered /\
  ~is_pseudo term.inst_opcode /\
  EVERY (from_block bb.bb_instructions) executed /\
  inv_ev_trace orc p d fuel ctx executed s t ==>
  inv_ev_trace orc p d fuel ctx ordered s t
Proof
  strip_tac >>
  `MEM bb sf.fn_blocks` by
    metis_tac[venomExecPropsTheory.FIND_MEM, lookup_block_def] >>
  `dft_block_rel bb bt` by metis_tac[dft_fn_rel_lookup_order] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[dft_fn_rel_def, bb_inst_ids_distinct] >>
  `PERM (MAP (\i. i.inst_id) executed) (MAP (\i. i.inst_id) ordered)` by
    metis_tac[preterminal_body_ids] >>
  drule_all inv_trace_original_representatives >> strip_tac >>
  `EVERY (\i. MEM i bb.bb_instructions) originals /\
   EVERY (\i. MEM i bb.bb_instructions) ordered` by
    (qpat_x_assum `ps = FILTER _ _` kall_tac >>
     gvs[EVERY_MEM, MEM_APPEND] >> metis_tac[]) >>
  `PERM originals ordered` by
    (irule inv_original_ids_perm >> simp[] >>
     qexists_tac `bb.bb_instructions` >> simp[]) >>
  `ALL_DISTINCT ordered` by
    (qpat_x_assum `ps = FILTER _ _` kall_tac >>
     gvs[MAP_APPEND, ALL_DISTINCT_APPEND] >> metis_tac[ALL_DISTINCT_MAP]) >>
  qpat_x_assum `inv_ev_trace _ _ _ _ _ executed _ _` kall_tac >>
  qpat_x_assum `ps = FILTER _ _` kall_tac >>
  irule inv_lookup_body_sort >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[MAP_APPEND] >>
  qexistsl_tac [`bt`, `tf`, `name`] >> simp[MAP_APPEND]
QED

Theorem dft_packet_preterminal_oracle_reflect:
  LIST_REL dft_fn_rel C.ctx_functions D.ctx_functions /\
  dft_fn_rel sf tf /\
  lookup_block name sf.fn_blocks = SOME bb /\
  lookup_block name tf.fn_blocks = SOME bt /\
  bb.bb_instructions = ps ++ ordered ++ [term] /\
  bt.bb_instructions = ps ++ executed ++ [term] /\
  ps = FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions /\
  EVERY (\i. ~is_pseudo i.inst_opcode) ordered /\
  ~is_pseudo term.inst_opcode /\
  EVERY (from_block bb.bb_instructions) executed /\
  inv_ev_trace orc p d fuel D executed s t ==>
  inv_ev_trace orc p d fuel C ordered s t
Proof
  strip_tac >>
  `inv_ev_trace orc p d fuel D ordered s t` by
    (irule preterminal_body_replay >> metis_tac[]) >>
  irule dft_packet_successful_schedule_reflect >>
  goal_assum (drule_at Any) >>
  simp[dft_head_bubbles_refl]
QED
