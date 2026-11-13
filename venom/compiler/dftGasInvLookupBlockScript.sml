Theory dftGasInvLookupBlock
Ancestors
  dftGasInvBlockTrace dftGasInvFixedTrace dftGasInvFlexibleTrace
  dftGasInvResidualTrace dftGasInvInversion dftGasOracleDefs dftGasInvExtraction
  dftRunRel dftScheduleOrder dftFrontEquiv dftCorrectnessFinal
  dftStructural dftBlockSim opcodeClass
  dftCorrectness venomWf venomInst venomState list rich_list sorting

Theorem inv_lookup_source_split[local]:
  dft_fn_rel fn fn' /\ lookup_block name fn.fn_blocks = SOME bb ==>
  ?pre body term.
    bb.bb_instructions = pre ++ body ++ [term] /\
    pre = FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions /\
    EVERY (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) body /\
    is_terminator term.inst_opcode /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[venomExecPropsTheory.FIND_MEM, lookup_block_def] >>
  `wf_function fn /\ pseudos_prefix bb` by
    gvs[dft_fn_rel_def, fn_pseudos_prefix_def] >>
  `bb_well_formed bb /\ ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[wf_function_def, EVERY_MEM, bb_inst_ids_distinct] >>
  drule_all pseudos_prefix_front_decomposition >> strip_tac >>
  qexistsl_tac [`FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions`,
    `FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bb.bb_instructions`,
    `LAST bb.bb_instructions`] >>
  simp[EVERY_FILTER, EVERY_MEM] >>
  gvs[bb_well_formed_def] >> metis_tac[APPEND_FRONT_LAST, APPEND_ASSOC]
QED

Theorem inv_related_terminal_unique[local]:
  bb_well_formed bb /\ dft_block_rel bb bb' /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb'.bb_instructions) /\
  MEM i bb'.bb_instructions /\ is_terminator i.inst_opcode ==>
  i = LAST bb'.bb_instructions
Proof
  strip_tac >>
  `LAST bb'.bb_instructions = LAST bb.bb_instructions` by
    metis_tac[dftRunRelTheory.dft_block_rel_last] >>
  `~is_pseudo i.inst_opcode` by
    (Cases_on `i.inst_opcode` >> gvs[is_terminator_def, is_pseudo_def]) >>
  `from_block bb.bb_instructions i` by
    (gvs[dft_block_rel_def, MEM_APPEND, MEM_FILTER] >> gvs[EVERY_MEM]) >>
  `?j. MEM j bb.bb_instructions /\ j.inst_id = i.inst_id /\
       is_terminator j.inst_opcode` by
    (gvs[from_block_def]
     >- (qexists_tac `i` >> simp[]) >>
     metis_tac[inv_ev_flip_nonterminator]) >>
  `j = LAST bb.bb_instructions` by
    (gvs[MEM_EL, bb_well_formed_def, LAST_EL] >>
     rename1 `k < LENGTH bb.bb_instructions` >>
     `k = PRE (LENGTH bb.bb_instructions)` by metis_tac[] >> gvs[]) >>
  `bb'.bb_instructions <> []` by
    (Cases_on `bb'.bb_instructions` >> gvs[]) >>
  metis_tac[all_distinct_map_mem_inj, MEM_LAST_NOT_NIL]
QED

Theorem inv_related_front_nonterminators[local]:
  bb_well_formed bb /\ dft_block_rel bb bb' /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb'.bb_instructions) ==>
  EVERY (\i. ~is_terminator i.inst_opcode) (FRONT bb'.bb_instructions)
Proof
  strip_tac >> simp[EVERY_MEM] >> rpt strip_tac >>
  `bb'.bb_instructions <> []` by
    (drule dft_block_rel_length >> gvs[bb_well_formed_def] >>
     Cases_on `bb'.bb_instructions` >> gvs[]) >>
  `MEM i bb'.bb_instructions` by
    metis_tac[APPEND_FRONT_LAST, MEM_APPEND] >>
  `i = LAST bb'.bb_instructions` by
    metis_tac[inv_related_terminal_unique] >>
  `ALL_DISTINCT bb'.bb_instructions` by metis_tac[ALL_DISTINCT_MAP] >>
  `ALL_DISTINCT (FRONT bb'.bb_instructions ++ [LAST bb'.bb_instructions])` by
    metis_tac[APPEND_FRONT_LAST] >>
  gvs[ALL_DISTINCT_APPEND]
QED

Theorem inv_related_target_split[local]:
  bb_well_formed bb /\ dft_block_rel bb bb' /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb'.bb_instructions) ==>
  ?body.
    bb'.bb_instructions =
      FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions ++
      body ++ [LAST bb.bb_instructions] /\
    EVERY (from_block bb.bb_instructions) body /\
    EVERY (\i. ~is_terminator i.inst_opcode) body
Proof
  strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (FRONT bb'.bb_instructions)` by
    metis_tac[inv_related_front_nonterminators] >>
  `LAST bb'.bb_instructions = LAST bb.bb_instructions` by
    metis_tac[dftRunRelTheory.dft_block_rel_last] >>
  `bb.bb_instructions <> [] /\ is_terminator (LAST bb.bb_instructions).inst_opcode` by
    gvs[bb_well_formed_def] >>
  `~is_pseudo (LAST bb.bb_instructions).inst_opcode` by
    (Cases_on `(LAST bb.bb_instructions).inst_opcode` >>
     gvs[is_terminator_def, is_pseudo_def]) >>
  qpat_x_assum `dft_block_rel _ _` mp_tac >>
  simp[dft_block_rel_def] >> strip_tac >>
  rename1 `EVERY (from_block bb.bb_instructions) scheduled` >>
  `scheduled <> []` by
    (strip_tac >> gvs[] >>
     `FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions = []` by
       metis_tac[PERM_NIL, MAP_EQ_NIL] >>
     gvs[FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[MEM_LAST_NOT_NIL]) >>
  qexists_tac `FRONT scheduled` >>
  `LAST scheduled = LAST bb.bb_instructions` by
    (Cases_on `scheduled` >> gvs[LAST_APPEND]) >>
  conj_tac >- metis_tac[APPEND_FRONT_LAST, APPEND_ASSOC] >>
  conj_tac
  >- (gvs[EVERY_MEM] >> metis_tac[APPEND_FRONT_LAST, MEM_APPEND]) >>
  Cases_on `scheduled` >> gvs[FRONT_APPEND, EVERY_APPEND]
QED

Theorem inv_related_body_ids[local]:
  dft_block_rel bb bb' /\
  bb.bb_instructions = pre ++ ordered ++ [term] /\
  bb'.bb_instructions = pre ++ executed ++ [term] /\
  pre = FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions /\
  EVERY (\i. ~is_pseudo i.inst_opcode) ordered /\
  ~is_pseudo term.inst_opcode ==>
  PERM (MAP (\i. i.inst_id) executed) (MAP (\i. i.inst_id) ordered)
Proof
  strip_tac >>
  `EVERY (\i. is_pseudo i.inst_opcode) pre` by
    (qpat_x_assum `pre = _` SUBST1_TAC >> simp[EVERY_FILTER, EVERY_MEM]) >>
  `FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions = ordered ++ [term]` by
    (qpat_x_assum `pre = FILTER _ _` kall_tac >>
     simp[FILTER_APPEND_DISTRIB] >>
     `FILTER (\i. ~is_pseudo i.inst_opcode) pre = []` by
       (simp[FILTER_EQ_NIL, EVERY_MEM] >> gvs[EVERY_MEM]) >>
     `FILTER (\i. ~is_pseudo i.inst_opcode) ordered = ordered` by
       simp[FILTER_EQ_ID] >> simp[]) >>
  qpat_x_assum `pre = FILTER _ _` (assume_tac o SYM) >>
  qpat_x_assum `dft_block_rel _ _` mp_tac >>
  simp[dft_block_rel_def] >> strip_tac >> gvs[MAP_APPEND, PERM_APPEND_IFF]
QED

Theorem inv_lookup_body_replay[local]:
  dft_fn_rel fn fn' /\
  lookup_block name fn.fn_blocks = SOME bb /\
  lookup_block name fn'.fn_blocks = SOME bb' /\
  bb.bb_instructions = pre ++ ordered ++ [term] /\
  bb'.bb_instructions = pre ++ executed ++ [term] /\
  pre = FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions /\
  EVERY (\i. ~is_pseudo i.inst_opcode) ordered /\
  ~is_pseudo term.inst_opcode /\
  EVERY (from_block bb.bb_instructions) executed /\
  inv_ev_trace orc p d fuel ctx executed s u ==>
  inv_ev_trace orc p d fuel ctx ordered s u
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by
    metis_tac[venomExecPropsTheory.FIND_MEM, lookup_block_def] >>
  `dft_block_rel bb bb'` by metis_tac[dft_fn_rel_lookup_order] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[dft_fn_rel_def, bb_inst_ids_distinct] >>
  `PERM (MAP (\i. i.inst_id) executed) (MAP (\i. i.inst_id) ordered)` by
    metis_tac[inv_related_body_ids] >>
  drule_all inv_trace_original_representatives >> strip_tac >>
  `EVERY (\i. MEM i bb.bb_instructions) originals /\
   EVERY (\i. MEM i bb.bb_instructions) ordered` by
    (qpat_x_assum `pre = FILTER _ _` kall_tac >>
     gvs[EVERY_MEM, MEM_APPEND] >> metis_tac[]) >>
  `PERM originals ordered` by
    (irule inv_original_ids_perm >> simp[] >>
     qexists_tac `bb.bb_instructions` >> simp[]) >>
  `ALL_DISTINCT ordered` by
    (qpat_x_assum `pre = FILTER _ _` kall_tac >>
     gvs[MAP_APPEND, ALL_DISTINCT_APPEND] >> metis_tac[ALL_DISTINCT_MAP]) >>
  qpat_x_assum `inv_ev_trace _ _ _ _ _ executed _ _` kall_tac >>
  qpat_x_assum `pre = FILTER _ _` kall_tac >>
  irule inv_lookup_body_sort >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[MAP_APPEND] >>
  qexistsl_tac [`bb'`, `fn'`, `name`] >> simp[MAP_APPEND]
QED

Theorem inv_lookup_block_success_reflect:
  dft_fn_rel fn fn' /\
  lookup_block name fn.fn_blocks = SOME bb /\
  lookup_block name fn'.fn_blocks = SOME bb' /\
  s.vs_inst_idx = LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) /\
  (r = OK t \/ r = IntRet vals t) /\
  ev_block orc p d fuel ctx bb' s = r ==>
  ev_block orc p d fuel ctx bb s = r
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by
    metis_tac[venomExecPropsTheory.FIND_MEM, lookup_block_def] >>
  `dft_block_rel bb bb'` by metis_tac[dft_fn_rel_lookup_order] >>
  `bb_well_formed bb` by metis_tac[dft_fn_rel_def, wf_function_def, EVERY_MEM] >>
  drule_all inv_lookup_source_split >> strip_tac >>
  rename1 `bb.bb_instructions = pre ++ ordered ++ [term]` >>
  qpat_x_assum `pre = FILTER _ _` (assume_tac o SYM) >>
  `LAST bb.bb_instructions = term` by simp[LAST_APPEND] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb'.bb_instructions)` by
    metis_tac[inv_lookup_block_contract] >>
  drule_all inv_related_target_split >> strip_tac >>
  rename1 `EVERY (from_block bb.bb_instructions) executed` >>
  `bb'.bb_instructions = pre ++ executed ++ [term]` by metis_tac[] >>
  `EVERY (\i. ~is_pseudo i.inst_opcode) ordered` by gvs[EVERY_MEM] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) ordered` by gvs[EVERY_MEM] >>
  `~is_pseudo term.inst_opcode` by
    (Cases_on `term.inst_opcode` >> gvs[is_terminator_def, is_pseudo_def]) >>
  `s.vs_inst_idx = LENGTH pre` by metis_tac[] >>
  gvs[] >~ [`ev_block _ _ _ _ _ _ _ = OK t`]
  >- (`?u. inv_ev_trace orc p d fuel ctx executed s u /\
           ev_step orc p d fuel ctx term u = OK t /\ ~t.vs_halted` by
        metis_tac[inv_block_trace_OK] >>
      `inv_ev_trace orc p d fuel ctx ordered s u` by
        (irule inv_lookup_body_replay >> metis_tac[]) >>
      metis_tac[inv_block_trace_OK]) >>
  `?u. inv_ev_trace orc p d fuel ctx executed s u /\
       ev_step orc p d fuel ctx term u = IntRet vals t` by
    metis_tac[inv_block_trace_IntRet] >>
  `inv_ev_trace orc p d fuel ctx ordered s u` by
    (irule inv_lookup_body_replay >> metis_tac[]) >>
  metis_tac[inv_block_trace_IntRet]
QED
