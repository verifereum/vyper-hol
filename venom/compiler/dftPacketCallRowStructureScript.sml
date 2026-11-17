Theory dftPacketCallRowStructure
Ancestors
  dftRunRel dftStructural dftScheduleOrder dftCorrectness venomWfProps
  list rich_list sorting venomWf phiTransform

Theorem packet_from_block_singleton[local]:
  ALL_DISTINCT (MAP (\i:instruction. i.inst_id) bi) /\ MEM x bi /\
  from_block bi y /\ x.inst_id = y.inst_id ==> from_block [x] y
Proof
  simp[from_block_def] >> rpt strip_tac >> gvs[] >>
  `x = j` by metis_tac[all_distinct_map_mem_inj,flip_operands_inst_id] >>
  gvs[]
QED

Theorem dft_packet_row_schedule:
  !bi xs ys.
    ALL_DISTINCT (MAP (\i:instruction. i.inst_id) bi) /\
    EVERY (\x. MEM x bi) xs /\ EVERY (from_block bi) ys /\
    PERM (MAP (\i. i.inst_id) xs) (MAP (\i. i.inst_id) ys) ==>
    ?rho. PERM rho (COUNT_LIST (LENGTH xs)) /\
      LENGTH xs = LENGTH ys /\
      LIST_REL (\q y. q < LENGTH xs /\
        y.inst_id = (EL q xs).inst_id /\ from_block [EL q xs] y) rho ys
Proof
  rpt gen_tac >> strip_tac >>
  `LIST_REL (\q id. q < LENGTH xs /\ id = (EL q xs).inst_id)
     (COUNT_LIST (LENGTH xs)) (MAP (\i. i.inst_id) xs)` by
    simp[LIST_REL_EL_EQN,EL_MAP,EL_COUNT_LIST,LENGTH_COUNT_LIST] >>
  drule_all LIST_REL_PERM >> strip_tac >>
  qexists_tac `l4` >> conj_tac >- metis_tac[PERM_SYM] >>
  `LENGTH xs = LENGTH ys` by metis_tac[PERM_LENGTH,LENGTH_MAP] >>
  simp[] >> gvs[LIST_REL_EL_EQN,EL_MAP] >>
  gen_tac >> strip_tac >>
  first_x_assum (qspec_then `n` mp_tac) >> simp[] >> strip_tac >> simp[] >>
  irule packet_from_block_singleton >> simp[] >>
  qexists_tac `bi` >> simp[] >> gvs[EVERY_EL]
QED

Theorem dft_packet_paired_row_structure:
  dft_fn_rel sf tf /\ lookup_block lbl sf.fn_blocks = SOME bb /\
  lookup_block lbl tf.fn_blocks = SOME bt ==>
  ?ps xs ys rho.
    bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
    bt.bb_label = bb.bb_label /\
    EVERY (\i. is_pseudo i.inst_opcode) ps /\
    EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
    EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
    LENGTH xs = LENGTH ys /\ PERM rho (COUNT_LIST (LENGTH xs)) /\
    LIST_REL (\q y. q < LENGTH xs /\
      y.inst_id = (EL q xs).inst_id /\ from_block [EL q xs] y) rho ys /\
    ALL_DISTINCT (MAP (\i. i.inst_id) xs) /\
    EVERY inst_wf bb.bb_instructions
Proof
  strip_tac >> drule_all dft_fn_rel_lookup_order >> strip_tac >>
  `MEM bb sf.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `wf_function sf /\ pseudos_prefix bb /\ EVERY inst_wf bb.bb_instructions` by
    (gvs[dft_fn_rel_def,fn_pseudos_prefix_def,fn_inst_wf_def,EVERY_MEM] >> metis_tac[]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[bb_inst_ids_distinct] >>
  drule (iffLR pseudos_prefix_split) >> strip_tac >>
  rename1 `bb.bb_instructions = ps ++ xs` >>
  `FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions = ps /\
   FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions = xs` by
    (simp[FILTER_APPEND_DISTRIB] >>
     `FILTER (\i. is_pseudo i.inst_opcode) ps = ps /\
      FILTER (\i. is_pseudo i.inst_opcode) xs = [] /\
      FILTER (\i. ~is_pseudo i.inst_opcode) ps = [] /\
      FILTER (\i. ~is_pseudo i.inst_opcode) xs = xs` by
       (simp[FILTER_EQ_ID,FILTER_EQ_NIL] >> gvs[EVERY_MEM]) >> simp[]) >>
  drule dft_block_rel_normal >> simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `bt.bb_instructions = ps ++ ys` >>
  `EVERY (\i. ~is_pseudo i.inst_opcode) ys` by
    simp[Abbr `ys`,EVERY_FILTER] >>
  `?rho. PERM rho (COUNT_LIST (LENGTH xs)) /\ LENGTH xs = LENGTH ys /\
    LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
      from_block [EL q xs] y) rho ys` by
    (irule dft_packet_row_schedule >>
     reverse conj_tac >- metis_tac[PERM_SYM] >>
     qexists_tac `bb.bb_instructions` >> simp[] >> gvs[EVERY_MEM]) >>
  rename1 `PERM schedule (COUNT_LIST (LENGTH xs))` >>
  qexistsl [`ps`,`xs`,`ys`,`schedule`] >> simp[] >> gvs[ALL_DISTINCT_APPEND]
QED
