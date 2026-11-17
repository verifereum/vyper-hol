Theory dftPacketFirstBodyObservation
Ancestors
  dftPacketSuccessorObservation dftPacketPseudoSegment dftPacketLiteralRowExtend
  dftPacketSameLevelCompose dftGasFromListReplayBoundary dftGasInvMemoryObservation
  dftRunRel dftScheduleOrder dftWf dftGasInvForwardActive
  o1ScheduleDecompHelpers venomExecProps venomWf venomInst venomState
  dftPacketFreshRow dftGasInvCrossingProbe list rich_list sorting

Theorem first_body_invoke_memory_order[local]:
  !x y. x.inst_opcode = INVOKE /\ inv_memory_observation y.inst_opcode ==>
    dft_must_order x y
Proof
  rpt gen_tac >> Cases_on `y.inst_opcode` >>
  simp[inv_memory_observation_def, dft_must_order_def,
       venomEffectsTheory.read_effects_def, venomEffectsTheory.write_effects_def,
       venomEffectsTheory.all_effects_def, is_terminator_def,
       pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem dft_packet_first_body_schedule:
  !sf tf bb bt ps xs ys rho q.
  dft_fn_rel sf tf /\
  lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
  lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
  bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
  EVERY (\x. is_pseudo x.inst_opcode) ps /\
  EVERY (\x. ~is_pseudo x.inst_opcode) xs /\
  EVERY (\x. ~is_pseudo x.inst_opcode) ys /\
  LENGTH xs = LENGTH ys /\ PERM rho (COUNT_LIST (LENGTH xs)) /\
  LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
    from_block [EL q xs] y) rho ys /\
  ys <> [] /\ q = EL 0 rho /\ inv_memory_observation (HD ys).inst_opcode ==>
  q < LENGTH xs /\ EL q xs = HD ys /\
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
  EVERY (\i. i.inst_opcode <> INVOKE) (TAKE q xs)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `q < LENGTH xs /\ from_block [EL q xs] (HD ys)` by
    (fs[LIST_REL_EL_EQN] >> first_x_assum (qspec_then `0` mp_tac) >>
     `0 < LENGTH ys` by (Cases_on `ys` >> fs[]) >> simp[EL,HD]) >>
  qpat_x_assum `q = EL 0 _` kall_tac >>
  `EL q xs = HD ys` by
    (drule_all inv_memory_observation_original >> simp[]) >>
  `wf_function sf` by fs[dft_fn_rel_def] >>
  `MEM bb sf.fn_blocks` by
    metis_tac[FIND_MEM, lookup_block_def] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[wf_fn_block_inst_ids_distinct] >>
  drule_all dft_fn_rel_lookup_order >> strip_tac >>
  `FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions = ps /\
   FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions = xs` by
    (`FILTER (\i. is_pseudo i.inst_opcode) ps = ps /\
      FILTER (\i. is_pseudo i.inst_opcode) xs = [] /\
      FILTER (\i. ~is_pseudo i.inst_opcode) ps = [] /\
      FILTER (\i. ~is_pseudo i.inst_opcode) xs = xs` by
       simp[FILTER_EQ_ID, FILTER_EQ_NIL] >> simp[FILTER_APPEND_DISTRIB]) >>
  simp[] >> conj_tac
  >- (rewrite_tac[EVERY_EL] >> qx_gen_tac `n` >> disch_tac >>
      `n < q /\ n < LENGTH xs` by (gvs[LENGTH_TAKE] >> decide_tac) >>
      simp[EL_TAKE] >> irule dft_wf_order_nonterminator >>
      qexistsl_tac [`bb`, `sf`, `EL q xs`] >> simp[] >>
      conj_tac >- metis_tac[MEM_EL, MEM_APPEND] >>
      irule id_before_append_right >> simp[id_before_def] >>
      qexistsl_tac [`n`, `q`] >> simp[EL_MAP]) >>
  suspend "no_invoke"
QED

Resume dft_packet_first_body_schedule[no_invoke]:
  simp[EVERY_EL,LENGTH_TAKE,EL_TAKE] >> rpt strip_tac >>
  rename1 `(EL r xs).inst_opcode = INVOKE` >>
  `r < LENGTH xs` by decide_tac >>
  `MEM (EL r xs) bb.bb_instructions /\ MEM (EL q xs) bb.bb_instructions` by
    metis_tac[MEM_EL, MEM_APPEND] >>
  `~is_pseudo (EL r xs).inst_opcode /\ ~is_pseudo (EL q xs).inst_opcode` by
    (fs[EVERY_EL] >> metis_tac[]) >>
  `id_before (MAP (\i. i.inst_id) bb.bb_instructions)
     (EL r xs).inst_id (EL q xs).inst_id` by
    (simp[] >> irule id_before_append_right >> simp[id_before_def] >>
     qexistsl_tac [`r`, `q`] >> simp[EL_MAP]) >>
  `dft_must_order (EL r xs) (EL q xs)` by
    metis_tac[first_body_invoke_memory_order] >>
  `id_before (MAP (\i. i.inst_id) bt.bb_instructions)
     (EL r xs).inst_id (EL q xs).inst_id` by
    (qpat_x_assum `dft_block_rel bb bt`
       (strip_assume_tac o REWRITE_RULE [dft_block_rel_def]) >>
     fs[] >> irule id_before_append_right >> metis_tac[]) >>
  `~MEM (EL r xs).inst_id (MAP (\i. i.inst_id) ps) /\
   ~MEM (EL q xs).inst_id (MAP (\i. i.inst_id) ps)` by
    (`MEM (EL r xs).inst_id (MAP (\i. i.inst_id) xs) /\
      MEM (EL q xs).inst_id (MAP (\i. i.inst_id) xs)` by
       (conj_tac >> simp[MEM_MAP] >> metis_tac[MEM_EL]) >>
     qpat_x_assum `ALL_DISTINCT (MAP _ bb.bb_instructions)` mp_tac >>
     asm_rewrite_tac[MAP_APPEND, ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  `id_before (MAP (\i. i.inst_id) ys) (EL r xs).inst_id (HD ys).inst_id` by
    (qpat_x_assum `id_before (MAP _ bt.bb_instructions) _ _` mp_tac >>
     gvs[id_before_append_suffix]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) xs)` by
    (qpat_x_assum `ALL_DISTINCT (MAP _ bb.bb_instructions)` mp_tac >>
     simp[MAP_APPEND,ALL_DISTINCT_APPEND]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) ys)` by
    (qpat_x_assum `dft_block_rel bb bt`
       (strip_assume_tac o REWRITE_RULE [dft_block_rel_def]) >>
     fs[] >> metis_tac[ALL_DISTINCT_PERM]) >>
  qpat_x_assum `id_before (MAP _ ys) _ (HD ys).inst_id` mp_tac >>
  qpat_x_assum `ALL_DISTINCT (MAP _ ys)` mp_tac >>
  rpt (pop_assum kall_tac) >> Cases_on `ys` >> simp[id_before_def] >>
  rpt strip_tac >> Cases_on `j` >> gvs[] >>
  spose_not_then strip_assume_tac >>
  `n < LENGTH (MAP (\i. i.inst_id) t)` by simp[] >>
  drule_then assume_tac EL_MEM >> metis_tac[]
QED

Finalise dft_packet_first_body_schedule
