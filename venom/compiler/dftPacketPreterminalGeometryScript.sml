Theory dftPacketPreterminalGeometry
Ancestors
  dftRunRel dftStructural dftCorrectness dftWf venomWf venomInst
  venomExecProps list rich_list sorting arithmetic

Theorem packet_body_shape[local]:
  !bb ps xs. bb_well_formed bb /\ bb.bb_instructions = ps ++ xs /\
    EVERY (\i. is_pseudo i.inst_opcode) ps ==>
    xs <> [] /\ is_terminator (LAST xs).inst_opcode /\
    EVERY (\i. ~is_terminator i.inst_opcode) (FRONT xs)
Proof
  rpt gen_tac >> strip_tac >>
  `!op. is_pseudo op ==> ~is_terminator op` by
    (Cases >> simp[is_pseudo_def, is_terminator_def]) >>
  `xs <> []` by
    (spose_not_then assume_tac >> gvs[bb_well_formed_def] >>
     `MEM (LAST bb.bb_instructions) bb.bb_instructions` by metis_tac[LAST_MEM] >>
     gvs[EVERY_MEM] >> metis_tac[]) >>
  fs[bb_well_formed_def] >>
  conj_tac >- metis_tac[LAST_APPEND_NOT_NIL] >>
  simp[EVERY_EL] >> rpt strip_tac >>
  `EL n (FRONT xs) = EL n xs` by metis_tac[FRONT_EL] >>
  qpat_x_assum `!i. i < _ /\ is_terminator _ ==> _`
    (qspec_then `LENGTH ps + n` mp_tac) >>
  gvs[LENGTH_FRONT, EL_APPEND2] >> decide_tac
QED

Theorem packet_preterminal_schedule[local]:
  !xs ys schedule (ct:num).
  ALL_DISTINCT (MAP (\i:instruction. i.inst_id) xs) /\
  PERM schedule (COUNT_LIST (LENGTH xs)) /\
  LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
    from_block [EL q xs] y) schedule ys /\
  ct + 1 = LENGTH ys /\ EL ct ys = LAST xs /\ LENGTH xs = LENGTH ys ==>
  !q. q < ct ==> MEM q (TAKE ct schedule)
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH schedule = LENGTH ys` by metis_tac[LIST_REL_LENGTH] >>
  `ct < LENGTH ys` by decide_tac >>
  `EL ct schedule = ct` by
    (qpat_assum `LIST_REL _ _ _` (mp_tac o SRULE [LIST_REL_EL_EQN]) >>
     strip_tac >> first_x_assum (qspec_then `ct` mp_tac) >> simp[] >>
     strip_tac >>
     `xs <> []` by (strip_tac >> gvs[]) >>
     `EL (EL ct schedule) (MAP (\i. i.inst_id) xs) =
      LAST (MAP (\i. i.inst_id) xs)` by simp[EL_MAP, LAST_MAP] >>
     qspecl_then [`MAP (\i. i.inst_id) xs`,`EL ct schedule`] mp_tac
       ALL_DISTINCT_LAST_EL_IFF >> simp[] >> decide_tac) >>
  rpt strip_tac >>
  `MEM q schedule` by metis_tac[PERM_MEM_EQ, MEM_COUNT_LIST, LESS_TRANS] >>
  fs[MEM_EL] >> rename1 `k < LENGTH schedule` >>
  `k < ct` by (Cases_on `k = ct` >> gvs[] >> decide_tac) >>
  simp[MEM_EL] >> qexists `k` >> simp[EL_TAKE]
QED

Theorem dft_packet_preterminal_geometry:
  !sf tf bb bt ps xs ys rho (count:num) inst.
  dft_fn_rel sf tf /\
  lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
  lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
  bb_well_formed bb /\ bb_well_formed bt /\
  bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
  EVERY (\i. is_pseudo i.inst_opcode) ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
  LENGTH xs = LENGTH ys /\ PERM rho (COUNT_LIST (LENGTH xs)) /\
  LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
    from_block [EL q xs] y) rho ys /\
  count < LENGTH ys /\ inst = EL count ys /\ is_terminator inst.inst_opcode ==>
  ?ordered executed.
    xs = ordered ++ [inst] /\ ys = executed ++ [inst] /\
    count = LENGTH executed /\ LENGTH ordered = LENGTH executed /\
    EVERY (\i. ~is_terminator i.inst_opcode) ordered /\
    EVERY (\i. ~is_terminator i.inst_opcode) executed /\
    ps = FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions /\
    EVERY (from_block bb.bb_instructions) executed /\
    (!q. q < LENGTH ordered ==> MEM q (TAKE count rho)) /\
    inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE
Proof
  map_every qx_gen_tac [`sf`,`tf`,`bb`,`bt`,`ps`,`xs`,`ys`,`schedule`,`ct`,`inst`] >>
  strip_tac >>
  `wf_function sf` by fs[dft_fn_rel_def] >>
  `MEM bb sf.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[wf_fn_block_inst_ids_distinct] >>
  drule_all dft_fn_rel_lookup_order >> strip_tac >>
  `LAST bt.bb_instructions = LAST bb.bb_instructions` by
    metis_tac[dft_block_rel_last] >>
  `xs <> [] /\ ys <> [] /\
   EVERY (\i. ~is_terminator i.inst_opcode) (FRONT xs) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (FRONT ys)` by
    metis_tac[packet_body_shape] >>
  `ct + 1 = LENGTH ys` by
    (qpat_assum `bb_well_formed bt` mp_tac >>
     qpat_assum `bt.bb_instructions = ps ++ ys` mp_tac >>
     qpat_assum `ct < LENGTH ys` mp_tac >>
     qpat_assum `inst = EL ct ys` mp_tac >>
     qpat_assum `is_terminator inst.inst_opcode` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     fs[bb_well_formed_def] >>
     qpat_x_assum `!i. _ ==> _` (qspec_then `LENGTH ps + ct` mp_tac) >>
     simp[EL_APPEND2] >> decide_tac) >>
  `inst = LAST xs /\ inst = LAST ys` by
    (qpat_x_assum `LAST bt.bb_instructions = LAST bb.bb_instructions` mp_tac >>
     `ct = PRE (LENGTH ys)` by decide_tac >>
     simp[LAST_APPEND_NOT_NIL, GSYM LAST_EL]) >>
  `EVERY (from_block bb.bb_instructions) (FRONT ys)` by
    (pure_rewrite_tac[EVERY_MEM] >> qx_gen_tac `v` >> strip_tac >>
     `MEM v ys` by metis_tac[MEM_FRONT_NOT_NIL] >>
     drule_all LIST_REL_MEM_IMP_R >> strip_tac >>
     gvs[from_block_def] >>
     qexists `EL x xs` >> simp[] >> metis_tac[EL_MEM]) >>
  `ps = FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions` by
    (`FILTER (\i. is_pseudo i.inst_opcode) ps = ps` by simp[FILTER_EQ_ID] >>
     `FILTER (\i. is_pseudo i.inst_opcode) xs = []` by
       simp[FILTER_EQ_NIL, GSYM EVERY_MEM] >>
     simp[FILTER_APPEND]) >>
  `xs = FRONT xs ++ [inst] /\ ys = FRONT ys ++ [inst]` by
    metis_tac[APPEND_FRONT_LAST] >>
  `inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE` by
    (rpt strip_tac >> fs[is_terminator_def]) >>
  qexistsl [`FRONT xs`, `FRONT ys`] >>
  qpat_x_assum `ps = FILTER _ _` (fn th => rewrite_tac[GSYM th]) >>
  simp[LENGTH_FRONT] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) xs)` by
    (qpat_x_assum `ALL_DISTINCT _` mp_tac >> simp[ALL_DISTINCT_APPEND]) >>
  `!q. q < ct ==> MEM q (TAKE ct schedule)` by
    metis_tac[packet_preterminal_schedule] >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED
