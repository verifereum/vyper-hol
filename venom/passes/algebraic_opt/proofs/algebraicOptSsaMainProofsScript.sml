Theory algebraicOptSsaMainProofs
Ancestors
  algebraicOptDefs algebraicOptSupplyProofs algebraicOptShapeProofs venomInst
  list pred_set

Theorem ao_transform_inst_supply_coverage:
  ao_alloc_fresh s = (fr,t) /\
  set inst.inst_outputs SUBSET set s.irs_used_vars /\
  inst.inst_id < s.irs_next_inst ==>
  set (FLAT (MAP (\i. i.inst_outputs)
    (ao_transform_inst dfg ra lbl idx targets fr inst))) SUBSET set t.irs_used_vars /\
  EVERY (\i. i.inst_id < t.irs_next_inst)
    (ao_transform_inst dfg ra lbl idx targets fr inst)
Proof
  rpt gen_tac >> strip_tac >> drule ao_alloc_fresh_props >> strip_tac >>
  drule ao_transform_inst_layout >>
  disch_then (qspecl_then [`targets`,`ra`,`lbl`,`inst`,`idx`,`dfg`] mp_tac) >>
  simp[ao_rewrite_layout_def] >> strip_tac >> gvs[MAP_EQ_CONS, SUBSET_DEF] >>
  metis_tac[MEM]
QED

Theorem ao_transform_inst_supply_frame:
  !s fr t inst V K.
  ao_alloc_fresh s = (fr,t) /\
  ALL_DISTINCT inst.inst_outputs /\
  inst.inst_id < s.irs_next_inst /\
  set inst.inst_outputs SUBSET set s.irs_used_vars /\
  V SUBSET set s.irs_used_vars /\
  (!k. k IN K ==> k < s.irs_next_inst) /\
  DISJOINT V (set inst.inst_outputs) /\
  inst.inst_id NOTIN K ==>
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs)
    (ao_transform_inst dfg ra lbl idx targets fr inst))) /\
  ALL_DISTINCT (MAP (\i. i.inst_id)
    (ao_transform_inst dfg ra lbl idx targets fr inst)) /\
  DISJOINT V (set (FLAT (MAP (\i. i.inst_outputs)
    (ao_transform_inst dfg ra lbl idx targets fr inst)))) /\
  DISJOINT K (set (MAP (\i. i.inst_id)
    (ao_transform_inst dfg ra lbl idx targets fr inst)))
Proof
  rpt gen_tac >> strip_tac >> drule ao_alloc_fresh_props >> strip_tac >>
  drule ao_transform_inst_layout >>
  disch_then (qspecl_then [`targets`,`ra`,`lbl`,`inst`,`idx`,`dfg`] mp_tac) >>
  simp[ao_rewrite_layout_def] >> strip_tac >>
  gvs[MAP_EQ_CONS, SUBSET_DEF, DISJOINT_DEF, EXTENSION] >>
  rpt (qpat_x_assum `[_] = _.inst_outputs` (assume_tac o SYM)) >>
  gvs[] >> rpt conj_tac >> rpt gen_tac >>
  metis_tac[prim_recTheory.LESS_REFL, prim_recTheory.LESS_SUC]
QED

Theorem ao_transform_insts_supply_frame:
  !xs s idx ys t V K.
    ao_transform_insts_supply dfg ra lbl targets s idx xs = (ys,t) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) xs)) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) xs) /\
    set (FLAT (MAP (\i. i.inst_outputs) xs)) SUBSET set s.irs_used_vars /\
    EVERY (\i. i.inst_id < s.irs_next_inst) xs /\
    V SUBSET set s.irs_used_vars /\
    (!k. k IN K ==> k < s.irs_next_inst) /\
    DISJOINT V (set (FLAT (MAP (\i. i.inst_outputs) xs))) /\
    DISJOINT K (set (MAP (\i. i.inst_id) xs)) ==>
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) ys)) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) ys) /\
    set (FLAT (MAP (\i. i.inst_outputs) ys)) SUBSET set t.irs_used_vars /\
    EVERY (\i. i.inst_id < t.irs_next_inst) ys /\
    DISJOINT V (set (FLAT (MAP (\i. i.inst_outputs) ys))) /\
    DISJOINT K (set (MAP (\i. i.inst_id) ys))
Proof
  Induct >- simp[ao_transform_insts_supply_def] >>
  pop_assum (mk_asm "ih") >> rpt gen_tac >>
  pure_rewrite_tac[Once ao_transform_insts_supply_def, LET_THM] >> BETA_TAC >>
  Cases_on `ao_alloc_fresh s` >>
  rename1 `ao_alloc_fresh s = (fr,s1)` >>
  Cases_on `ao_transform_insts_supply dfg ra lbl targets s1 (SUC idx) xs` >>
  rename1 `ao_transform_insts_supply dfg ra lbl targets s1 (SUC idx) xs = (zs,t1)` >>
  simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `head ++ zs = ys` >>
  gvs[ALL_DISTINCT_APPEND] >>
  `ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) head)) /\
   ALL_DISTINCT (MAP (\i. i.inst_id) head) /\
   DISJOINT (V UNION set (FLAT (MAP (\i. i.inst_outputs) xs)))
     (set (FLAT (MAP (\i. i.inst_outputs) head))) /\
   DISJOINT (K' UNION set (MAP (\i. i.inst_id) xs))
     (set (MAP (\i. i.inst_id) head))` by
    (qunabbrev_tac `head` >> irule ao_transform_inst_supply_frame >>
     simp[DISJOINT_SYM, DISJOINT_DEF, EXTENSION] >>
     conj_tac >- (gvs[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
     qexistsl [`s`,`s1`] >>
     gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS, SUBSET_DEF] >>
     metis_tac[]) >>
  `set (FLAT (MAP (\i. i.inst_outputs) head)) SUBSET set s1.irs_used_vars /\
   EVERY (\i. i.inst_id < s1.irs_next_inst) head` by
    (qunabbrev_tac `head` >> irule ao_transform_inst_supply_coverage >>
     qexists `s` >> simp[]) >>
  drule (cj 1 ao_alloc_fresh_bounds) >> strip_tac >>
  drule (cj 9 ao_alloc_fresh_bounds) >> strip_tac >>
  asm_x "ih" (drule_then (qspecl_then
    [`V UNION set (FLAT (MAP (\i. i.inst_outputs) head))`,
     `K' UNION set (MAP (\i. i.inst_id) head)`] mp_tac)) >>
  impl_tac >-
    (gvs[DISJOINT_DEF, EXTENSION, SUBSET_DEF, EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
     rpt conj_tac >> rpt gen_tac >>
     metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  strip_tac >> drule ao_transform_insts_supply_used_vars >> strip_tac >>
  gvs[DISJOINT_DEF, EXTENSION, SUBSET_DEF, EVERY_MEM] >>
  rpt conj_tac >> rpt gen_tac >>
  metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]
QED

Theorem ao_transform_block_supply_frame:
  !s bb bb' t V K.
    ao_transform_block_supply dfg ra targets s bb = (bb',t) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    set (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) SUBSET set s.irs_used_vars /\
    EVERY (\i. i.inst_id < s.irs_next_inst) bb.bb_instructions /\
    V SUBSET set s.irs_used_vars /\
    (!k. k IN K ==> k < s.irs_next_inst) /\
    DISJOINT V (set (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))) /\
    DISJOINT K (set (MAP (\i. i.inst_id) bb.bb_instructions)) ==>
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb'.bb_instructions)) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb'.bb_instructions) /\
    set (FLAT (MAP (\i. i.inst_outputs) bb'.bb_instructions)) SUBSET set t.irs_used_vars /\
    EVERY (\i. i.inst_id < t.irs_next_inst) bb'.bb_instructions /\
    DISJOINT V (set (FLAT (MAP (\i. i.inst_outputs) bb'.bb_instructions))) /\
    DISJOINT K (set (MAP (\i. i.inst_id) bb'.bb_instructions))
Proof
  rpt gen_tac >> rewrite_tac[ao_transform_block_supply_def] >>
  Cases_on `ao_transform_insts_supply dfg ra bb.bb_label targets s 0 bb.bb_instructions` >>
  simp[] >> strip_tac >> gvs[] >>
  drule ao_transform_insts_supply_frame >>
  disch_then (qspecl_then [`V`,`K'`] mp_tac) >> simp[]
QED

Theorem ao_transform_blocks_supply_frame:
  !bbs s bbs' t V K.
    ao_transform_blocks_supply dfg ra targets s bbs = (bbs',t) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs))) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts_blocks bbs)) /\
    set (FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs))) SUBSET set s.irs_used_vars /\
    EVERY (\i. i.inst_id < s.irs_next_inst) (fn_insts_blocks bbs) /\
    V SUBSET set s.irs_used_vars /\
    (!k. k IN K ==> k < s.irs_next_inst) /\
    DISJOINT V (set (FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs)))) /\
    DISJOINT K (set (MAP (\i. i.inst_id) (fn_insts_blocks bbs))) ==>
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs'))) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts_blocks bbs')) /\
    set (FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs'))) SUBSET set t.irs_used_vars /\
    EVERY (\i. i.inst_id < t.irs_next_inst) (fn_insts_blocks bbs') /\
    DISJOINT V (set (FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs')))) /\
    DISJOINT K (set (MAP (\i. i.inst_id) (fn_insts_blocks bbs')))
Proof
  Induct >- simp[ao_transform_blocks_supply_def, fn_insts_blocks_def] >>
  pop_assum (mk_asm "ih") >> rpt gen_tac >>
  pure_rewrite_tac[Once ao_transform_blocks_supply_def, LET_THM] >> BETA_TAC >>
  Cases_on `ao_transform_block_supply dfg ra targets s h` >>
  rename1 `ao_transform_block_supply dfg ra targets s h = (bb,s1)` >>
  Cases_on `ao_transform_blocks_supply dfg ra targets s1 bbs` >>
  rename1 `ao_transform_blocks_supply dfg ra targets s1 bbs = (bs,t1)` >>
  simp[fn_insts_blocks_def, MAP_APPEND, ALL_DISTINCT_APPEND] >> strip_tac >> gvs[] >>
  drule ao_transform_block_supply_frame >>
  disch_then (qspecl_then
    [`V UNION set (FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs)))`,
     `K' UNION set (MAP (\i. i.inst_id) (fn_insts_blocks bbs))`] mp_tac) >>
  impl_tac >-
    (gvs[DISJOINT_DEF, EXTENSION, EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
     metis_tac[]) >>
  strip_tac >> drule ao_transform_block_supply_used_vars >> strip_tac >>
  asm_x "ih" (drule_then (qspecl_then
    [`V UNION set (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))`,
     `K' UNION set (MAP (\i. i.inst_id) bb.bb_instructions)`] mp_tac)) >>
  impl_tac >-
    (gvs[DISJOINT_DEF, EXTENSION, SUBSET_DEF, EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
     rpt conj_tac >> rpt gen_tac >>
     metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  strip_tac >> drule ao_transform_blocks_supply_used_vars >> strip_tac >>
  gvs[fn_insts_blocks_def, MAP_APPEND, ALL_DISTINCT_APPEND,
      DISJOINT_DEF, EXTENSION, SUBSET_DEF, EVERY_MEM] >>
  rpt conj_tac >> rpt gen_tac >>
  metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]
QED
