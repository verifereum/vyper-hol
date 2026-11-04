Theory algebraicOptSsaMainProofs
Ancestors
  algebraicOptDefs algebraicOptSsaSupplyProofs algebraicOptOutputShapeProofs
Libs
  listTheory pred_setTheory

Theorem ao_transform_insts_supply_mono:
  !xs s idx ys t.
    ao_transform_insts_supply dfg ra lbl targets s idx xs = (ys,t) ==>
    set s.irs_used_vars SUBSET set t.irs_used_vars /\
    s.irs_next_inst <= t.irs_next_inst
Proof
  Induct >> simp[ao_transform_insts_supply_def] >> rpt gen_tac >>
  Cases_on `ao_alloc_fresh s` >>
  rename1 `ao_alloc_fresh s = (fr,s1)` >>
  Cases_on `ao_transform_insts_supply dfg ra lbl targets s1 (SUC idx) xs` >>
  simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule ao_alloc_fresh_bounds >> strip_tac >>
  metis_tac[SUBSET_TRANS, arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem ao_transform_block_supply_mono:
  ao_transform_block_supply dfg ra targets s bb = (bb',t) ==>
  set s.irs_used_vars SUBSET set t.irs_used_vars /\
  s.irs_next_inst <= t.irs_next_inst
Proof
  rewrite_tac[ao_transform_block_supply_def] >>
  Cases_on `ao_transform_insts_supply dfg ra bb.bb_label targets s 0 bb.bb_instructions` >>
  simp[] >> strip_tac >> drule ao_transform_insts_supply_mono >> simp[]
QED

Theorem ao_transform_blocks_supply_mono:
  !bbs s bbs' t.
    ao_transform_blocks_supply dfg ra targets s bbs = (bbs',t) ==>
    set s.irs_used_vars SUBSET set t.irs_used_vars /\
    s.irs_next_inst <= t.irs_next_inst
Proof
  Induct >> simp[ao_transform_blocks_supply_def] >> rpt gen_tac >>
  Cases_on `ao_transform_block_supply dfg ra targets s h` >>
  rename1 `ao_transform_block_supply dfg ra targets s h = (bb,s1)` >>
  Cases_on `ao_transform_blocks_supply dfg ra targets s1 bbs` >>
  simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule ao_transform_block_supply_mono >> strip_tac >>
  metis_tac[SUBSET_TRANS, arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem ao_transform_inst_supply_coverage:
  ao_alloc_fresh s = (fr,t) /\
  set inst.inst_outputs SUBSET set s.irs_used_vars /\
  inst.inst_id < s.irs_next_inst ==>
  set (FLAT (MAP (\i. i.inst_outputs)
    (ao_transform_inst dfg ra lbl idx targets fr inst))) SUBSET set t.irs_used_vars /\
  EVERY (\i. i.inst_id < t.irs_next_inst)
    (ao_transform_inst dfg ra lbl idx targets fr inst)
Proof
  strip_tac >> drule ao_alloc_fresh_contract >> strip_tac >>
  drule ao_transform_inst_projection >>
  disch_then (qspecl_then [`targets`,`ra`,`lbl`,`inst`,`idx`,`dfg`] mp_tac) >>
  simp[] >> strip_tac >> gvs[MAP_EQ_CONS, SUBSET_DEF] >>
  metis_tac[MEM]
QED
