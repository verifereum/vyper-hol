Theory algebraicOptMainShapeProofs
Ancestors
  algebraicOptShapeProofs algebraicOptDefs algebraicOptSupplyProofs
  venomWf venomInst venomFnScheduleRunner irSupply
Libs
  listTheory pred_setTheory

Theorem ao_handle_offset_inst_wf:
  inst_wf inst ==> inst_wf (ao_handle_offset_inst inst)
Proof
  Cases_on `inst.inst_opcode = ADD` >>
  simp[ao_handle_offset_inst_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `h` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `h` >> simp[] >>
  Cases_on `t'` >> simp[inst_wf_def]
QED

Theorem ao_offset_blocks_insts:
  !bbs.
    fn_insts_blocks
      (MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) bbs) =
    MAP ao_handle_offset_inst (fn_insts_blocks bbs)
Proof
  Induct >> simp[fn_insts_blocks_def, MAP_APPEND]
QED

Theorem ao_offset_function_insts:
  fn0 = fn with fn_blocks :=
    MAP (\bb. bb with bb_instructions :=
      MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks ==>
  fn_insts fn0 = MAP ao_handle_offset_inst (fn_insts fn)
Proof
  strip_tac >> gvs[fn_insts_def, ao_offset_blocks_insts]
QED

Theorem ao_offset_function_inst_wf:
  fn_inst_wf fn /\
  fn0 = fn with fn_blocks :=
    MAP (\bb. bb with bb_instructions :=
      MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks ==>
  fn_inst_wf fn0
Proof
  strip_tac >> gvs[fn_inst_wf_def, MEM_MAP] >>
  rpt strip_tac >> gvs[MEM_MAP] >> metis_tac[ao_handle_offset_inst_wf]
QED

Theorem ao_offset_function_ids_outputs:
  fn0 = fn with fn_blocks :=
    MAP (\bb. bb with bb_instructions :=
      MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks ==>
  MAP (\i. i.inst_id) (fn_insts fn0) = MAP (\i. i.inst_id) (fn_insts fn) /\
  MAP (\i. i.inst_outputs) (fn_insts fn0) =
    MAP (\i. i.inst_outputs) (fn_insts fn)
Proof
  strip_tac >> drule ao_offset_function_insts >>
  simp[MAP_MAP_o, combinTheory.o_DEF, ao_handle_offset_inst_shape]
QED

Theorem ao_transform_insts_supply_unary:
  !insts s idx outs s'.
    EVERY inst_wf insts /\
    ao_transform_insts_supply dfg ra lbl targets s idx insts = (outs,s') ==>
    EVERY (\out.
      (out.inst_opcode = ISZERO ==>
        LENGTH out.inst_operands = 1 /\ LENGTH out.inst_outputs = 1) /\
      (out.inst_opcode = ASSERT ==> LENGTH out.inst_operands = 1)) outs
Proof
  Induct >> simp[Once ao_transform_insts_supply_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `ao_alloc_fresh s` >> rename1 `ao_alloc_fresh s = (fr,s1)` >>
  Cases_on `ao_transform_insts_supply dfg ra lbl targets s1 (SUC idx) insts` >>
  rename1 `ao_transform_insts_supply dfg ra lbl targets s1 (SUC idx) insts = (tail,s2)` >>
  gvs[Once ao_transform_insts_supply_def, EVERY_APPEND] >>
  first_x_assum drule_all >> strip_tac >>
  simp[EVERY_MEM] >> metis_tac[ao_transform_inst_unary]
QED

Theorem ao_transform_block_supply_unary:
  EVERY inst_wf bb.bb_instructions /\
  ao_transform_block_supply dfg ra targets s bb = (bb',s') ==>
  EVERY (\out.
    (out.inst_opcode = ISZERO ==>
      LENGTH out.inst_operands = 1 /\ LENGTH out.inst_outputs = 1) /\
    (out.inst_opcode = ASSERT ==> LENGTH out.inst_operands = 1))
    bb'.bb_instructions
Proof
  Cases_on `ao_transform_insts_supply dfg ra bb.bb_label targets s 0
    bb.bb_instructions` >>
  gvs[ao_transform_block_supply_def] >> strip_tac >> gvs[] >>
  metis_tac[ao_transform_insts_supply_unary]
QED

Theorem ao_transform_blocks_supply_unary:
  !bbs s bbs' s'.
    EVERY (\bb. EVERY inst_wf bb.bb_instructions) bbs /\
    ao_transform_blocks_supply dfg ra targets s bbs = (bbs',s') ==>
    EVERY (\out.
      (out.inst_opcode = ISZERO ==>
        LENGTH out.inst_operands = 1 /\ LENGTH out.inst_outputs = 1) /\
      (out.inst_opcode = ASSERT ==> LENGTH out.inst_operands = 1))
      (fn_insts_blocks bbs')
Proof
  Induct >> simp[Once ao_transform_blocks_supply_def, fn_insts_blocks_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `ao_transform_block_supply dfg ra targets s h` >>
  rename1 `ao_transform_block_supply dfg ra targets s h = (bb,s1)` >>
  Cases_on `ao_transform_blocks_supply dfg ra targets s1 bbs` >>
  rename1 `ao_transform_blocks_supply dfg ra targets s1 bbs = (tail,s2)` >>
  gvs[Once ao_transform_blocks_supply_def, fn_insts_blocks_def, EVERY_APPEND] >>
  first_x_assum drule_all >> strip_tac >>
  metis_tac[ao_transform_block_supply_unary]
QED

Theorem ao_main_function_unary:
  !fn fn0 sup bbs sup1 mid. fn_inst_wf fn /\
  fn0 = fn with fn_blocks :=
    MAP (\bb. bb with bb_instructions :=
      MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
  ao_transform_blocks_supply (dfg_build_function fn0) (range_analyze fn0)
    (ao_compute_fn_iszero_targets fn0) sup fn0.fn_blocks = (bbs,sup1) /\
  mid = fn0 with fn_blocks := bbs ==>
  EVERY (\out.
    (out.inst_opcode = ISZERO ==>
      LENGTH out.inst_operands = 1 /\ LENGTH out.inst_outputs = 1) /\
    (out.inst_opcode = ASSERT ==> LENGTH out.inst_operands = 1)) (fn_insts mid)
Proof
  rpt gen_tac >> strip_tac >>
  `fn_inst_wf fn0` by metis_tac[ao_offset_function_inst_wf] >>
  `EVERY (\bb. EVERY inst_wf bb.bb_instructions) fn0.fn_blocks` by
    (gvs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  drule_all ao_transform_blocks_supply_unary >>
  gvs[fn_insts_def]
QED

Theorem ao_transform_block_supply_label:
  ao_transform_block_supply dfg ra targets s bb = (bb',s') ==>
  bb'.bb_label = bb.bb_label
Proof
  Cases_on `ao_transform_insts_supply dfg ra bb.bb_label targets s 0
    bb.bb_instructions` >>
  simp[ao_transform_block_supply_def] >> strip_tac >> gvs[]
QED

Theorem ao_transform_blocks_supply_labels:
  !bbs s bbs' s'.
    ao_transform_blocks_supply dfg ra targets s bbs = (bbs',s') ==>
    MAP (\bb. bb.bb_label) bbs' = MAP (\bb. bb.bb_label) bbs
Proof
  Induct >> simp[Once ao_transform_blocks_supply_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `ao_transform_block_supply dfg ra targets s h` >>
  rename1 `ao_transform_block_supply dfg ra targets s h = (bb,s1)` >>
  Cases_on `ao_transform_blocks_supply dfg ra targets s1 bbs` >>
  rename1 `ao_transform_blocks_supply dfg ra targets s1 bbs = (tail,s2)` >>
  gvs[Once ao_transform_blocks_supply_def] >>
  first_x_assum drule >> simp[] >>
  metis_tac[ao_transform_block_supply_label]
QED
