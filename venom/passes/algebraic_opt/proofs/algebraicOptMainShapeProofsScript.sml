Theory algebraicOptMainShapeProofs
Ancestors
  algebraicOptShapeProofs algebraicOptDefs algebraicOptSupplyProofs
  venomWf venomInst venomFnScheduleRunner irSupply rtaSupplyProofs
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

Theorem ao_transform_inst_supply_keys:
  !s fr s1 inst.
    ir_supply_inst_ok s /\ ao_alloc_fresh s = (fr,s1) ==>
    set (MAP (\i. i.inst_id)
      (ao_transform_inst dfg ra lbl idx targets fr inst)) SUBSET
      ({inst.inst_id} UNION
        (set s1.irs_used_inst_ids DIFF set s.irs_used_inst_ids)) /\
    set (FLAT (MAP (\i. i.inst_outputs)
      (ao_transform_inst dfg ra lbl idx targets fr inst))) SUBSET
      (set inst.inst_outputs UNION
        (set s1.irs_used_vars DIFF set s.irs_used_vars))
Proof
  rpt gen_tac >> strip_tac >>
  `fr "not" = fr "inner"` by
    (drule ao_alloc_fresh_tags >> disch_then (qspec_then `"not"` mp_tac) >> simp[]) >>
  `fr "xor" = fr "inner"` by
    (drule ao_alloc_fresh_tags >> disch_then (qspec_then `"xor"` mp_tac) >> simp[]) >>
  `ao_rewrite_layout inst fr
    (ao_transform_inst dfg ra lbl idx targets fr inst)` by
      simp[ao_transform_inst_layout] >>
  drule ao_rewrite_layout_ids >> strip_tac >>
  drule ao_rewrite_layout_outputs >> strip_tac >>
  drule_all ao_alloc_fresh_contract >> strip_tac >>
  gvs[SUBSET_DEF] >> metis_tac[]
QED

Theorem ao_transform_insts_supply_keys:
  !insts s idx outs s'.
    ir_supply_inst_ok s /\
    ao_transform_insts_supply dfg ra lbl targets s idx insts = (outs,s') ==>
    set (MAP (\i. i.inst_id) outs) SUBSET
      (set (MAP (\i. i.inst_id) insts) UNION
        (set s'.irs_used_inst_ids DIFF set s.irs_used_inst_ids)) /\
    set (FLAT (MAP (\i. i.inst_outputs) outs)) SUBSET
      (set (FLAT (MAP (\i. i.inst_outputs) insts)) UNION
        (set s'.irs_used_vars DIFF set s.irs_used_vars))
Proof
  Induct >> simp[Once ao_transform_insts_supply_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `ao_alloc_fresh s` >> rename1 `ao_alloc_fresh s = (fr,s1)` >>
  Cases_on `ao_transform_insts_supply dfg ra lbl targets s1 (SUC idx) insts` >>
  rename1 `ao_transform_insts_supply dfg ra lbl targets s1 (SUC idx) insts = (tail,s2)` >>
  gvs[Once ao_transform_insts_supply_def] >>
  drule_all ao_alloc_fresh_contract >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule_all ao_transform_insts_supply_mono >> strip_tac >>
  drule_all ao_transform_inst_supply_keys >>
  strip_tac >>
  gvs[MAP_APPEND, FLAT_APPEND, SUBSET_DEF] >> metis_tac[]
QED

Theorem ao_transform_insts_supply_distinct:
  !insts s idx outs s'.
    ir_supply_inst_ok s /\
    set (MAP (\i. i.inst_id) insts) SUBSET set s.irs_used_inst_ids /\
    set (FLAT (MAP (\i. i.inst_outputs) insts)) SUBSET set s.irs_used_vars /\
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) insts)) /\
    ao_transform_insts_supply dfg ra lbl targets s idx insts = (outs,s') ==>
    ALL_DISTINCT (MAP (\i. i.inst_id) outs) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) outs))
Proof
  Induct >> simp[Once ao_transform_insts_supply_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `ao_alloc_fresh s` >> rename1 `ao_alloc_fresh s = (fr,s1)` >>
  Cases_on `ao_transform_insts_supply dfg ra lbl targets s1 (SUC idx) insts` >>
  rename1 `ao_transform_insts_supply dfg ra lbl targets s1 (SUC idx) insts = (tail,s2)` >>
  gvs[Once ao_transform_insts_supply_def] >>
  `ir_supply_inst_ok s1 /\
   set s.irs_used_inst_ids SUBSET set s1.irs_used_inst_ids /\
   set s.irs_used_vars SUBSET set s1.irs_used_vars` by
    (drule_all ao_alloc_fresh_contract >> strip_tac >> gvs[SUBSET_DEF]) >>
  `set (MAP (\i. i.inst_id) insts) SUBSET set s1.irs_used_inst_ids /\
   set (FLAT (MAP (\i. i.inst_outputs) insts)) SUBSET set s1.irs_used_vars` by
    (gvs[SUBSET_DEF] >> metis_tac[]) >>
  gvs[ALL_DISTINCT_APPEND] >>
  first_x_assum drule_all >> strip_tac >>
  `MEM h.inst_id s.irs_used_inst_ids /\
   set h.inst_outputs SUBSET set s.irs_used_vars` by
    (gvs[SUBSET_DEF] >> metis_tac[]) >>
  drule_all ao_transform_inst_supply_distinct >> strip_tac >>
  drule_all ao_transform_insts_supply_keys >> strip_tac >>
  drule_all ao_transform_inst_supply_keys >> strip_tac >>
  gvs[SUBSET_DEF] >> metis_tac[]
QED

Theorem ao_transform_block_supply_keys:
  ir_supply_inst_ok s /\
  ao_transform_block_supply dfg ra targets s bb = (bb',s') ==>
  set (MAP (\i. i.inst_id) bb'.bb_instructions) SUBSET
    (set (MAP (\i. i.inst_id) bb.bb_instructions) UNION
      (set s'.irs_used_inst_ids DIFF set s.irs_used_inst_ids)) /\
  set (FLAT (MAP (\i. i.inst_outputs) bb'.bb_instructions)) SUBSET
    (set (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) UNION
      (set s'.irs_used_vars DIFF set s.irs_used_vars))
Proof
  Cases_on `ao_transform_insts_supply dfg ra bb.bb_label targets s 0
    bb.bb_instructions` >>
  gvs[ao_transform_block_supply_def] >> strip_tac >> gvs[] >>
  metis_tac[ao_transform_insts_supply_keys]
QED

Theorem ao_transform_block_supply_distinct:
  ir_supply_inst_ok s /\
  set (MAP (\i. i.inst_id) bb.bb_instructions) SUBSET set s.irs_used_inst_ids /\
  set (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) SUBSET set s.irs_used_vars /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) /\
  ao_transform_block_supply dfg ra targets s bb = (bb',s') ==>
  ALL_DISTINCT (MAP (\i. i.inst_id) bb'.bb_instructions) /\
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb'.bb_instructions))
Proof
  Cases_on `ao_transform_insts_supply dfg ra bb.bb_label targets s 0
    bb.bb_instructions` >>
  gvs[ao_transform_block_supply_def] >> strip_tac >> gvs[] >>
  metis_tac[ao_transform_insts_supply_distinct]
QED

Theorem ao_transform_blocks_supply_keys:
  !bbs s bbs' s'.
    ir_supply_inst_ok s /\
    ao_transform_blocks_supply dfg ra targets s bbs = (bbs',s') ==>
    set (MAP (\i. i.inst_id) (fn_insts_blocks bbs')) SUBSET
      (set (MAP (\i. i.inst_id) (fn_insts_blocks bbs)) UNION
        (set s'.irs_used_inst_ids DIFF set s.irs_used_inst_ids)) /\
    set (FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs'))) SUBSET
      (set (FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs))) UNION
        (set s'.irs_used_vars DIFF set s.irs_used_vars))
Proof
  Induct >> simp[Once ao_transform_blocks_supply_def, fn_insts_blocks_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `ao_transform_block_supply dfg ra targets s h` >>
  rename1 `ao_transform_block_supply dfg ra targets s h = (bb,s1)` >>
  Cases_on `ao_transform_blocks_supply dfg ra targets s1 bbs` >>
  rename1 `ao_transform_blocks_supply dfg ra targets s1 bbs = (tail,s2)` >>
  gvs[Once ao_transform_blocks_supply_def, fn_insts_blocks_def] >>
  drule_all ao_transform_block_supply_mono >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule_all ao_transform_blocks_supply_mono >> strip_tac >>
  drule_all ao_transform_block_supply_keys >> strip_tac >>
  gvs[MAP_APPEND, FLAT_APPEND, SUBSET_DEF] >> metis_tac[]
QED

Theorem ao_transform_blocks_supply_distinct:
  !bbs s bbs' s'.
    ir_supply_inst_ok s /\
    set (MAP (\i. i.inst_id) (fn_insts_blocks bbs)) SUBSET set s.irs_used_inst_ids /\
    set (FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs))) SUBSET set s.irs_used_vars /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts_blocks bbs)) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs))) /\
    ao_transform_blocks_supply dfg ra targets s bbs = (bbs',s') ==>
    ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts_blocks bbs')) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs')))
Proof
  Induct >> simp[Once ao_transform_blocks_supply_def, fn_insts_blocks_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `ao_transform_block_supply dfg ra targets s h` >>
  rename1 `ao_transform_block_supply dfg ra targets s h = (bb,s1)` >>
  Cases_on `ao_transform_blocks_supply dfg ra targets s1 bbs` >>
  rename1 `ao_transform_blocks_supply dfg ra targets s1 bbs = (tail,s2)` >>
  gvs[Once ao_transform_blocks_supply_def, fn_insts_blocks_def,
      MAP_APPEND, FLAT_APPEND, ALL_DISTINCT_APPEND] >>
  drule_all ao_transform_block_supply_mono >> strip_tac >>
  `set (MAP (\i. i.inst_id) (fn_insts_blocks bbs)) SUBSET set s1.irs_used_inst_ids /\
   set (FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs))) SUBSET set s1.irs_used_vars` by
    (gvs[SUBSET_DEF] >> metis_tac[]) >>
  first_x_assum drule_all >> strip_tac >>
  drule_all ao_transform_block_supply_distinct >> strip_tac >>
  drule_all ao_transform_blocks_supply_keys >> strip_tac >>
  drule_all ao_transform_block_supply_keys >> strip_tac >>
  gvs[SUBSET_DEF] >> metis_tac[]
QED

Theorem ao_offset_function_key_contract:
  !fn fn0 sup.
    wf_function fn /\ wf_ssa fn /\ ir_supply_covers_fn sup fn /\
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks ==>
    ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn0)) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn0))) /\
    set (MAP (\i. i.inst_id) (fn_insts fn0)) SUBSET set sup.irs_used_inst_ids /\
    set (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn0))) SUBSET set sup.irs_used_vars
Proof
  rpt gen_tac >> strip_tac >>
  drule ao_offset_function_ids_outputs >> strip_tac >>
  gvs[wf_function_def, wf_ssa_def, ssa_form_def,
      fn_inst_ids_distinct_def, ir_supply_covers_fn_def,
      fn_ir_inst_ids_def, fn_ir_vars_def, list_subset_def,
      fn_insts_def, fn_insts_blocks_inst_ids, block_ir_inst_ids_def,
      SUBSET_DEF, EVERY_MEM] >>
  conj_tac
  >- gvs[lambdify block_ir_inst_ids_def] >>
  metis_tac[fn_insts_blocks_outputs_ir_vars]
QED

Theorem ao_main_function_distinct:
  !fn fn0 sup bbs sup1 mid.
    wf_function fn /\ wf_ssa fn /\ ir_supply_inst_ok sup /\
    ir_supply_covers_fn sup fn /\
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    ao_transform_blocks_supply (dfg_build_function fn0) (range_analyze fn0)
      (ao_compute_fn_iszero_targets fn0) sup fn0.fn_blocks = (bbs,sup1) /\
    mid = fn0 with fn_blocks := bbs ==>
    ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts mid)) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (fn_insts mid)))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all ao_offset_function_key_contract >> strip_tac >>
  gvs[fn_insts_def] >>
  metis_tac[ao_transform_blocks_supply_distinct]
QED

Theorem ao_main_function_output_support:
  !fn fn0 sup bbs sup1 mid.
    ir_supply_inst_ok sup /\
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    ao_transform_blocks_supply (dfg_build_function fn0) (range_analyze fn0)
      (ao_compute_fn_iszero_targets fn0) sup fn0.fn_blocks = (bbs,sup1) /\
    mid = fn0 with fn_blocks := bbs ==>
    set (FLAT (MAP (\i. i.inst_outputs) (fn_insts mid))) SUBSET
      (set (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn))) UNION
        (set sup1.irs_used_vars DIFF set sup.irs_used_vars))
Proof
  rpt gen_tac >> strip_tac >>
  drule ao_offset_function_ids_outputs >> strip_tac >>
  drule_all ao_transform_blocks_supply_keys >> strip_tac >>
  gvs[fn_insts_def]
QED

Theorem ao_main_function_labels:
  !fn fn0 sup bbs sup1 mid.
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    ao_transform_blocks_supply (dfg_build_function fn0) (range_analyze fn0)
      (ao_compute_fn_iszero_targets fn0) sup fn0.fn_blocks = (bbs,sup1) /\
    mid = fn0 with fn_blocks := bbs ==>
    fn_labels mid = fn_labels fn /\ fn_entry_label mid = fn_entry_label fn
Proof
  rpt gen_tac >> strip_tac >>
  drule ao_transform_blocks_supply_labels >> strip_tac >>
  `MAP (\bb. bb.bb_label) bbs = MAP (\bb. bb.bb_label) fn.fn_blocks` by
    gvs[MAP_MAP_o, combinTheory.o_DEF] >>
  qpat_x_assum `ao_transform_blocks_supply _ _ _ _ _ = _` kall_tac >>
  conj_tac >- gvs[fn_labels_def] >>
  gvs[fn_entry_label_def, entry_block_def, MAP_MAP_o, combinTheory.o_DEF] >>
  Cases_on `bbs` >> Cases_on `fn.fn_blocks` >> fs[]
QED
