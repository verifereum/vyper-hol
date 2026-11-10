Theory algebraicOptMainShapeProofs
Ancestors
  algebraicOptShapeProofs algebraicOptDefs algebraicOptSupplyProofs
  venomWf venomInst venomFnScheduleRunner irSupply rtaSupplyProofs
  unitShapeDefs stackPlanTypes list pred_set

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

Theorem ao_compute_iszero_step_chain_property:
  (!v chain. ALOOKUP targets v = SOME chain ==> EVERY P chain) /\
  (inst.inst_opcode = ISZERO ==>
    EVERY P inst.inst_operands /\ EVERY (P o Var) inst.inst_outputs) ==>
  !v chain. ALOOKUP (ao_compute_iszero_step targets inst) v = SOME chain ==>
    EVERY P chain
Proof
  strip_tac >>
  Cases_on `inst.inst_opcode = ISZERO`
  >- (Cases_on `inst.inst_operands`
      >- (gvs[ao_compute_iszero_step_def] >> metis_tac[]) >>
      Cases_on `t`
      >- (Cases_on `inst.inst_outputs`
          >- (gvs[ao_compute_iszero_step_def] >> metis_tac[]) >>
          Cases_on `t`
          >- (Cases_on `h`
              >- (gvs[ao_compute_iszero_step_def, AllCaseEqs(), EVERY_SNOC,
                      combinTheory.o_DEF] >> rpt strip_tac >> gvs[] >> metis_tac[]) 
              >- (Cases_on `ALOOKUP targets s` >>
                  gvs[ao_compute_iszero_step_def, AllCaseEqs(), EVERY_SNOC,
                      combinTheory.o_DEF] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
              gvs[ao_compute_iszero_step_def, AllCaseEqs(), EVERY_SNOC,
                  combinTheory.o_DEF] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
          (gvs[ao_compute_iszero_step_def] >> metis_tac[])) >>
      (Cases_on `inst.inst_outputs`
       >- (gvs[ao_compute_iszero_step_def] >> metis_tac[]) >>
       Cases_on `t` >> gvs[ao_compute_iszero_step_def] >> metis_tac[])) >>
  (gvs[ao_compute_iszero_step_def] >> metis_tac[])
QED

Theorem ao_compute_iszero_fold_chain_property:
  !insts targets.
    (!v chain. ALOOKUP targets v = SOME chain ==> EVERY P chain) /\
    EVERY (\inst. inst.inst_opcode = ISZERO ==>
      EVERY P inst.inst_operands /\ EVERY (P o Var) inst.inst_outputs) insts ==>
    !v chain. ALOOKUP (FOLDL ao_compute_iszero_step targets insts) v = SOME chain ==>
      EVERY P chain
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum match_mp_tac >> simp[] >>
  metis_tac[ao_compute_iszero_step_chain_property]
QED

Theorem ao_compute_iszero_targets_chain_property:
  EVERY (\inst. inst.inst_opcode = ISZERO ==>
    EVERY P inst.inst_operands /\ EVERY (P o Var) inst.inst_outputs) insts ==>
  !v chain. ALOOKUP (ao_compute_iszero_targets insts) v = SOME chain ==>
    EVERY P chain
Proof
  strip_tac >> simp[ao_compute_iszero_targets_def] >>
  match_mp_tac ao_compute_iszero_fold_chain_property >> simp[]
QED

Theorem ao_compute_iszero_targets_support:
  EVERY (\inst. set (inst_ir_vars inst) SUBSET V) insts ==>
  !v chain op. ALOOKUP (ao_compute_iszero_targets insts) v = SOME chain /\
    MEM op chain ==> set (venomInst$operand_vars [op]) SUBSET V
Proof
  strip_tac >>
  `EVERY (\inst. inst.inst_opcode = ISZERO ==>
     EVERY (\op. set (venomInst$operand_vars [op]) SUBSET V) inst.inst_operands /\
     EVERY ((\op. set (venomInst$operand_vars [op]) SUBSET V) o Var)
       inst.inst_outputs) insts` by
    (gvs[EVERY_MEM] >> gen_tac >> strip_tac >>
     `set inst.inst_outputs SUBSET V /\ set (inst_uses inst) SUBSET V` by
       (gvs[inst_ir_vars_def, SUBSET_DEF] >> metis_tac[]) >>
     strip_tac >> conj_tac
     >- (qpat_x_assum `set (inst_uses _) SUBSET _` mp_tac >>
         rewrite_tac[inst_uses_def] >>
         pure_once_rewrite_tac[ao_operand_support] >> simp[EVERY_MEM]) >>
     gvs[EVERY_MEM, combinTheory.o_DEF, venomInstTheory.operand_vars_def,
         venomInstTheory.operand_var_def, SUBSET_DEF]) >>
  drule ao_compute_iszero_targets_chain_property >>
  simp[EVERY_MEM] >> metis_tac[]
QED

Theorem ao_transform_inst_supply_vars:
  !s fr s1 inst.
    ir_supply_inst_ok s /\ ao_alloc_fresh s = (fr,s1) /\
    set (inst_ir_vars inst) SUBSET set s.irs_used_vars /\
    (!v chain op. ALOOKUP targets v = SOME chain /\ MEM op chain ==>
      set (venomInst$operand_vars [op]) SUBSET set s.irs_used_vars) ==>
    EVERY (\out. set (inst_ir_vars out) SUBSET set s1.irs_used_vars)
      (ao_transform_inst dfg ra lbl idx targets fr inst)
Proof
  rpt gen_tac >> strip_tac >>
  `fr "not" = fr "inner" /\ fr "xor" = fr "inner"` by
    (conj_tac
     >- (drule ao_alloc_fresh_tags >> disch_then (qspec_then `"not"` mp_tac) >> simp[]) >>
     drule ao_alloc_fresh_tags >> disch_then (qspec_then `"xor"` mp_tac) >> simp[]) >>
  `set (inst_uses inst) SUBSET set s.irs_used_vars /\
   set inst.inst_outputs SUBSET set s.irs_used_vars` by
    gvs[inst_ir_vars_def, SUBSET_DEF] >>
  drule_all ao_transform_inst_supply_keys >> strip_tac >>
  `!out. MEM out (ao_transform_inst dfg ra lbl idx targets fr inst) ==>
    set (inst_uses out) SUBSET
      (set s.irs_used_vars UNION {SND (fr "not"); SND (fr "iz")})` by
    (match_mp_tac ao_transform_inst_support >> simp[] >> metis_tac[]) >>
  drule_all ao_alloc_fresh_contract >> strip_tac >>
  gvs[EVERY_MEM, inst_ir_vars_def, SUBSET_DEF, MEM_FLAT, MEM_MAP] >>
  metis_tac[]
QED

Theorem ao_transform_insts_supply_vars:
  !insts s idx outs s'.
    ir_supply_inst_ok s /\
    EVERY (\inst. set (inst_ir_vars inst) SUBSET set s.irs_used_vars) insts /\
    (!v chain op. ALOOKUP targets v = SOME chain /\ MEM op chain ==>
      set (venomInst$operand_vars [op]) SUBSET set s.irs_used_vars) /\
    ao_transform_insts_supply dfg ra lbl targets s idx insts = (outs,s') ==>
    EVERY (\out. set (inst_ir_vars out) SUBSET set s'.irs_used_vars) outs
Proof
  Induct >> simp[Once ao_transform_insts_supply_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `ao_alloc_fresh s` >> rename1 `ao_alloc_fresh s = (fr,s1)` >>
  Cases_on `ao_transform_insts_supply dfg ra lbl targets s1 (SUC idx) insts` >>
  rename1 `ao_transform_insts_supply dfg ra lbl targets s1 (SUC idx) insts = (tail,s2)` >>
  gvs[Once ao_transform_insts_supply_def, EVERY_APPEND] >>
  `ir_supply_inst_ok s1 /\ set s.irs_used_vars SUBSET set s1.irs_used_vars` by
    (drule_all ao_alloc_fresh_contract >> strip_tac >> gvs[SUBSET_DEF]) >>
  `EVERY (\inst. set (inst_ir_vars inst) SUBSET set s1.irs_used_vars) insts /\
   (!v chain op. ALOOKUP targets v = SOME chain /\ MEM op chain ==>
      set (venomInst$operand_vars [op]) SUBSET set s1.irs_used_vars)` by
    (gvs[EVERY_MEM, SUBSET_DEF] >> metis_tac[]) >>
  first_x_assum drule_all >> strip_tac >>
  drule_all ao_transform_inst_supply_vars >> strip_tac >>
  drule_all ao_transform_insts_supply_mono >> strip_tac >>
  gvs[EVERY_MEM, SUBSET_DEF] >> metis_tac[]
QED

Theorem ao_transform_block_supply_vars:
  ir_supply_inst_ok s /\
  EVERY (\inst. set (inst_ir_vars inst) SUBSET set s.irs_used_vars) bb.bb_instructions /\
  (!v chain op. ALOOKUP targets v = SOME chain /\ MEM op chain ==>
    set (venomInst$operand_vars [op]) SUBSET set s.irs_used_vars) /\
  ao_transform_block_supply dfg ra targets s bb = (bb',s') ==>
  EVERY (\out. set (inst_ir_vars out) SUBSET set s'.irs_used_vars) bb'.bb_instructions
Proof
  Cases_on `ao_transform_insts_supply dfg ra bb.bb_label targets s 0
    bb.bb_instructions` >>
  gvs[ao_transform_block_supply_def] >> strip_tac >> gvs[] >>
  metis_tac[ao_transform_insts_supply_vars]
QED

Theorem ao_transform_blocks_supply_vars:
  !bbs s bbs' s'.
    ir_supply_inst_ok s /\
    EVERY (\inst. set (inst_ir_vars inst) SUBSET set s.irs_used_vars)
      (fn_insts_blocks bbs) /\
    (!v chain op. ALOOKUP targets v = SOME chain /\ MEM op chain ==>
      set (venomInst$operand_vars [op]) SUBSET set s.irs_used_vars) /\
    ao_transform_blocks_supply dfg ra targets s bbs = (bbs',s') ==>
    EVERY (\out. set (inst_ir_vars out) SUBSET set s'.irs_used_vars)
      (fn_insts_blocks bbs')
Proof
  Induct >> simp[Once ao_transform_blocks_supply_def, fn_insts_blocks_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `ao_transform_block_supply dfg ra targets s h` >>
  rename1 `ao_transform_block_supply dfg ra targets s h = (bb,s1)` >>
  Cases_on `ao_transform_blocks_supply dfg ra targets s1 bbs` >>
  rename1 `ao_transform_blocks_supply dfg ra targets s1 bbs = (tail,s2)` >>
  gvs[Once ao_transform_blocks_supply_def, fn_insts_blocks_def, EVERY_APPEND] >>
  drule_all ao_transform_block_supply_mono >> strip_tac >>
  `EVERY (\inst. set (inst_ir_vars inst) SUBSET set s1.irs_used_vars)
     (fn_insts_blocks bbs) /\
   (!v chain op. ALOOKUP targets v = SOME chain /\ MEM op chain ==>
      set (venomInst$operand_vars [op]) SUBSET set s1.irs_used_vars)` by
    (gvs[EVERY_MEM, SUBSET_DEF] >> metis_tac[]) >>
  first_x_assum drule_all >> strip_tac >>
  drule_all ao_transform_block_supply_vars >> strip_tac >>
  drule_all ao_transform_blocks_supply_mono >> strip_tac >>
  gvs[EVERY_MEM, SUBSET_DEF] >> metis_tac[]
QED

Theorem ao_offset_function_vars:
  !fn fn0 sup.
    ir_supply_covers_fn sup fn /\
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks ==>
    EVERY (\inst. set (inst_ir_vars inst) SUBSET set sup.irs_used_vars) (fn_insts fn0)
Proof
  rpt gen_tac >> strip_tac >>
  drule ao_offset_function_insts >> strip_tac >>
  gvs[EVERY_MEM, MEM_MAP, ir_supply_covers_fn_def, list_subset_def,
      fn_ir_vars_def, fn_insts_def] >>
  rpt strip_tac >> gvs[inst_ir_vars_def, ao_handle_offset_inst_shape, SUBSET_DEF] >>
  rpt strip_tac >>
  qpat_x_assum `!x. MEM x (FLAT (MAP block_ir_vars _)) ==> _` irule >>
  gvs[unitShapeDefsTheory.MEM_fn_insts_blocks_iff,
      MEM_FLAT, MEM_MAP, block_ir_vars_def, inst_ir_vars_def] >>
  simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  metis_tac[inst_ir_vars_def, MEM_APPEND]
QED

Theorem ao_main_function_vars:
  !fn fn0 sup bbs sup1 mid.
    ir_supply_inst_ok sup /\ ir_supply_covers_fn sup fn /\
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    ao_transform_blocks_supply (dfg_build_function fn0) (range_analyze fn0)
      (ao_compute_fn_iszero_targets fn0) sup fn0.fn_blocks = (bbs,sup1) /\
    mid = fn0 with fn_blocks := bbs ==>
    EVERY (\inst. set (inst_ir_vars inst) SUBSET set sup1.irs_used_vars) (fn_insts mid)
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `ir_supply_inst_ok supply` >>
  drule_all ao_offset_function_vars >> strip_tac >>
  drule ao_compute_iszero_targets_support >> strip_tac >>
  `!v chain op. ALOOKUP (ao_compute_fn_iszero_targets fn0) v = SOME chain /\
    MEM op chain ==> set (venomInst$operand_vars [op]) SUBSET set supply.irs_used_vars` by
    (rewrite_tac[ao_compute_fn_iszero_targets_def] >> metis_tac[]) >>
  gvs[fn_insts_def] >>
  drule_all ao_transform_blocks_supply_vars >> simp[]
QED

Theorem ao_compute_iszero_targets_no_labels:
  EVERY label_positions_ok insts ==>
  !v chain op. ALOOKUP (ao_compute_iszero_targets insts) v = SOME chain /\
    MEM op chain ==> ~is_label_operand op
Proof
  strip_tac >>
  `EVERY (\inst. inst.inst_opcode = ISZERO ==>
     EVERY (\op. ~is_label_operand op) inst.inst_operands /\
     EVERY ((\op. ~is_label_operand op) o Var) inst.inst_outputs) insts` by
    (gvs[EVERY_MEM, combinTheory.o_DEF,
         stackPlanTypesTheory.is_label_operand_def] >> rpt strip_tac >>
     `label_positions_ok inst` by metis_tac[] >>
     gvs[label_positions_ok_def, EVERY_MEM]) >>
  drule ao_compute_iszero_targets_chain_property >>
  simp[EVERY_MEM] >> metis_tac[]
QED

Theorem ao_transform_insts_supply_noncontrol:
  !insts s idx outs s'.
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> PHI) insts /\
    ao_transform_insts_supply dfg ra lbl targets s idx insts = (outs,s') ==>
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> PHI) outs
Proof
  Induct >> simp[Once ao_transform_insts_supply_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `ao_alloc_fresh s` >> rename1 `ao_alloc_fresh s = (fr,s1)` >>
  Cases_on `ao_transform_insts_supply dfg ra lbl targets s1 (SUC idx) insts` >>
  gvs[Once ao_transform_insts_supply_def, EVERY_APPEND] >>
  metis_tac[ao_transform_inst_noncontrol]
QED

Theorem ao_transform_insts_supply_nonempty:
  !insts s idx outs s'.
    ao_transform_insts_supply dfg ra lbl targets s idx insts = (outs,s') ==>
    (outs = [] <=> insts = [])
Proof
  Cases >> simp[Once ao_transform_insts_supply_def] >>
  rpt gen_tac >>
  Cases_on `ao_alloc_fresh s` >>
  Cases_on `ao_transform_insts_supply dfg ra lbl targets r (SUC idx) t` >>
  simp[Once ao_transform_insts_supply_def] >>
  metis_tac[ao_transform_inst_nonempty]
QED

Theorem ao_transform_insts_supply_last:
  !insts s idx outs s'.
    insts <> [] /\
    ao_transform_insts_supply dfg ra lbl targets s idx insts = (outs,s') ==>
    is_terminator (LAST outs).inst_opcode =
      is_terminator (LAST insts).inst_opcode /\
    ((LAST outs).inst_opcode = PHI <=> (LAST insts).inst_opcode = PHI)
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `ao_alloc_fresh s` >> rename1 `ao_alloc_fresh s = (fr,s1)` >>
  Cases_on `ao_transform_insts_supply dfg ra lbl targets s1 (SUC idx) insts` >>
  rename1 `ao_transform_insts_supply dfg ra lbl targets s1 (SUC idx) insts = (tail,s2)` >>
  gvs[Once ao_transform_insts_supply_def] >>
  Cases_on `insts = []`
  >- (gvs[] >> fs[ao_transform_insts_supply_def] >>
      metis_tac[ao_transform_inst_control]) >>
  `tail <> []` by metis_tac[ao_transform_insts_supply_nonempty] >>
  `ao_transform_inst dfg ra lbl idx targets fr h <> []` by
    metis_tac[ao_transform_inst_nonempty] >>
  simp[rich_listTheory.LAST_APPEND_NOT_NIL, LAST_DEF] >>
  first_x_assum drule_all >> simp[]
QED

Theorem ao_transform_insts_supply_successors:
  !insts s idx outs s'.
    insts <> [] /\
    (!v chain op. ALOOKUP targets v = SOME chain /\ MEM op chain ==>
       ~is_label_operand op) /\
    ao_transform_insts_supply dfg ra lbl targets s idx insts = (outs,s') ==>
    get_successors (LAST outs) = get_successors (LAST insts)
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `ao_alloc_fresh s` >> rename1 `ao_alloc_fresh s = (fr,s1)` >>
  Cases_on `ao_transform_insts_supply dfg ra lbl targets s1 (SUC idx) insts` >>
  rename1 `ao_transform_insts_supply dfg ra lbl targets s1 (SUC idx) insts = (tail,s2)` >>
  gvs[Once ao_transform_insts_supply_def] >>
  Cases_on `insts = []`
  >- (gvs[] >> fs[ao_transform_insts_supply_def] >>
      metis_tac[ao_transform_inst_successors]) >>
  `tail <> []` by metis_tac[ao_transform_insts_supply_nonempty] >>
  simp[rich_listTheory.LAST_APPEND_NOT_NIL, LAST_DEF] >>
  first_x_assum drule_all >> simp[]
QED

Theorem ao_transform_block_supply_last:
  bb.bb_instructions <> [] /\
  ao_transform_block_supply dfg ra targets s bb = (bb',s') ==>
  bb'.bb_instructions <> [] /\
  is_terminator (LAST bb'.bb_instructions).inst_opcode =
    is_terminator (LAST bb.bb_instructions).inst_opcode /\
  ((LAST bb'.bb_instructions).inst_opcode = PHI <=>
    (LAST bb.bb_instructions).inst_opcode = PHI)
Proof
  Cases_on `ao_transform_insts_supply dfg ra bb.bb_label targets s 0
    bb.bb_instructions` >>
  gvs[ao_transform_block_supply_def] >> strip_tac >> gvs[] >>
  metis_tac[ao_transform_insts_supply_nonempty, ao_transform_insts_supply_last]
QED

Theorem ao_transform_inst_phis:
  FILTER (\i. i.inst_opcode = PHI)
    (ao_transform_inst dfg ra lbl idx targets fr inst) =
  if inst.inst_opcode = PHI then [ao_resolve_iszero_inst targets inst] else []
Proof
  Cases_on `is_terminator inst.inst_opcode \/ inst.inst_opcode = PHI`
  >- (gvs[] >> simp[ao_transform_inst_control_owner,
        ao_resolve_iszero_inst_fields]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> PHI)
      (ao_transform_inst dfg ra lbl idx targets fr inst)` by
    metis_tac[ao_transform_inst_noncontrol] >>
  gvs[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]
QED

Theorem ao_transform_insts_supply_phis:
  !insts s idx outs s'.
    ao_transform_insts_supply dfg ra lbl targets s idx insts = (outs,s') ==>
    FILTER (\i. i.inst_opcode = PHI) outs =
      MAP (ao_resolve_iszero_inst targets) (FILTER (\i. i.inst_opcode = PHI) insts)
Proof
  Induct >> simp[Once ao_transform_insts_supply_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `ao_alloc_fresh s` >> rename1 `ao_alloc_fresh s = (fr,s1)` >>
  Cases_on `ao_transform_insts_supply dfg ra lbl targets s1 (SUC idx) insts` >>
  gvs[Once ao_transform_insts_supply_def, FILTER_APPEND_DISTRIB] >>
  first_x_assum drule_all >>
  simp[ao_transform_inst_phis] >> strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[]
QED

Theorem ao_transform_inst_not_terminator:
  ~is_terminator inst.inst_opcode ==>
  EVERY (\i. ~is_terminator i.inst_opcode)
    (ao_transform_inst dfg ra lbl idx targets fr inst)
Proof
  strip_tac >> Cases_on `inst.inst_opcode = PHI`
  >- simp[ao_transform_inst_control_owner, ao_resolve_iszero_inst_fields,
          is_terminator_def] >>
  drule_all ao_transform_inst_noncontrol >> simp[EVERY_MEM] >> metis_tac[]
QED

Theorem ao_transform_insts_supply_front:
  !insts s idx outs s'.
    EVERY (\i. ~is_terminator i.inst_opcode) (FRONT insts) /\
    ao_transform_insts_supply dfg ra lbl targets s idx insts = (outs,s') ==>
    EVERY (\i. ~is_terminator i.inst_opcode) (FRONT outs)
Proof
  Induct >> simp[Once ao_transform_insts_supply_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `ao_alloc_fresh s` >> rename1 `ao_alloc_fresh s = (fr,s1)` >>
  Cases_on `ao_transform_insts_supply dfg ra lbl targets s1 (SUC idx) insts` >>
  rename1 `ao_transform_insts_supply dfg ra lbl targets s1 (SUC idx) insts = (tail,s2)` >>
  gvs[Once ao_transform_insts_supply_def] >>
  Cases_on `insts = []`
  >- (gvs[] >> fs[ao_transform_insts_supply_def] >>
      qspec_then `h` mp_tac (Q.GEN `inst` (cj 1 ao_transform_inst_control)) >>
      simp[EVERY_MEM]) >>
  `tail <> []` by metis_tac[ao_transform_insts_supply_nonempty] >>
  gvs[FRONT_DEF, rich_listTheory.FRONT_APPEND_NOT_NIL, EVERY_APPEND] >>
  metis_tac[ao_transform_inst_not_terminator]
QED

Theorem ao_transform_insts_supply_labels:
  !insts s idx outs s'.
    (!v chain op. ALOOKUP targets v = SOME chain /\ MEM op chain ==>
       ~is_label_operand op) /\
    ao_transform_insts_supply dfg ra lbl targets s idx insts = (outs,s') ==>
    set (FLAT (MAP inst_ir_labels outs)) SUBSET
      set (FLAT (MAP inst_ir_labels insts))
Proof
  Induct >> simp[Once ao_transform_insts_supply_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `ao_alloc_fresh s` >> rename1 `ao_alloc_fresh s = (fr,s1)` >>
  Cases_on `ao_transform_insts_supply dfg ra lbl targets s1 (SUC idx) insts` >>
  gvs[Once ao_transform_insts_supply_def] >>
  first_x_assum drule_all >> strip_tac >>
  drule ao_transform_inst_labels >> strip_tac >>
  gvs[SUBSET_DEF, MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem ao_transform_block_supply_labels:
  (!v chain op. ALOOKUP targets v = SOME chain /\ MEM op chain ==>
     ~is_label_operand op) /\
  ao_transform_block_supply dfg ra targets s bb = (bb',s') ==>
  set (block_ir_labels bb') SUBSET set (block_ir_labels bb)
Proof
  Cases_on `ao_transform_insts_supply dfg ra bb.bb_label targets s 0
    bb.bb_instructions` >>
  gvs[ao_transform_block_supply_def] >> strip_tac >> gvs[] >>
  drule_all ao_transform_insts_supply_labels >>
  simp[block_ir_labels_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem ao_transform_blocks_supply_label_support:
  !bbs s bbs' s'.
    (!v chain op. ALOOKUP targets v = SOME chain /\ MEM op chain ==>
       ~is_label_operand op) /\
    ao_transform_blocks_supply dfg ra targets s bbs = (bbs',s') ==>
    set (FLAT (MAP block_ir_labels bbs')) SUBSET
      set (FLAT (MAP block_ir_labels bbs))
Proof
  Induct >> simp[Once ao_transform_blocks_supply_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `ao_transform_block_supply dfg ra targets s h` >>
  rename1 `ao_transform_block_supply dfg ra targets s h = (bb,s1)` >>
  Cases_on `ao_transform_blocks_supply dfg ra targets s1 bbs` >>
  gvs[Once ao_transform_blocks_supply_def] >>
  first_x_assum drule_all >> strip_tac >>
  drule_all ao_transform_block_supply_labels >>
  fs[SUBSET_DEF] >> metis_tac[]
QED

Theorem ao_handle_offset_label_positions:
  label_positions_ok inst ==> label_positions_ok (ao_handle_offset_inst inst)
Proof
  Cases_on `inst.inst_opcode = ADD` >> simp[ao_handle_offset_inst_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `h` >> simp[] >> Cases_on `t` >> simp[] >>
  Cases_on `h` >> simp[] >> Cases_on `t'` >>
  simp[label_positions_ok_def, is_label_operand_def]
QED

Theorem ao_offset_function_label_contract:
  !fn fn0.
    EVERY label_positions_ok (fn_insts fn) /\
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks ==>
    EVERY label_positions_ok (fn_insts fn0) /\
    fn_ir_labels fn0 = fn_ir_labels fn
Proof
  rpt gen_tac >> strip_tac >>
  drule ao_offset_function_insts >> strip_tac >> conj_tac
  >- (gvs[EVERY_MAP, combinTheory.o_DEF, EVERY_MEM, MEM_MAP] >>
      metis_tac[ao_handle_offset_label_positions]) >>
  gvs[fn_ir_labels_def, block_ir_labels_def, MAP_MAP_o, combinTheory.o_DEF,
      ao_handle_offset_inst_labels] >>
  simp[lambdify block_ir_labels_def, ETA_THM]
QED

Theorem ao_main_function_label_support:
  !fn fn0 supply bbs supply1 mid.
    EVERY label_positions_ok (fn_insts fn) /\
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    ao_transform_blocks_supply (dfg_build_function fn0) (range_analyze fn0)
      (ao_compute_fn_iszero_targets fn0) supply fn0.fn_blocks = (bbs,supply1) /\
    mid = fn0 with fn_blocks := bbs ==>
    set (fn_ir_labels mid) SUBSET set (fn_ir_labels fn)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all ao_offset_function_label_contract >> strip_tac >>
  drule ao_compute_iszero_targets_no_labels >> strip_tac >>
  `!v chain op. ALOOKUP (ao_compute_fn_iszero_targets fn0) v = SOME chain /\
    MEM op chain ==> ~is_label_operand op` by
    (rewrite_tac[ao_compute_fn_iszero_targets_def] >> metis_tac[]) >>
  drule_all ao_transform_blocks_supply_label_support >> strip_tac >>
  gvs[fn_ir_labels_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem ao_main_function_coverage:
  !fn fn0 supply bbs supply1 mid.
    ir_supply_inst_ok supply /\ ir_supply_covers_fn supply fn /\
    EVERY label_positions_ok (fn_insts fn) /\
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    ao_transform_blocks_supply (dfg_build_function fn0) (range_analyze fn0)
      (ao_compute_fn_iszero_targets fn0) supply fn0.fn_blocks = (bbs,supply1) /\
    mid = fn0 with fn_blocks := bbs ==>
    ir_supply_inst_ok supply1 /\ ir_supply_covers_fn supply1 mid
Proof
  rpt gen_tac >> strip_tac >>
  drule_all ao_main_function_vars >> strip_tac >>
  drule_all ao_main_function_label_support >> strip_tac >>
  drule_all ao_transform_blocks_supply_mono >> strip_tac >>
  drule_all ao_transform_blocks_supply_keys >> strip_tac >>
  drule ao_offset_function_ids_outputs >> strip_tac >>
  `set (fn_ir_inst_ids mid) SUBSET set supply1.irs_used_inst_ids` by
    (gvs[fn_ir_inst_ids_def, fn_insts_def, fn_insts_blocks_inst_ids,
       ir_supply_covers_fn_def, list_subset_def, SUBSET_DEF, EVERY_MEM] >>
     gvs[lambdify block_ir_inst_ids_def] >> metis_tac[]) >>
  gvs[ir_supply_covers_fn_def, list_subset_def, EVERY_MEM, SUBSET_DEF,
      ir_supply_inst_ok_def] >>
  qpat_x_assum `!inst. MEM inst (fn_insts _) ==> _` mp_tac >>
  rpt (pop_assum kall_tac) >>
  simp[fn_insts_def, unitShapeDefsTheory.MEM_fn_insts_blocks_iff,
       fn_ir_vars_def, block_ir_vars_def, MEM_FLAT, MEM_MAP] >>
  rpt strip_tac >> gvs[MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem ao_prefix_order_cons[local]:
  (!i j. i < j /\ j < LENGTH (h::xs) /\ P (EL j (h::xs)) ==>
     P (EL i (h::xs))) <=>
  ((!i j. i < j /\ j < LENGTH xs /\ P (EL j xs) ==> P (EL i xs)) /\
   (P h \/ EVERY (\x. ~P x) xs))
Proof
  eq_tac
  >- (strip_tac >> conj_tac
      >- (rpt strip_tac >>
          first_x_assum (qspecl_then [`SUC i`,`SUC j`] mp_tac) >> simp[]) >>
      Cases_on `P h` >> simp[EVERY_EL] >> rpt strip_tac >>
      first_x_assum (qspecl_then [`0`,`SUC n`] mp_tac) >> simp[]) >>
  strip_tac >> rpt gen_tac >>
  Cases_on `i` >> Cases_on `j` >> simp[] >>
  rpt strip_tac >> gvs[EVERY_EL] >> metis_tac[]
QED

Theorem ao_prefix_order_split:
  !xs.
  (!i j. i < j /\ j < LENGTH xs /\ P (EL j xs) ==> P (EL i xs)) <=>
  (?ps rest. xs = ps ++ rest /\ EVERY P ps /\ EVERY (\x. ~P x) rest)
Proof
  Induct >- simp[] >> gen_tac >>
  rewrite_tac[ao_prefix_order_cons] >>
  Cases_on `P h` >> simp[] >> eq_tac
  >- (strip_tac >> gvs[] >> qexistsl [`h::ps`,`rest`] >> simp[]) 
  >- (strip_tac >> Cases_on `ps` >> gvs[] >> metis_tac[]) 
  >- (strip_tac >> qexistsl [`[]`,`h::xs`] >> simp[]) >>
  strip_tac >> Cases_on `ps` >> gvs[] >>
  qexistsl [`[]`,`xs`] >> simp[]
QED

Theorem ao_transform_insts_supply_no_phis:
  EVERY (\i. i.inst_opcode <> PHI) insts /\
  ao_transform_insts_supply dfg ra lbl targets s idx insts = (outs,s') ==>
  EVERY (\i. i.inst_opcode <> PHI) outs
Proof
  strip_tac >> drule ao_transform_insts_supply_phis >>
  gvs[GSYM FILTER_EQ_NIL]
QED

Theorem ao_transform_insts_supply_phi_prefix:
  !insts s idx outs s'.
    (!i j. i < j /\ j < LENGTH insts /\ (EL j insts).inst_opcode = PHI ==>
       (EL i insts).inst_opcode = PHI) /\
    ao_transform_insts_supply dfg ra lbl targets s idx insts = (outs,s') ==>
    (!i j. i < j /\ j < LENGTH outs /\ (EL j outs).inst_opcode = PHI ==>
       (EL i outs).inst_opcode = PHI)
Proof
  Induct >- simp[ao_transform_insts_supply_def] >>
  rpt gen_tac >> strip_tac >>
  gnvs[ao_prefix_order_cons] >>
  Cases_on `ao_alloc_fresh s` >> rename1 `ao_alloc_fresh s = (fr,s1)` >>
  Cases_on `ao_transform_insts_supply dfg ra lbl targets s1 (SUC idx) insts` >>
  rename1 `ao_transform_insts_supply dfg ra lbl targets s1 (SUC idx) insts = (tail,s2)` >>
  gnvs[Once ao_transform_insts_supply_def, Excl "LENGTH_APPEND"] >>
  Cases_on `h.inst_opcode = PHI`
  >- (`ao_transform_inst dfg ra lbl idx targets fr h =
         [ao_resolve_iszero_inst targets h]` by
        (irule ao_transform_inst_control_owner >> simp[]) >>
      gvs[] >>
      qpat_x_assum `!s idx outs s'. _` (qspecl_then [`s1`,`SUC idx`,`tail`,`s'`] mp_tac) >>
      simp[] >> (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
      rpt gen_tac >> Cases_on `i` >> Cases_on `j` >>
      simp[ao_resolve_iszero_inst_fields, GSYM arithmeticTheory.ADD1] >> metis_tac[]) >>
  gvs[] >>
  `EVERY (\i. i.inst_opcode <> PHI) (h::insts)` by simp[] >>
  `EVERY (\i. i.inst_opcode <> PHI)
      (ao_transform_inst dfg ra lbl idx targets fr h ++ tail)` by
    (`ao_transform_insts_supply dfg ra lbl targets s idx (h::insts) =
        (ao_transform_inst dfg ra lbl idx targets fr h ++ tail,s')` by
       simp[Once ao_transform_insts_supply_def] >>
     metis_tac[ao_transform_insts_supply_no_phis]) >>
  qpat_x_assum `EVERY _ (_ ++ _)` mp_tac >>
  rpt (pop_assum kall_tac) >>
  pure_rewrite_tac[EVERY_EL] >> simp[] >> metis_tac[]
QED

Theorem ao_last_only_front:
  !xs.
    (!i. i < LENGTH xs /\ P (EL i xs) ==> i = PRE (LENGTH xs)) <=>
    EVERY (\x. ~P x) (FRONT xs)
Proof
  Induct >- simp[] >> gen_tac >> Cases_on `xs = []`
  >- (gvs[] >> simp[FRONT_DEF]) >>
  simp[FRONT_DEF] >>
  eq_tac
  >- (strip_tac >> conj_tac
      >- (first_x_assum (qspec_then `0` mp_tac) >> simp[] >>
          Cases_on `xs` >> gvs[]) >>
      first_x_assum (irule o iffLR) >> rpt strip_tac >>
      first_x_assum (qspec_then `SUC i` mp_tac) >>
      Cases_on `xs` >> gvs[]) >>
  strip_tac >> gen_tac >> Cases_on `i` >> simp[] >>
  first_x_assum (mp_tac o iffRL) >> simp[] >>
  Cases_on `xs` >> gvs[] >> metis_tac[]
QED

Theorem ao_transform_block_supply_well_formed:
  bb_well_formed bb /\
  ao_transform_block_supply dfg ra targets s bb = (bb',s') ==>
  bb_well_formed bb'
Proof
  strip_tac >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  drule_all ao_transform_block_supply_last >> strip_tac >>
  Cases_on `ao_transform_insts_supply dfg ra bb.bb_label targets s 0
    bb.bb_instructions` >>
  gvs[ao_transform_block_supply_def, bb_well_formed_def] >>
  gvs[ao_last_only_front] >>
  conj_tac >- metis_tac[ao_transform_insts_supply_front] >>
  metis_tac[ao_transform_insts_supply_phi_prefix]
QED

Theorem ao_offset_block_well_formed:
  bb_well_formed bb ==>
  bb_well_formed (bb with bb_instructions :=
    MAP ao_handle_offset_inst bb.bb_instructions)
Proof
  simp[bb_well_formed_def, LAST_MAP, ao_handle_offset_inst_shape, EL_MAP] >>
  rpt strip_tac >> gvs[EL_MAP, ao_handle_offset_inst_shape] >> metis_tac[]
QED

Theorem ao_transform_blocks_supply_well_formed:
  !bbs s bbs' s'.
    EVERY bb_well_formed bbs /\
    ao_transform_blocks_supply dfg ra targets s bbs = (bbs',s') ==>
    EVERY bb_well_formed bbs'
Proof
  Induct >> simp[Once ao_transform_blocks_supply_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `ao_transform_block_supply dfg ra targets s h` >>
  rename1 `ao_transform_block_supply dfg ra targets s h = (bb,s1)` >>
  Cases_on `ao_transform_blocks_supply dfg ra targets s1 bbs` >>
  gvs[Once ao_transform_blocks_supply_def] >>
  metis_tac[ao_transform_block_supply_well_formed]
QED

Theorem ao_offset_inst_successors:
  get_successors (ao_handle_offset_inst inst) = get_successors inst
Proof
  Cases_on `inst.inst_opcode = ADD` >>
  simp[ao_handle_offset_inst_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `h` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `h` >> simp[] >>
  Cases_on `t'` >> simp[get_successors_def, is_terminator_def]
QED

Theorem ao_offset_block_successors:
  bb_succs (bb with bb_instructions :=
    MAP ao_handle_offset_inst bb.bb_instructions) = bb_succs bb
Proof
  Cases_on `bb.bb_instructions` >>
  simp[bb_succs_def, LAST_DEF, LAST_MAP, ao_offset_inst_successors] >>
  Cases_on `t = []` >> simp[LAST_MAP, ao_offset_inst_successors]
QED

Theorem ao_transform_block_supply_successors:
  (!v chain op. ALOOKUP targets v = SOME chain /\ MEM op chain ==>
     ~is_label_operand op) /\
  ao_transform_block_supply dfg ra targets s bb = (bb',s') ==>
  bb_succs bb' = bb_succs bb
Proof
  Cases_on `ao_transform_insts_supply dfg ra bb.bb_label targets s 0
    bb.bb_instructions` >>
  gvs[ao_transform_block_supply_def] >> strip_tac >> gvs[] >>
  drule ao_transform_insts_supply_nonempty >> strip_tac >>
  Cases_on `bb.bb_instructions = []` >> gvs[bb_succs_def] >>
  drule_all ao_transform_insts_supply_successors >> strip_tac >>
  Cases_on `q` >> Cases_on `bb.bb_instructions` >> gvs[]
QED

Theorem ao_transform_blocks_supply_successors:
  !bbs s bbs' s'.
    (!v chain op. ALOOKUP targets v = SOME chain /\ MEM op chain ==>
       ~is_label_operand op) /\
    ao_transform_blocks_supply dfg ra targets s bbs = (bbs',s') ==>
    MAP (\bb. (bb.bb_label,bb_succs bb)) bbs' =
    MAP (\bb. (bb.bb_label,bb_succs bb)) bbs
Proof
  Induct >> simp[Once ao_transform_blocks_supply_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `ao_transform_block_supply dfg ra targets s h` >>
  rename1 `ao_transform_block_supply dfg ra targets s h = (bb,s1)` >>
  Cases_on `ao_transform_blocks_supply dfg ra targets s1 bbs` >>
  gvs[Once ao_transform_blocks_supply_def] >>
  metis_tac[ao_transform_block_supply_successors, ao_transform_block_supply_label]
QED

Theorem ao_main_function_successors:
  !fn fn0 sup bbs sup1 mid.
    EVERY label_positions_ok (fn_insts fn) /\
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    ao_transform_blocks_supply (dfg_build_function fn0) (range_analyze fn0)
      (ao_compute_fn_iszero_targets fn0) sup fn0.fn_blocks = (bbs,sup1) /\
    mid = fn0 with fn_blocks := bbs ==>
    MAP (\bb. (bb.bb_label,bb_succs bb)) mid.fn_blocks =
    MAP (\bb. (bb.bb_label,bb_succs bb)) fn.fn_blocks
Proof
  rpt gen_tac >> strip_tac >>
  drule_all ao_offset_function_label_contract >> strip_tac >>
  drule ao_compute_iszero_targets_no_labels >> strip_tac >>
  `!v chain op. ALOOKUP (ao_compute_fn_iszero_targets fn0) v = SOME chain /\
    MEM op chain ==> ~is_label_operand op` by
    (rewrite_tac[ao_compute_fn_iszero_targets_def] >> metis_tac[]) >>
  drule_all ao_transform_blocks_supply_successors >> strip_tac >>
  gvs[MAP_MAP_o, combinTheory.o_DEF, ao_offset_block_successors]
QED

Theorem ao_main_function_well_formed:
  !fn fn0 sup bbs sup1 mid.
    wf_function fn /\ wf_ssa fn /\ ir_supply_inst_ok sup /\
    ir_supply_covers_fn sup fn /\
    EVERY label_positions_ok (fn_insts fn) /\
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    ao_transform_blocks_supply (dfg_build_function fn0) (range_analyze fn0)
      (ao_compute_fn_iszero_targets fn0) sup fn0.fn_blocks = (bbs,sup1) /\
    mid = fn0 with fn_blocks := bbs ==>
    wf_function mid
Proof
  rpt gen_tac >> strip_tac >>
  drule_all ao_main_function_distinct >> strip_tac >>
  drule_all ao_main_function_labels >> strip_tac >>
  drule_all ao_main_function_successors >> strip_tac >>
  `EVERY bb_well_formed fn0.fn_blocks` by
    (gvs[EVERY_MEM, MEM_MAP] >> rpt strip_tac >> gvs[] >>
     irule ao_offset_block_well_formed >> fs[wf_function_def]) >>
  drule_all ao_transform_blocks_supply_well_formed >> strip_tac >>
  `fn_succs_closed mid` by
    (fs[fn_succs_closed_def] >> rpt strip_tac >>
     `MEM (bb.bb_label,bb_succs bb)
       (MAP (\bb. (bb.bb_label,bb_succs bb)) mid.fn_blocks)` by
       (simp[MEM_MAP] >> metis_tac[]) >>
     `MEM (bb.bb_label,bb_succs bb)
       (MAP (\bb. (bb.bb_label,bb_succs bb)) fn.fn_blocks)` by gvs[] >>
     qpat_x_assum `MEM _ (MAP _ fn.fn_blocks)` mp_tac >>
     simp[MEM_MAP] >> strip_tac >> gvs[] >>
     metis_tac[wf_function_def, fn_succs_closed_def]) >>
  gvs[wf_function_def, fn_inst_ids_distinct_def, fn_insts_def,
      MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF, EVERY_MEM] >>
  conj_tac
  >- (gvs[fn_has_entry_def, fn_labels_def] >>
      Cases_on `bbs` >> gvs[]) >>
  gvs[fn_insts_blocks_inst_ids, lambdify block_ir_inst_ids_def]
QED
