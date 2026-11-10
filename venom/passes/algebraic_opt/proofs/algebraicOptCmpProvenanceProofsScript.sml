Theory algebraicOptCmpProvenanceProofs
Ancestors
  algebraicOptMainShapeProofs algebraicOptCmpSimulationProofs algebraicOptDefs
  algebraicOptShapeProofs algebraicOptCmpScanProofs list venomInst pred_set

Theorem ao_simple_comparator_outputs:
  EVERY (\i. is_comparator i.inst_opcode ==> i.inst_outputs = inst.inst_outputs)
    (ao_opt_shift inst) /\
  EVERY (\i. is_comparator i.inst_opcode ==> i.inst_outputs = inst.inst_outputs)
    (ao_opt_signextend ra lbl idx inst) /\
  EVERY (\i. is_comparator i.inst_opcode ==> i.inst_outputs = inst.inst_outputs)
    (ao_opt_exp inst) /\
  EVERY (\i. is_comparator i.inst_opcode ==> i.inst_outputs = inst.inst_outputs)
    (ao_opt_addsub inst) /\
  EVERY (\i. is_comparator i.inst_opcode ==> i.inst_outputs = inst.inst_outputs)
    (ao_opt_and inst) /\
  EVERY (\i. is_comparator i.inst_opcode ==> i.inst_outputs = inst.inst_outputs)
    (ao_opt_muldiv inst) /\
  EVERY (\i. is_comparator i.inst_opcode ==> i.inst_outputs = inst.inst_outputs)
    (ao_opt_or dfg inst)
Proof
  Cases_on `inst.inst_operands` >>
  simp[ao_opt_shift_def, ao_opt_signextend_def, ao_opt_exp_def,
       ao_opt_addsub_def, ao_opt_and_def, ao_opt_muldiv_def, ao_opt_or_def] >>
  Cases_on `t` >>
  simp[ao_opt_shift_def, ao_opt_signextend_def, ao_opt_exp_def,
       ao_opt_addsub_def, ao_opt_and_def, ao_opt_muldiv_def, ao_opt_or_def] >>
  Cases_on `t'` >>
  simp[ao_opt_shift_def, ao_opt_signextend_def, ao_opt_exp_def,
       ao_opt_addsub_def, ao_opt_and_def, ao_opt_muldiv_def, ao_opt_or_def] >>
  Cases_on `h` >> Cases_on `h'` >> simp[] >>
  rpt conj_tac >> rpt (IF_CASES_TAC >> simp[])
QED

Theorem ao_eq_comparator_outputs:
  EVERY (\i. is_comparator i.inst_opcode ==> i.inst_outputs = inst.inst_outputs)
    (ao_opt_eq dfg fr inst)
Proof
  Cases_on `inst.inst_operands` >> simp[ao_opt_eq_def] >>
  Cases_on `t` >> simp[ao_opt_eq_def] >>
  Cases_on `t'` >> simp[ao_opt_eq_def] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  Cases_on `fr "not"` >> Cases_on `fr "xor"` >>
  gvs[passSharedDefsTheory.is_comparator_def]
QED

Theorem ao_prefer_iz_comparator_outputs:
  EVERY (\i. is_comparator i.inst_opcode ==> i.inst_outputs = inst.inst_outputs)
    (ao_cmp_prefer_iz_zero fr op1 inst) /\
  EVERY (\i. is_comparator i.inst_opcode ==> i.inst_outputs = inst.inst_outputs)
    (ao_cmp_prefer_iz_max fr op1 inst) /\
  EVERY (\i. is_comparator i.inst_opcode ==> i.inst_outputs = inst.inst_outputs)
    (ao_cmp_prefer_iz_general fr op1 op2 inst)
Proof
  Cases_on `fr "not"` >> Cases_on `fr "xor"` >> Cases_on `fr "iz"` >>
  simp[ao_cmp_prefer_iz_zero_def, ao_cmp_prefer_iz_max_def,
       ao_cmp_prefer_iz_general_def, passSharedDefsTheory.is_comparator_def]
QED

Theorem ao_comparator_comparator_outputs:
  EVERY (\i. is_comparator i.inst_opcode ==> i.inst_outputs = inst.inst_outputs)
    (ao_opt_comparator dfg ra lbl idx fr inst)
Proof
  Cases_on `inst.inst_operands` >> simp[ao_opt_comparator_def] >>
  Cases_on `t` >> simp[ao_opt_comparator_def] >>
  Cases_on `t'` >> simp[ao_opt_comparator_def] >>
  Cases_on `h = h'` >> simp[] >>
  Cases_on `ao_opt_cmp_range ra lbl idx inst
    (inst.inst_opcode = GT \/ inst.inst_opcode = SGT)
    (inst.inst_opcode = SGT \/ inst.inst_opcode = SLT)` >> simp[] >>
  pairarg_tac >> simp[] >>
  rpt (IF_CASES_TAC >> simp[ao_prefer_iz_comparator_outputs]) >>
  Cases_on `fr "not"` >> Cases_on `fr "iz"` >>
  gvs[passSharedDefsTheory.is_comparator_def]
QED

Theorem ao_peephole_comparator_outputs:
  EVERY (\i. is_comparator i.inst_opcode ==> i.inst_outputs = inst.inst_outputs)
    (ao_peephole_inst dfg ra lbl idx fr inst)
Proof
  simp[ao_peephole_inst_def] >>
  rpt (IF_CASES_TAC >>
    simp[ao_simple_comparator_outputs, ao_eq_comparator_outputs,
         ao_comparator_comparator_outputs])
QED

Theorem ao_transform_inst_comparator_outputs:
  EVERY (\i. is_comparator i.inst_opcode ==> i.inst_outputs = inst.inst_outputs)
    (ao_transform_inst dfg ra lbl idx targets fr inst)
Proof
  simp[ao_transform_inst_def, ao_resolve_iszero_inst_fields] >>
  rpt (IF_CASES_TAC >> simp[ao_resolve_iszero_inst_fields]) >>
  Cases_on `ao_opt_producer dfg (ao_resolve_iszero_inst targets inst)`
  >- (simp[EVERY_MAP, ao_post_flip_inst_shape] >>
      mp_tac (Q.SPEC `ao_pre_flip_inst (ao_resolve_iszero_inst targets inst)`
        (Q.GEN `inst` ao_peephole_comparator_outputs)) >>
      simp[ao_pre_flip_inst_shape, ao_resolve_iszero_inst_fields]) >>
  drule ao_opt_producer_shape >> strip_tac >>
  gvs[ao_post_flip_inst_shape, ao_resolve_iszero_inst_fields]
QED

Theorem ao_transform_insts_supply_comparator_outputs:
  !insts s idx outs s'.
    ao_transform_insts_supply dfg ra lbl targets s idx insts = (outs,s') ==>
    !out. MEM out outs /\ is_comparator out.inst_opcode ==>
      ?inst. MEM inst insts /\ out.inst_outputs = inst.inst_outputs
Proof
  Induct >> simp[Once ao_transform_insts_supply_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `ao_alloc_fresh s` >> rename1 `ao_alloc_fresh s = (fr,s1)` >>
  Cases_on `ao_transform_insts_supply dfg ra lbl targets s1 (SUC idx) insts` >>
  gvs[Once ao_transform_insts_supply_def] >>
  first_x_assum drule >> strip_tac >>
  rpt strip_tac >>
  mp_tac (Q.SPEC `h` (Q.GEN `inst` ao_transform_inst_comparator_outputs)) >>
  simp[EVERY_MEM] >> metis_tac[]
QED

Theorem ao_transform_block_supply_comparator_outputs:
  ao_transform_block_supply dfg ra targets s bb = (bb',s') ==>
  !out. MEM out bb'.bb_instructions /\ is_comparator out.inst_opcode ==>
    ?inst. MEM inst bb.bb_instructions /\ out.inst_outputs = inst.inst_outputs
Proof
  Cases_on `ao_transform_insts_supply dfg ra bb.bb_label targets s 0
    bb.bb_instructions` >>
  gvs[ao_transform_block_supply_def] >> strip_tac >> gvs[] >>
  metis_tac[ao_transform_insts_supply_comparator_outputs]
QED

Theorem ao_transform_blocks_supply_comparator_outputs:
  !bbs s bbs' s'.
    ao_transform_blocks_supply dfg ra targets s bbs = (bbs',s') ==>
    !out. MEM out (fn_insts_blocks bbs') /\ is_comparator out.inst_opcode ==>
      ?inst. MEM inst (fn_insts_blocks bbs) /\
        out.inst_outputs = inst.inst_outputs
Proof
  Induct >> simp[Once ao_transform_blocks_supply_def, fn_insts_blocks_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `ao_transform_block_supply dfg ra targets s h` >>
  rename1 `ao_transform_block_supply dfg ra targets s h = (bb,s1)` >>
  Cases_on `ao_transform_blocks_supply dfg ra targets s1 bbs` >>
  gvs[Once ao_transform_blocks_supply_def, fn_insts_blocks_def] >>
  first_x_assum drule >> strip_tac >>
  metis_tac[ao_transform_block_supply_comparator_outputs]
QED

Theorem ao_main_function_comparator_outputs:
  !fn fn0 sup bbs sup1 mid.
  fn0 = fn with fn_blocks :=
    MAP (\bb. bb with bb_instructions :=
      MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
  ao_transform_blocks_supply (dfg_build_function fn0) (range_analyze fn0)
    (ao_compute_fn_iszero_targets fn0) sup fn0.fn_blocks = (bbs,sup1) /\
  mid = fn0 with fn_blocks := bbs ==>
  !out. MEM out (fn_insts mid) /\ is_comparator out.inst_opcode ==>
    ?inst. MEM inst (fn_insts fn) /\ out.inst_outputs = inst.inst_outputs
Proof
  rpt gen_tac >> strip_tac >>
  drule ao_offset_function_ids_outputs >> strip_tac >>
  drule ao_transform_blocks_supply_comparator_outputs >>
  gvs[fn_insts_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  `MEM inst.inst_outputs (MAP (\i. i.inst_outputs) (fn_insts fn))` by
    (pure_rewrite_tac[fn_insts_def] >>
     qpat_x_assum `MAP (\i. i.inst_outputs) _ = _` (fn th => rewrite_tac[GSYM th]) >>
     simp[MEM_MAP] >> metis_tac[]) >>
  gvs[MEM_MAP, fn_insts_def] >> metis_tac[]
QED

Theorem ao_main_function_comparator_initial:
  !fn fn0 sup bbs sup1 mid ignored flipped s.
  fn0 = fn with fn_blocks :=
    MAP (\bb. bb with bb_instructions :=
      MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
  ao_transform_blocks_supply (dfg_build_function fn0) (range_analyze fn0)
    (ao_compute_fn_iszero_targets fn0) sup fn0.fn_blocks = (bbs,sup1) /\
  mid = fn0 with fn_blocks := bbs /\
  (!inst x. MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs ==>
     lookup_var x s = NONE) /\
  flipped = {v | ?out action. MEM out (fn_insts mid) /\
    ao_cmp_flip_cert (dfg_build_function mid) out action /\
    MEM v out.inst_outputs} ==>
  ao_cmp_state_rel ignored flipped s s
Proof
  rpt gen_tac >> strip_tac >>
  irule ao_cmp_state_rel_initial >> rpt strip_tac >>
  qpat_x_assum `v IN flipped` mp_tac >>
  asm_rewrite_tac[] >>
  simp[ao_cmp_flip_cert_def, ao_cmp_source_def] >> strip_tac >>
  drule ao_main_function_comparator_outputs >>
  disch_then drule >> disch_then drule >>
  strip_tac >> gvs[] >>
  qpat_x_assum `!out. MEM out _ /\ is_comparator _ ==> _` drule_all >>
  strip_tac >> gvs[] >> metis_tac[MEM]
QED
