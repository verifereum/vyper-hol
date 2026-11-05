Theory o1MakeSsaStructuralShape
Ancestors
  o1MakeSsaFormats o1MakeSsaCfg o1ContractMakeSsaPtrOk
  o1PassContract unitShapeDefs venomWf irSupply makeSsaCurrentProps list
  dretDesugarDefs venomInst venomFnScheduleRunner simplifyCfgWfssa

Theorem make_ssa_current_fn_opcode_property:
  make_ssa_current_fn s fn = (fn',s') /\
  P PHI /\ P ASSIGN /\ P NOP /\
  EVERY (\i. P i.inst_opcode) (fn_insts fn) ==>
  EVERY (\i. P i.inst_opcode) (fn_insts fn')
Proof
  strip_tac >> drule make_ssa_current_fn_opcode_provenance >>
  gvs[EVERY_MEM, mssa_mem_fn_insts] >> metis_tac[]
QED

Theorem make_ssa_current_fn_no_dret:
  make_ssa_current_fn s fn = (fn',s') /\ no_dret fn ==> no_dret fn'
Proof
  strip_tac >> drule make_ssa_current_fn_opcode_property >>
  disch_then (qspec_then `\op. op <> DRET` mp_tac) >>
  gvs[no_dret_def, EVERY_MEM]
QED

Theorem make_ssa_current_fn_entry_no_return:
  make_ssa_current_fn s fn = (fn',s') /\ entry_fn_no_return fn ==>
  entry_fn_no_return fn'
Proof
  simp[entry_fn_no_return_def] >> strip_tac >>
  ho_match_mp_tac make_ssa_current_fn_opcode_property >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem make_ssa_current_fn_entry_no_params:
  make_ssa_current_fn s fn = (fn',s') /\ entry_fn_no_params fn ==>
  entry_fn_no_params fn'
Proof
  simp[entry_fn_no_params_def] >> strip_tac >>
  ho_match_mp_tac make_ssa_current_fn_opcode_property >>
  goal_assum (drule_at Any) >> simp[is_param_opcode_def]
QED

Theorem make_ssa_current_fn_nonentry_termination:
  make_ssa_current_fn s fn = (fn',s') /\
  EVERY (\i. ~MEM i.inst_opcode [STOP; RETURN]) (fn_insts fn) ==>
  EVERY (\i. ~MEM i.inst_opcode [STOP; RETURN]) (fn_insts fn')
Proof
  strip_tac >> ho_match_mp_tac make_ssa_current_fn_opcode_property >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem make_ssa_current_fn_entry_name:
  make_ssa_current_fn s fn = (fn',s') /\
  fn_entry_label fn = SOME fn.fn_name ==>
  fn_entry_label fn' = SOME fn'.fn_name
Proof
  metis_tac[make_ssa_current_fn_entry_label, mssa_fields]
QED

Theorem make_ssa_current_fn_reserved_labels:
  make_ssa_current_fn s fn = (fn',s') /\
  EVERY (\bb. ~reserved_label bb.bb_label) fn.fn_blocks ==>
  EVERY (\bb. ~reserved_label bb.bb_label) fn'.fn_blocks
Proof
  strip_tac >> drule make_ssa_current_fn_labels >> strip_tac >>
  `EVERY (\l. ~reserved_label l) (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    simp[EVERY_MAP] >>
  pop_assum mp_tac >>
  qpat_x_assum `MAP _ _ = MAP _ _` (fn th => rewrite_tac[GSYM th]) >>
  simp[EVERY_MAP]
QED

Theorem make_ssa_current_fn_instruction_shapes:
  make_ssa_current_fn s fn = (fn',s') /\
  EVERY inst_shape_ok (fn_insts fn) ==>
  EVERY inst_shape_ok (fn_insts fn')
Proof
  simp[EVERY_MEM, mssa_mem_fn_insts] >> strip_tac >>
  `EVERY (\bb. EVERY inst_shape_ok bb.bb_instructions) fn.fn_blocks` by
    (simp[EVERY_MEM] >> metis_tac[]) >>
  drule_all make_ssa_current_fn_inst_shape >>
  simp[EVERY_MEM] >> metis_tac[]
QED

Theorem make_ssa_current_fn_wf_function:
  make_ssa_current_fn s fn = (fn',s') /\ wf_function fn /\
  ir_supply_inst_ok s /\ ir_supply_covers_fn s fn ==> wf_function fn'
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    fs[wf_function_def, fn_labels_def] >>
  `ALL_DISTINCT (MAP basic_block_bb_label fn.fn_blocks)` by
    (pure_once_rewrite_tac[GSYM bb_label_eta] >> first_assum ACCEPT_TAC) >>
  drule_all make_ssa_current_fn_cfg_blocks >> strip_tac >>
  drule make_ssa_current_fn_labels >> strip_tac >>
  `ALL_DISTINCT (fn_ir_inst_ids fn)` by
    (pure_rewrite_tac[fn_ir_inst_ids_def, lambdify block_ir_inst_ids_def] >>
     fs[wf_function_def, fn_inst_ids_distinct_def]) >>
  `EVERY (\id. MEM id s.irs_used_inst_ids) (fn_ir_inst_ids fn) /\
   ssa_vars_covered s (fn_ir_vars fn)` by
    fs[ir_supply_covers_fn_def, list_subset_def, ssa_vars_covered_def, EVERY_MEM] >>
  drule_all make_ssa_current_fn_supply_ok >> strip_tac >>
  `EVERY bb_well_formed fn'.fn_blocks` by
    (irule make_ssa_current_fn_blocks_well_formed >>
     goal_assum (drule_at Any) >> fs[wf_function_def, EVERY_MEM]) >>
  simp[wf_function_def] >> rpt conj_tac
  >- fs[fn_labels_def, wf_function_def]
  >- (fs[fn_has_entry_def, wf_function_def] >>
      Cases_on `fn'.fn_blocks` >> gvs[])
  >- fs[EVERY_MEM]
  >- (fs[fn_succs_closed_def, wf_function_def, fn_labels_def] >>
      rpt strip_tac >>
      `MEM (bb.bb_label, bb_succs bb)
        (MAP (\b. (b.bb_label, bb_succs b)) fn.fn_blocks)` by
        (qpat_x_assum `MAP (\b. (b.bb_label, bb_succs b)) _ = _`
           (fn th => pure_rewrite_tac[GSYM th]) >>
         simp[MEM_MAP] >> metis_tac[]) >>
      fs[MEM_MAP] >> metis_tac[]) >>
  fs[ssa_ids_supply_ok_def, fn_inst_ids_distinct_def,
     fn_ir_inst_ids_def] >>
  qpat_x_assum `ALL_DISTINCT (FLAT (MAP block_ir_inst_ids fn'.fn_blocks))` mp_tac >>
  pure_rewrite_tac[lambdify block_ir_inst_ids_def] >> simp[]
QED

Theorem make_ssa_current_fn_invoke_ok:
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') /\ fn_invoke_ok names fn ==>
  fn_invoke_ok names fn'
Proof
  strip_tac >> drule_all mssa_origin >> strip_tac >>
  simp[fn_invoke_ok_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[mssa_inst_origin_def] >> strip_tac >>
  gvs[fn_invoke_ok_def] >>
  qpat_x_assum `!inst. _` drule_all >> strip_tac >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `h` >> gvs[]
QED

Theorem wf_ssa_phi_label_ref:
  wf_ssa fn /\ MEM inst (fn_insts fn) /\ inst.inst_opcode = PHI /\
  MEM (Label l) inst.inst_operands ==> MEM l (fn_labels fn)
Proof
  simp[wf_ssa_def, def_dominates_uses_def, mssa_mem_fn_insts] >>
  rpt strip_tac >> first_x_assum drule_all >> simp[phi_edge_uses_wf_def] >>
  strip_tac >>
  drule simplifyCfgWfssaTheory.phi_pair_label_mem >>
  disch_then (qspec_then `l` mp_tac) >> simp[] >> strip_tac >>
  fs[MEM_MAP] >> PairCases_on `y` >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  simp[fn_labels_def, MEM_MAP] >> metis_tac[]
QED

Theorem make_ssa_current_fn_label_refs_ok:
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') /\ fn_label_refs_ok fn ==>
  fn_label_refs_ok fn'
Proof
  strip_tac >> drule_all mssa_origin >> strip_tac >>
  drule_all mssa_wf_ssa >> strip_tac >>
  drule make_ssa_current_fn_labels >> strip_tac >>
  simp[fn_label_refs_ok_def] >> rpt strip_tac >>
  Cases_on `inst.inst_opcode = PHI`
  >- metis_tac[wf_ssa_phi_label_ref] >>
  `mssa_inst_origin orig fn inst` by metis_tac[] >>
  qpat_x_assum `mssa_inst_origin _ _ _` mp_tac >>
  pure_rewrite_tac[mssa_inst_origin_def] >> strip_tac >> gvs[]
  >- (`MEM (Label l) inst'.inst_operands` by
        (qpat_x_assum `MAP _ _ = _` (fn th => rewrite_tac[GSYM th]) >>
         simp[MEM_MAP] >> qexists `Label l` >> simp[]) >>
      fs[fn_label_refs_ok_def, fn_labels_def] >> metis_tac[]) >>
  gvs[]
QED
