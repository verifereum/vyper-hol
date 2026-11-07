Theory concretizePtrBPOrigins
Ancestors
  pointerClosure pointerConfinedDefs basePtrDefs basePtrProofs venomInst
  finite_map pred_set list passSharedDefs concretizeMemLocDefs
  concretizeAnalysisScan basePtrConvergenceOrbit

Definition ptr_bp_alloc_roots_def:
  ptr_bp_alloc_roots fn aid =
    {out | ?inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
                 inst.inst_id = aid /\ inst_output inst = SOME out}
End

Definition ptr_bp_origins_def:
  ptr_bp_origins fn bp <=>
    !v aid off. MEM (Ptr (Allocation aid) off) (bp_get_ptrs bp v) ==>
      v IN pointer_derived_vars fn (ptr_bp_alloc_roots fn aid)
End

Theorem ptr_bp_alloc_roots_finite:
  FINITE (ptr_bp_alloc_roots fn aid)
Proof
  irule SUBSET_FINITE_I >>
  qexists `IMAGE THE (IMAGE inst_output (set (fn_insts fn)))` >>
  simp[ptr_bp_alloc_roots_def, SUBSET_DEF] >>
  metis_tac[optionTheory.THE_DEF]
QED

Theorem ptr_bp_origins_empty:
  ptr_bp_origins fn FEMPTY
Proof
  simp[ptr_bp_origins_def, bp_get_ptrs_def]
QED

Theorem ptr_bp_origins_update[local]:
  ptr_bp_origins fn bp /\
  (!aid off. MEM (Ptr (Allocation aid) off) ps ==>
    out IN pointer_derived_vars fn (ptr_bp_alloc_roots fn aid)) ==>
  ptr_bp_origins fn (bp |+ (out,ps))
Proof
  simp[ptr_bp_origins_def, bp_get_ptrs_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `v = out` >> gvs[] >> metis_tac[]
QED

Theorem ptr_bp_origin_root[local]:
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  inst_output inst = SOME out ==>
  out IN pointer_derived_vars fn (ptr_bp_alloc_roots fn inst.inst_id)
Proof
  rpt strip_tac >>
  `out IN ptr_bp_alloc_roots fn inst.inst_id` by
    (simp[ptr_bp_alloc_roots_def] >> metis_tac[]) >>
  metis_tac[pointer_derived_vars_roots, ptr_bp_alloc_roots_finite, SUBSET_DEF]
QED

Theorem ptr_bp_origin_step[local]:
  MEM inst (fn_insts fn) /\ is_pointer_preserving_op inst.inst_opcode /\
  MEM (Var u) inst.inst_operands /\ inst_output inst = SOME out /\
  u IN pointer_derived_vars fn (ptr_bp_alloc_roots fn aid) ==>
  out IN pointer_derived_vars fn (ptr_bp_alloc_roots fn aid)
Proof
  rpt strip_tac >> irule pointer_derived_vars_closed >>
  simp[ptr_bp_alloc_roots_finite] >>
  goal_assum (drule_at Any) >>
  metis_tac[inst_output_member]
QED

Theorem ptr_bp_origin_map[local]:
  ptr_bp_origins fn bp /\ MEM inst (fn_insts fn) /\
  is_pointer_preserving_op inst.inst_opcode /\
  MEM (Var src) inst.inst_operands /\ inst_output inst = SOME out /\
  (!p. ptr_base (f p) = ptr_base p) ==>
  ptr_bp_origins fn (bp |+ (out, MAP f (bp_get_ptrs bp src)))
Proof
  rpt strip_tac >> irule ptr_bp_origins_update >> simp[] >>
  simp[MEM_MAP] >> rpt strip_tac >>
  rename1 `MEM p (bp_get_ptrs bp src)` >>
  `ptr_base p = Allocation aid` by metis_tac[ptr_base_def] >>
  Cases_on `p` >> gvs[ptr_base_def] >>
  irule ptr_bp_origin_step >> goal_assum (drule_at Any) >>
  gvs[ptr_bp_origins_def] >> metis_tac[]
QED

Theorem ptr_bp_offset_base[local]:
  ptr_base (offset_by p delta) = ptr_base p /\
  ptr_base (sub_offset_by p delta) = ptr_base p
Proof
  Cases_on `p` >> Cases_on `delta` >>
  rename1 `Ptr alloc off` >> Cases_on `off` >>
  simp[offset_by_def, sub_offset_by_def, ptr_base_def] >>
  rpt IF_CASES_TAC >> simp[ptr_base_def]
QED

Theorem ptr_bp_handle_origins:
  ptr_bp_origins fn bp /\ MEM inst (fn_insts fn) ==>
  ptr_bp_origins fn (SND (bp_handle_inst bp inst))
Proof
  rpt strip_tac >>
  simp[bp_handle_inst_def] >>
  Cases_on `inst_output inst` >> simp[] >>
  Cases_on `inst.inst_opcode` >> simp[]
  >~ [`inst.inst_opcode = ALLOCA`]
  >- (irule ptr_bp_origins_update >> simp[] >>
     simp[ptr_from_alloca_def] >> rpt strip_tac >> gvs[] >>
     irule ptr_bp_origin_root >> simp[])
  >~ [`inst.inst_opcode = ADD`] >- suspend "add"
  >~ [`inst.inst_opcode = SUB`] >- suspend "sub"
  >~ [`inst.inst_opcode = PHI`] >- suspend "phi"
  >> suspend "assign"
QED

Resume ptr_bp_handle_origins[assign]:
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >> Cases_on `h` >> simp[] >>
  irule ptr_bp_origins_update >> simp[] >> rpt strip_tac >>
  irule ptr_bp_origin_step >>
  simp[is_pointer_preserving_op_def] >>
  goal_assum (drule_at Any) >>
  gvs[ptr_bp_origins_def, is_pointer_preserving_op_def] >> metis_tac[]
QED

Resume ptr_bp_handle_origins[add]:
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >> Cases_on `t'` >> simp[] >>
  Cases_on `h` >> Cases_on `h'` >> simp[] >>
  rpt IF_CASES_TAC >> simp[] >>
  irule ptr_bp_origin_map >> simp[ptr_bp_offset_base] >>
  goal_assum (drule_at Any) >> simp[is_pointer_preserving_op_def] >>
  metis_tac[]
QED

Resume ptr_bp_handle_origins[sub]:
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >> Cases_on `t'` >> simp[] >>
  Cases_on `h` >> Cases_on `h'` >> simp[] >>
  rpt IF_CASES_TAC >> simp[] >>
  irule ptr_bp_origin_map >> simp[ptr_bp_offset_base] >>
  goal_assum (drule_at Any) >> simp[is_pointer_preserving_op_def] >>
  metis_tac[]
QED

Resume ptr_bp_handle_origins[phi]:
  IF_CASES_TAC >> simp[] >>
  irule ptr_bp_origins_update >> simp[] >> rpt strip_tac >>
  drule MEM_bp_normalize >>
  simp[MEM_FLAT, MEM_MAP] >> rpt strip_tac >>
  rename1 `ptr_base p = _` >> Cases_on `p` >> gvs[ptr_base_def]
  >- metis_tac[ptr_bp_origins_def]
  >> irule ptr_bp_origin_step >>
  goal_assum (drule_at Any) >>
  simp[is_pointer_preserving_op_def] >>
  qexists `SND y'` >> conj_tac
  >- metis_tac[ptr_bp_origins_def]
  >> rewrite_tac[GSYM MEM_operand_vars_eq_Var] >>
  irule phi_pairs_mem_operand_vars >> simp[MEM_MAP] >>
  goal_assum (drule_at Any) >> simp[]
QED

Finalise ptr_bp_handle_origins

Theorem ptr_bp_block_origins[local]:
  !insts bp. ptr_bp_origins fn bp /\
    EVERY (\inst. MEM inst (fn_insts fn)) insts ==>
    ptr_bp_origins fn (SND (bp_process_block bp insts))
Proof
  Induct >> simp[bp_process_block_def] >> rpt strip_tac >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  `ptr_bp_origins fn r1` by
    metis_tac[ptr_bp_handle_origins, pairTheory.SND] >>
  first_x_assum drule >> simp[]
QED

Theorem ptr_bp_pass_origins[local]:
  ptr_bp_origins fn bp ==>
    ptr_bp_origins fn (SND (bp_one_pass fn order bp))
Proof
  strip_tac >> rewrite_tac[bp_one_pass_scan] >>
  irule ptr_bp_block_origins >>
  simp[EVERY_MEM] >> metis_tac[bp_scan_insts_member]
QED

Theorem ptr_bp_iterate_origins:
  !fuel bp. ptr_bp_origins fn bp ==>
    ptr_bp_origins fn (bp_iterate_fuel fuel fn order bp)
Proof
  Induct >> simp[bp_iterate_fuel_def] >> rpt strip_tac >>
  pairarg_tac >> gvs[] >>
  `ptr_bp_origins fn result'` by
    metis_tac[ptr_bp_pass_origins, pairTheory.SND] >>
  IF_CASES_TAC >> simp[]
QED

Theorem ptr_bp_analyze_origins:
  MEM (Ptr (Allocation aid) off) (bp_get_ptrs (bp_analyze_fuel fuel cfg fn) v) ==>
  v IN pointer_derived_vars fn (ptr_bp_alloc_roots fn aid)
Proof
  `ptr_bp_origins fn (bp_analyze_fuel fuel cfg fn)` by
    simp[bp_analyze_fuel_def, ptr_bp_iterate_origins, ptr_bp_origins_empty] >>
  metis_tac[ptr_bp_origins_def]
QED
