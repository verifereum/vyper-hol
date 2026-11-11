Theory lowerDloadConfiguredSuccessor
Ancestors
  lowerDloadPositionBoundary lowerDloadPhaseBoundary lowerDloadSupplySegment lowerDloadDefs
  venomExecProps venomExecSemantics venomState contextCodegenRel list rich_list pred_set

Theorem macro_step_labels[local]:
  MEM inst.inst_opcode [ALLOCA; ADD; CODECOPY; MLOAD; DLOAD; DLOADBYTES] /\
  step_inst fuel C inst s = OK z ==>
  z.vs_current_bb = s.vs_current_bb /\ z.vs_prev_bb = s.vs_prev_bb
Proof
  strip_tac >> gvs[] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[exec_alloca_def, exec_pure2_def, exec_read1_def,
       update_var_def, write_memory_with_expansion_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

Theorem macro_code_opcodes[local]:
  lower_dload_inst_supply a i = (code,b) /\
  i.inst_opcode IN {DLOAD; DLOADBYTES} ==>
  EVERY (\inst. MEM inst.inst_opcode [ALLOCA; ADD; CODECOPY; MLOAD; DLOAD; DLOADBYTES]) code
Proof
  simp[IN_INSERT, IN_SING] >> strip_tac >>
  gvs[lower_dload_inst_supply_def, AllCaseEqs()]
QED

Theorem macro_prefix_labels[local]:
  !C code t0 un0 n t un.
    ld_target_prefix C code t0 un0 n t un ==>
    EVERY (\inst. MEM inst.inst_opcode [ALLOCA; ADD; CODECOPY; MLOAD; DLOAD; DLOADBYTES]) code ==>
    t.vs_current_bb = t0.vs_current_bb /\ t.vs_prev_bb = t0.vs_prev_bb
Proof
  ho_match_mp_tac ld_target_prefix_ind >> simp[] >> rpt strip_tac >>
  `MEM (EL n code).inst_opcode [ALLOCA; ADD; CODECOPY; MLOAD; DLOAD; DLOADBYTES]` by
    (gvs[EVERY_EL] >> first_x_assum drule >> simp[]) >>
  drule_all macro_step_labels >> strip_tac >> metis_tac[]
QED

Theorem lower_dload_configured_prefix_labels:
  lower_dload_inst_supply a i = (code,b) /\
  i.inst_opcode IN {DLOAD; DLOADBYTES} /\
  ld_target_prefix C code t0 un0 n t un ==>
  t.vs_current_bb = t0.vs_current_bb /\ t.vs_prev_bb = t0.vs_prev_bb
Proof
  strip_tac >> drule_all macro_code_opcodes >> strip_tac >>
  drule macro_prefix_labels >> simp[]
QED

Theorem lower_dload_configured_macro_successor:
  lookup_block t0.vs_current_bb gn.fn_blocks = SOME gb /\
  gb.bb_instructions = p ++ code ++ nextcode ++ tail /\
  lower_dload_insts_supply a0 pre = (p,a) /\
  lower_dload_inst_supply a i = (code,b) /\
  lower_dload_inst_supply b j = (nextcode,c) /\
  i.inst_opcode IN {DLOAD; DLOADBYTES} /\
  t0.vs_inst_idx = LENGTH p /\
  ld_target_prefix CT code t0 un0 (LENGTH code) t un ==>
  t.vs_current_bb = t0.vs_current_bb /\
  t.vs_prev_bb = t0.vs_prev_bb /\
  t.vs_inst_idx = LENGTH (p ++ code) /\
  lower_dload_insts_supply a0 (pre ++ [i]) = (p ++ code,b) /\
  active_inst gn (HD nextcode) t
Proof
  strip_tac >> drule_all lower_dload_configured_prefix_labels >> strip_tac >>
  drule_all ld_target_prefix_completed_position >> strip_tac >> simp[] >>
  conj_tac
  >- (irule lower_dload_insts_supply_append_forward >>
      qexists_tac `a` >> simp[lower_dload_insts_supply_def]) >>
  `nextcode <> []` by metis_tac[o1ContractLowerDloadTheory.lower_dload_inst_supply_nonempty] >>
  simp[active_inst_def] >> qexists_tac `gb` >> simp[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  Cases_on `nextcode` >> gvs[EL_APPEND2] >>
  metis_tac[lookup_block_MEM, lookup_block_label]
QED
