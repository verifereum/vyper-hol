Theory concretizeAnalysisOriginFlow
Ancestors
  concretizeAnalysisCoverage concretizeAnalysisBaseModel singleWriterScan
  concretizePtrClosure frameOriginUpdates frameOriginHistoryCompletedWrites basePtrDefs venomInst
  pointerClosure pointerConfinedDefs ptrDiscipline relation list pred_set finite_map

Definition bp_flow_def:
  bp_flow fn aid v <=>
    ?x. sw_seed (bp_descriptor_stream (fn_insts fn)) (Allocation aid) x /\
        RTC (sw_edge (bp_descriptor_stream (fn_insts fn))) x v
End

Definition origin_local_flow_def:
  origin_local_flow fn om <=>
    !v aid site. FLOOKUP om v = SOME (OriginLocal aid,site) ==> bp_flow fn aid v
End

Theorem bp_flow_seed:
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  inst_output inst = SOME v ==> bp_flow fn inst.inst_id v
Proof
  rpt strip_tac >> simp[bp_flow_def] >> qexists `v` >>
  simp[sw_seed_def, bp_descriptor_stream_member] >>
  qexistsl [`{Allocation inst.inst_id}`, `{}`] >> simp[] >>
  qexists `inst` >> simp[bp_descriptor_def]
QED

Theorem bp_flow_edge:
  bp_flow fn aid x /\ sw_edge (bp_descriptor_stream (fn_insts fn)) x y ==>
  bp_flow fn aid y
Proof
  simp[bp_flow_def] >> metis_tac[RTC_TRANS, RTC_SINGLE]
QED

Theorem origin_local_flow_empty[simp]:
  origin_local_flow fn FEMPTY
Proof
  simp[origin_local_flow_def]
QED

Theorem origin_local_flow_restrict:
  origin_local_flow fn om ==> origin_local_flow fn (DRESTRICT om keys)
Proof
  simp[origin_local_flow_def, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem bp_descriptor_seed_support:
  bp_descriptor inst = SOME (v,seed,sources) /\ a IN seed ==>
  inst.inst_opcode = ALLOCA /\ inst_output inst = SOME v
Proof
  Cases_on `inst_output inst` >> simp[bp_descriptor_def] >>
  Cases_on `inst.inst_opcode` >> simp[] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem bp_descriptor_edge_support:
  bp_descriptor inst = SOME (v,seed,sources) /\ u IN sources ==>
  u = v \/ (is_pointer_preserving_op inst.inst_opcode /\
    MEM (Var u) inst.inst_operands /\ MEM v inst.inst_outputs)
Proof
  Cases_on `inst_output inst` >> simp[bp_descriptor_def] >>
  Cases_on `inst.inst_opcode` >> simp[] >>
  rpt strip_tac >> gvs[AllCaseEqs(), is_pointer_preserving_op_def] >>
  gvs[MEM_MAP] >>
  gvs[inst_output_def, AllCaseEqs()] >>
  PairCases_on `y` >> simp[] >>
  drule cfgNormBaseTheory.phi_pairs_mem_var >> simp[]
QED

Theorem bp_flow_support:
  bp_flow fn aid v ==> v IN fn_pv P fn
Proof
  simp[bp_flow_def] >> rpt strip_tac >>
  `x IN fn_pv P fn` by
    (gvs[sw_seed_def, bp_descriptor_stream_member] >>
     drule_all bp_descriptor_seed_support >> strip_tac >>
     simp[fn_pv_def] >>
     `x IN ptr_roots P fn` by
       (simp[ptr_roots_def, alloca_roots_def] >> metis_tac[]) >>
     metis_tac[concretizeAnalysisRootsTheory.ptr_roots_finite,
       pointer_derived_vars_roots, SUBSET_DEF]) >>
  `!u w. RTC (sw_edge (bp_descriptor_stream (fn_insts fn))) u w ==>
     u IN fn_pv P fn ==> w IN fn_pv P fn` suffices_by metis_tac[] >>
  ho_match_mp_tac RTC_INDUCT >> simp[] >> rpt strip_tac >>
  first_x_assum irule >>
  gvs[sw_edge_def, bp_descriptor_stream_member] >>
  drule_all bp_descriptor_edge_support >> strip_tac >> gvs[] >>
  gvs[fn_pv_def] >> irule pointer_derived_vars_closed >>
  metis_tac[concretizeAnalysisRootsTheory.ptr_roots_finite]
QED

Theorem bp_flow_descriptor:
  MEM inst (fn_insts fn) /\ bp_descriptor inst = SOME (v,seed,sources) /\
  u IN sources /\ bp_flow fn aid u ==> bp_flow fn aid v
Proof
  rpt strip_tac >> irule bp_flow_edge >> goal_assum (drule_at Any) >>
  simp[sw_edge_def, bp_descriptor_stream_member] >>
  qexistsl [`seed`, `sources`] >> simp[] >> metis_tac[]
QED


Theorem origin_local_flow_phis:
  origin_local_flow fn om /\ EVERY (\i. MEM i (fn_insts fn)) insts ==>
  origin_local_flow fn (origin_phis prev om insts)
Proof
  simp[origin_local_flow_def] >> rpt strip_tac >>
  drule origin_phis_lookup >> strip_tac
  >- metis_tac[] >>
  gvs[origin_phi_some, origin_op_some] >>
  `bp_flow fn aid v'` by metis_tac[] >>
  drule resolve_phi_var_pair >> strip_tac >>
  `MEM v' (MAP SND (phi_pairs inst.inst_operands))` by
    (simp[MEM_MAP] >> metis_tac[pairTheory.SND]) >>
  irule bp_flow_descriptor >>
  qexistsl [`inst`, `{}`, `v INSERT set (MAP SND (phi_pairs inst.inst_operands))`, `v'`] >>
  gvs[EVERY_MEM, bp_descriptor_def, inst_output_def]
QED

Theorem origin_local_flow_entry:
  origin_local_flow fn om ==> origin_local_flow fn (origin_entry fn s om)
Proof
  strip_tac >> simp[origin_entry_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  irule origin_local_flow_phis >> simp[] >>
  drule venomExecProofsTheory.lookup_block_MEM >>
  simp[EVERY_MEM, fn_insts_def,
    venomWfPropsTheory.fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
  metis_tac[]
QED

Theorem origin_flow_arithmetic_shape[local]:
  (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) /\
  step_inst fuel ctx inst s = OK s' ==>
  ?op1 op2. inst.inst_operands = [op1;op2]
Proof
  strip_tac >>
  gvs[Once venomExecSemanticsTheory.step_inst_def,
      venomExecSemanticsTheory.step_inst_base_def,
      venomExecSemanticsTheory.exec_pure2_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem origin_flow_assign_shape[local]:
  inst.inst_opcode = ASSIGN /\ step_inst fuel ctx inst s = OK s' ==>
  ?op. inst.inst_operands = [op]
Proof
  strip_tac >> gvs[Once venomExecSemanticsTheory.step_inst_def,
      venomExecSemanticsTheory.step_inst_base_def, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem origin_flow_inherited_descriptor[local]:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB \/ inst.inst_opcode = ASSIGN) /\
  inst_output inst = SOME v /\ MEM (Var u) inst.inst_operands /\
  u IN fn_pv P fn /\ step_inst fuel ctx inst s = OK s' ==>
  ?seed sources. bp_descriptor inst = SOME (v,seed,sources) /\ u IN sources
Proof
  rpt strip_tac
  >- (drule_at (Pos last) origin_flow_arithmetic_shape >> simp[] >> strip_tac >>
      `!l. ~MEM (Label l) inst.inst_operands` by
        (fs[fn_ptr_ok_def] >>
         qpat_x_assum `!i. MEM i (fn_insts fn) ==> _` drule >> simp[] >>
         metis_tac[]) >>
      Cases_on `op1` >> Cases_on `op2` >>
      gvs[bp_descriptor_def])
  >- (drule_at (Pos last) origin_flow_arithmetic_shape >> simp[] >> strip_tac >>
      `!l. ~MEM (Label l) inst.inst_operands` by
        (fs[fn_ptr_ok_def] >>
         qpat_x_assum `!i. MEM i (fn_insts fn) ==> _` drule >> simp[] >>
         metis_tac[]) >>
      `!w. op2 = Var w ==> w NOTIN fn_pv P fn` by
        (gvs[fn_ptr_ok_def, affine_pointer_ops_def, fn_pv_def,
             fn_insts_def, venomWfPropsTheory.fn_insts_blocks_flat,
             MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
      Cases_on `op1` >> Cases_on `op2` >>
      gvs[bp_descriptor_def] >> metis_tac[]) >>
  drule_all origin_flow_assign_shape >> strip_tac >>
  gvs[bp_descriptor_def]
QED

Theorem origin_local_flow_step:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\ origin_local_flow fn om /\
  step_inst fuel ctx inst s = OK s' ==>
  origin_local_flow fn (origin_step PG om inst s')
Proof
  strip_tac >> simp[origin_local_flow_def] >> rpt strip_tac >>
  drule origin_step_lookup >> strip_tac
  >- metis_tac[origin_local_flow_def] >>
  `inst_output inst = SOME v` by simp[inst_output_def] >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (drule origin_out_alloca >> simp[] >> strip_tac >> gvs[] >>
      irule bp_flow_seed >> simp[]) >>
  Cases_on `inst.inst_opcode = PARAM`
  >- (drule origin_out_param >> simp[] >> strip_tac >> gvs[]) >>
  Cases_on `inst.inst_opcode = DALLOCA`
  >- (drule origin_out_dalloca >> simp[] >> strip_tac >> gvs[]) >>
  drule_all origin_out_inherited >> strip_tac >>
  gvs[origin_op_some] >>
  `bp_flow fn aid v'` by metis_tac[origin_local_flow_def] >>
  `v' IN fn_pv P fn` by metis_tac[bp_flow_support] >>
  `?seed sources. bp_descriptor inst = SOME (v,seed,sources) /\ v' IN sources` by
    (irule origin_flow_inherited_descriptor >> metis_tac[]) >>
  irule bp_flow_descriptor >> metis_tac[]
QED
