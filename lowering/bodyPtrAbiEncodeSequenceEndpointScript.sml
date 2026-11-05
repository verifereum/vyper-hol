(* Check transport for capped straight-line execution. *)
Theory bodyPtrAbiEncodeSequenceEndpoint
Ancestors
  ptrSafeRun ptrDiscipline contextCodegenRel venomExecSemantics venomState
  venomInst venomExecProofs list rich_list arithmetic

Theorem ptr_safe_step_no_exemption_transport:
  inst.inst_opcode <> INVOKE /\ ~in_revert_forward fn0 s /\
  ~about_to_revert fn0 inst s /\
  ptr_safe_step D lo fuel ctx fn0 PG G tn inst s ==>
  ptr_safe_step D lo fuel ctx fn PG G tn inst s
Proof
  simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def] >>
  metis_tac[]
QED

Theorem block_no_revert_instruction:
  EVERY (\inst. inst.inst_opcode <> REVERT) bb.bb_instructions /\
  get_instruction bb k = SOME inst ==> inst.inst_opcode <> REVERT
Proof
  simp[get_instruction_def, EVERY_MEM] >> strip_tac >>
  Cases_on `k < LENGTH bb.bb_instructions` >> gvs[] >>
  metis_tac[MEM_EL]
QED

Theorem block_no_revert_forward:
  EVERY (\inst. inst.inst_opcode <> REVERT) bb.bb_instructions ==>
  ~revert_forward_at bb k
Proof
  simp[revert_forward_at_def, revert_forward_pair_def] >>
  metis_tac[block_no_revert_instruction]
QED

Theorem function_block_no_revert_exemptions:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  EVERY (\b. EVERY (\i. i.inst_opcode <> REVERT) b.bb_instructions) fn.fn_blocks /\
  inst.inst_opcode <> REVERT ==>
  ~in_revert_forward fn s /\ ~about_to_revert fn inst s
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_def, FIND_MEM] >>
  `EVERY (\i. i.inst_opcode <> REVERT) bb.bb_instructions` by
    (qpat_x_assum `EVERY _ fn.fn_blocks` mp_tac >>
     simp_tac bool_ss [EVERY_MEM] >> disch_then (qspec_then `bb` mp_tac) >> simp[]) >>
  conj_tac
  >- (simp[in_revert_forward_def] >> metis_tac[block_no_revert_forward]) >>
  simp[about_to_revert_def, active_inst_def] >>
  fs[EVERY_MEM] >> metis_tac[MEM_EL]
QED

Theorem nonterminating_code_no_revert:
  EVERY (\i. ~is_terminator i.inst_opcode) xs ==>
  EVERY (\i. i.inst_opcode <> REVERT) xs
Proof
  simp_tac bool_ss [EVERY_MEM] >> rpt strip_tac >>
  first_x_assum (qspec_then `i` mp_tac) >> simp[is_terminator_def]
QED

Theorem padded_singleton_no_revert_exemptions:
  fn.fn_blocks = [bb] /\ bb.bb_label = s.vs_current_bb /\
  bb.bb_instructions = REPLICATE start pad ++ xs /\
  pad.inst_opcode <> REVERT /\
  EVERY (\i. ~is_terminator i.inst_opcode) xs /\
  inst.inst_opcode <> REVERT ==>
  ~in_revert_forward fn s /\ ~about_to_revert fn inst s
Proof
  strip_tac >> irule function_block_no_revert_exemptions >>
  simp[lookup_block_def, FIND_thm, EVERY_REPLICATE] >>
  metis_tac[nonterminating_code_no_revert]
QED
