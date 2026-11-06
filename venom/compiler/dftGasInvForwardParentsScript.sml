Theory dftGasInvForwardParents
Ancestors
  dftGasInvForwardResidual dftGasInvForwardEffects dftDefs
  contextCodegenRel venomEffects venomInst venomWf dftCallChecks
  dftScheduleOrder passSharedDefs list rich_list

Theorem inv_forward_copy_not_entry:
  ALL_DISTINCT (MAP (\a. a.inst_id) bb.bb_instructions) /\
  revert_forward_pair bb i j /\
  get_instruction bb i = SOME copy /\ get_instruction bb j = SOME rev ==>
  ~MEM copy (entry_instructions bb.bb_instructions order
    (dft_eda bb.bb_instructions))
Proof
  strip_tac >>
  `copy.inst_opcode = RETURNDATACOPY /\ rev.inst_opcode = REVERT /\
   MEM rev bb.bb_instructions` by
    (gvs[revert_forward_pair_def, get_instruction_def, AllCaseEqs()] >>
     metis_tac[MEM_EL]) >>
  `MEM copy (inst_all_deps bb.bb_instructions order
    (dft_eda bb.bb_instructions) rev)` by
    metis_tac[inv_forward_all_deps] >>
  simp[entry_instructions_def, MEM_FILTER, MEM_nub, MEM_FLAT, MEM_MAP] >>
  rpt strip_tac >>
  simp[read_effects_def, write_effects_def, empty_effects_def, is_pseudo_def] >>
  disj1_tac >>
  qexists `MAP (\d. d.inst_id)
    (inst_all_deps bb.bb_instructions order (dft_eda bb.bb_instructions) rev)` >>
  conj_tac >- (qexists `rev` >> simp[is_pseudo_def]) >>
  simp[MEM_MAP] >> qexists `copy` >> simp[]
QED

Theorem inv_forward_copy_parent:
  ALL_DISTINCT (MAP (\a. a.inst_id) bb.bb_instructions) /\
  non_pseudo_defs_before_uses bb.bb_instructions /\
  bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions /\
  revert_forward_pair bb i j /\
  get_instruction bb i = SOME copy /\ get_instruction bb j = SOME rev /\
  MEM parent bb.bb_instructions /\ ~is_pseudo parent.inst_opcode /\
  MEM copy (inst_all_deps bb.bb_instructions order
    (dft_eda bb.bb_instructions) parent) ==>
  parent = rev
Proof
  strip_tac >>
  `i < j /\ j < LENGTH bb.bb_instructions /\ i < LENGTH bb.bb_instructions /\
   copy = EL i bb.bb_instructions /\ rev = EL j bb.bb_instructions /\
   copy.inst_opcode = RETURNDATACOPY /\ rev.inst_opcode = REVERT` by
    gvs[revert_forward_pair_def, get_instruction_def, AllCaseEqs()] >>
  `j = PRE (LENGTH bb.bb_instructions)` by
    (gvs[bb_well_formed_def] >>
     first_x_assum irule >> simp[is_terminator_def]) >>
  `?k. k < LENGTH bb.bb_instructions /\ parent = EL k bb.bb_instructions` by
    metis_tac[MEM_EL] >>
  Cases_on `k = j` >- gvs[] >>
  `k < j` by decide_tac >>
  `~is_terminator parent.inst_opcode` by
    (strip_tac >> gvs[bb_well_formed_def] >> metis_tac[]) >>
  Cases_on `k <= i`
  >- (drule_all nonterminator_dft_eda_deps_backward >> strip_tac >>
      rename1 `EL a bb.bb_instructions = copy` >>
      rename1 `EL b bb.bb_instructions = parent` >>
      `ALL_DISTINCT bb.bb_instructions` by
        metis_tac[ALL_DISTINCT_MAP] >>
      `a = i /\ b = k` by metis_tac[ALL_DISTINCT_EL_IMP] >>
      gvs[]) >>
  `parent.inst_opcode = ASSIGN` by
    (gvs[revert_forward_pair_def] >>
     first_x_assum irule >> simp[get_instruction_def] >>
     qexists `k` >> simp[] >> decide_tac) >>
  `copy.inst_outputs = []` by
    ( `inst_wf copy` by metis_tac[EVERY_MEM, MEM_EL] >>
      gvs[inst_wf_def]) >>
  `MEM copy (inst_data_deps bb.bb_instructions order parent)` by
    metis_tac[inv_assign_all_deps] >>
  metis_tac[inst_data_deps_has_outputs]
QED
