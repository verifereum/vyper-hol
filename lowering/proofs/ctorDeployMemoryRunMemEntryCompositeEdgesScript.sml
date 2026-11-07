Theory ctorDeployMemoryRunMemEntryCompositeEdges
Ancestors
  ctorDeployMemoryRunMemEntryBytes ctorDeployMemoryRunMemEntryWord ctorAbiActualArrayEntry
  fragGasPathMem fragGasSeqMem fragExec gasCount memSafeRun
  unitTransformDefs instMemFrontier allocaHistory
  venomInst venomInstProofs venomExecSemantics venomState list rich_list arithmetic

Theorem ctor_checked_jump_edge:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id JMP [Label lbl] []) /\
  lookup_block lbl func.fn_blocks = SOME target /\
  phi_prefix_length target.bb_instructions = 0 /\ ~s.vs_halted ==>
  gas_path_mem_edge ctx func s 0 (OK (jump_to lbl s))
Proof
  strip_tac >>
  simp[gas_path_mem_edge_def] >>
  qexists `0` >>
  simp[step_inst_def, Once step_inst_base_def, mk_inst_def,
       gas_count_step_def, mem_safe_step_def, inst_dload_in_section_def] >>
  conj_tac
  >- (disj2_tac >> irule below_frontier_no_ranges >> simp[]) >>
  disj2_tac >> disj1_tac >>
  qexistsl [`jump_to lbl s`, `target`, `jump_to lbl s`] >>
  simp[Once step_inst_base_def, is_terminator_def, jump_to_def,
       eval_phis_no_phi]
QED

Theorem ctor_checked_jump_history:
  alloca_history func s ==> alloca_history func (jump_to lbl s)
Proof
  simp[alloca_history_def, jump_to_def]
QED

Theorem ctor_checked_jump_path:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id JMP [Label lbl] []) /\
  lookup_block lbl func.fn_blocks = SOME target /\
  phi_prefix_length target.bb_instructions = 0 /\ ~s.vs_halted /\
  alloca_history func s ==>
  gas_path_mem ctx func s 0 (OK (jump_to lbl s)) /\
  (jump_to lbl s).vs_gas_readings = s.vs_gas_readings /\
  alloca_history func (jump_to lbl s)
Proof
  strip_tac >>
  drule_all ctor_checked_jump_edge >> disch_then (qspec_then `ctx` assume_tac) >>
  `gas_path_mem ctx func (jump_to lbl s) 0 (OK (jump_to lbl s))` by
    (irule (cj 1 gas_path_mem_rules) >> simp[jump_to_def]) >>
  conj_tac
  >- (mp_tac (cj 2 gas_path_mem_rules) >> simp[] >> metis_tac[ADD_0]) >>
  simp[jump_to_def, ctor_checked_jump_history]
QED

Theorem ctor_checked_array_entry_jump:
  ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial i i s /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ [mk_inst id JMP [Label hdr] []] /\
  lookup_block hdr func.fn_blocks = SOME hdr_bb /\
  phi_prefix_length hdr_bb.bb_instructions = 0 /\
  ~s.vs_halted /\ s.vs_inst_idx = LENGTH prefix /\ alloca_history func s ==>
  ?h. ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
      tv vs slot_id slot initial i i h /\
    ~h.vs_halted /\ h.vs_current_bb = hdr /\ h.vs_inst_idx = 0 /\
    abi_decode_sim ctx func s h /\ gas_path_mem ctx func s 0 (OK h) /\
    h.vs_gas_readings = s.vs_gas_readings /\ alloca_history func h
Proof
  strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME (mk_inst id JMP [Label hdr] [])` by
    simp[get_instruction_def, EL_APPEND_EQN] >>
  drule_all ctor_checked_jump_path >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all ctor_actual_array_observation_jump >>
  disch_then (qspec_then `hdr` assume_tac) >>
  drule_all ctor_word_path_sim >> strip_tac >>
  qexists `jump_to hdr s` >> simp[jump_to_def]
QED

Theorem ctor_checked_branch_edge:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id JNZ [cond;Label yes;Label no] []) /\
  eval_operand cond s = SOME w /\
  lbl = (if w <> 0w then yes else no) /\
  lookup_block lbl func.fn_blocks = SOME target /\
  phi_prefix_length target.bb_instructions = 0 /\ ~s.vs_halted ==>
  gas_path_mem_edge ctx func s 0 (OK (jump_to lbl s))
Proof
  strip_tac >> simp[gas_path_mem_edge_def] >> qexists `0` >>
  simp[step_inst_def, Once step_inst_base_def, mk_inst_def,
       gas_count_step_def, mem_safe_step_def, inst_dload_in_section_def] >>
  conj_tac
  >- (disj2_tac >> irule below_frontier_no_ranges >> simp[]) >>
  disj2_tac >> disj1_tac >>
  qexistsl [`jump_to lbl s`, `target`, `jump_to lbl s`] >>
  Cases_on `w = 0w` >>
  gvs[Once step_inst_base_def, is_terminator_def, jump_to_def, eval_phis_no_phi]
QED

Theorem ctor_checked_branch_path:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id JNZ [cond;Label yes;Label no] []) /\
  eval_operand cond s = SOME w /\ lbl = (if w <> 0w then yes else no) /\
  lookup_block lbl func.fn_blocks = SOME target /\
  phi_prefix_length target.bb_instructions = 0 /\ ~s.vs_halted /\
  alloca_history func s ==>
  gas_path_mem ctx func s 0 (OK (jump_to lbl s)) /\
  (jump_to lbl s).vs_gas_readings = s.vs_gas_readings /\
  alloca_history func (jump_to lbl s)
Proof
  strip_tac >>
  drule_all ctor_checked_branch_edge >> disch_then (qspec_then `ctx` assume_tac) >>
  `gas_path_mem ctx func (jump_to lbl s) 0 (OK (jump_to lbl s))` by
    (irule (cj 1 gas_path_mem_rules) >> simp[jump_to_def]) >>
  conj_tac
  >- (mp_tac (cj 2 gas_path_mem_rules) >> simp[] >> metis_tac[ADD_0]) >>
  simp[jump_to_def, ctor_checked_jump_history]
QED

Theorem ctor_checked_sequence_endpoint:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\ ~s.vs_halted /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) code /\
  run_inst_seq_mem_ok code s /\ run_inst_seq code s = OK t /\
  t.vs_allocas = s.vs_allocas /\ t.vs_current_bb = s.vs_current_bb /\
  end_idx = s.vs_inst_idx + LENGTH code /\ alloca_history func s ==>
  gas_path_mem ctx func s 0 (OK (t with vs_inst_idx := end_idx)) /\
  t.vs_gas_readings = s.vs_gas_readings /\
  alloca_history func (t with vs_inst_idx := end_idx)
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
   EVERY (\i. i.inst_opcode <> ALLOCA) code` by fs[EVERY_CONJ] >>
  `FILTER (\i. i.inst_opcode = GAS) code = []` by
    (fs[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]) >>
  drule_all run_inst_seq_gas_path_mem >>
  disch_then (qspec_then `ctx` assume_tac) >>
  `gas_path_mem ctx func s 0 (OK (t with vs_inst_idx := end_idx))` by gvs[] >>
  drule gas_path_mem_ok_suffix >> simp[] >> strip_tac >>
  irule ctor_sequence_history_advance >> qexistsl [`bb`, `code`, `s`] >> simp[ADD_COMM]
QED
