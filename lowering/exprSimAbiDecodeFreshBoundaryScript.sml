Theory exprSimAbiDecodeFreshBoundary
Ancestors
  exprSimAbiGasBridge fragExec venomExecSemantics venomInst list rich_list
  abiEncoderObserver venomExecProofs venomInstProps venomState arithmetic

Definition abi_decode_fresh_context_def:
  abi_decode_fresh_context sa sb L ids fn <=>
    cs_extends sa sb /\ sa.cs_blocks <> sb.cs_blocks /\ frag_ops_free sa sb /\
    fn_has_code sa sb fn /\ LENGTH ids = LENGTH sa.cs_current_insts /\
    L <> sb.cs_current_bb /\
    ~MEM L (MAP (\bb. bb.bb_label) (emitted_blocks sa sb)) /\
    EVERY (\i. ~MEM (Label L) i.inst_operands) (frag_code sa sb)
End

Theorem abi_decode_fresh_target_phis:
  cs_extends sa sb /\ sa.cs_blocks <> sb.cs_blocks /\ frag_ops_free sa sb /\
  fn_has_code sa sb fn /\ lbl <> L /\
  (lbl <> sb.cs_current_bb \/ sb.cs_current_insts <> []) /\
  lookup_block lbl (frag_relabel_observer sa sb L ids fn id).fn_blocks = SOME bb ==>
  ?original. lookup_block lbl fn.fn_blocks = SOME original /\
    phi_prefix_length original.bb_instructions = 0 /\
    phi_prefix_length bb.bb_instructions = 0
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `sb.cs_current_insts <> []`
  >- metis_tac[frag_relabel_target_phis] >>
  `emitted_blocks sa sb <> []` by
    (drule frag_extends_emitted_shape >> strip_tac >> gvs[]) >>
  drule frag_relabel_observer_lookup_cases >> strip_tac >> gvs[] >>
  drule_all start_swap_emitted_blocks >> strip_tac >> fs[MEM_APPEND] >> gvs[] >>
  `MEM bb (emitted_blocks sa sb)` by
    (`emitted_blocks sa sb = FRONT (emitted_blocks sa sb) ++
       [LAST (emitted_blocks sa sb)]` by simp[APPEND_FRONT_LAST] >>
     metis_tac[MEM_APPEND]) >>
  drule_all frag_relabel_front_nonphi >> strip_tac >>
  qexists_tac `bb` >> conj_tac >- (fs[fn_has_code_def] >> metis_tac[]) >>
  Cases_on `bb.bb_instructions` >> fs[phi_prefix_length_def]
QED

Theorem abi_decode_fresh_empty_cut_phis:
  L <> sb.cs_current_bb /\ sb.cs_current_insts = [] /\
  lookup_block sb.cs_current_bb
    (frag_relabel_observer sa sb L ids fn id).fn_blocks = SOME bb ==>
  phi_prefix_length bb.bb_instructions = 0
Proof
  simp[frag_relabel_observer_cut] >> strip_tac >>
  gvs[phi_prefix_length_def, mk_inst_def]
QED

Theorem abi_decode_fresh_region_entry_bound:
  (u.vs_current_bb,u.vs_inst_idx) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
  LENGTH ids = LENGTH sa.cs_current_insts ==>
  (u.vs_current_bb = L ==> LENGTH sa.cs_current_insts <= u.vs_inst_idx)
Proof
  simp[frag_observer_region_def, start_relabel_def] >> metis_tac[]
QED

Theorem abi_decode_fresh_off_cut_opcodes:
  abi_decode_fresh_context sa sb L ids fn /\
  (u.vs_current_bb,u.vs_inst_idx) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
  (u.vs_current_bb,u.vs_inst_idx) <> frag_observer_cut sb /\
  lookup_block u.vs_current_bb (frag_relabel_observer sa sb L ids fn id).fn_blocks = SOME bb /\
  get_instruction bb u.vs_inst_idx = SOME inst ==>
  inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
  inst.inst_opcode <> PHI /\ inst.inst_opcode <> STOP /\ inst.inst_opcode <> RETURN
Proof
  strip_tac >> fs[abi_decode_fresh_context_def] >>
  `(u.vs_current_bb = L ==> LENGTH sa.cs_current_insts <= u.vs_inst_idx)` by
    metis_tac[abi_decode_fresh_region_entry_bound] >>
  drule_all frag_relabel_code_provenance >> strip_tac >>
  fs[frag_ops_free_def, EVERY_MEM]
QED

Theorem abi_decode_fresh_successful_terminator_jump[local]:
  step_inst 0 ctx inst s = OK middle /\ ~middle.vs_halted /\
  is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  inst.inst_opcode <> STOP /\ inst.inst_opcode <> RETURN ==>
  MEM inst.inst_opcode [JMP; JNZ; DJMP]
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >> fs[is_terminator_def] >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  pairarg_tac >> gvs[]
QED

Theorem abi_decode_fresh_region_closed:
  abi_decode_fresh_context sa sb L ids fn ==>
  observer_region_closed ctx (frag_relabel_observer sa sb L ids fn id)
    (frag_observer_cut sb)
    (frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb))
Proof
  strip_tac >> rw[observer_region_closed_def] >>
  fs[abi_observer_step_def] >>
  drule_all abi_decode_fresh_off_cut_opcodes >> strip_tac
  >- (drule_all step_preserves_control_flow >> strip_tac >>
      gvs[frag_observer_region_def] >> metis_tac[LESS_EQ_SUC_REFL, LESS_EQ_TRANS]) >>
  `MEM inst.inst_opcode [JMP; JNZ; DJMP]` by
    metis_tac[abi_decode_fresh_successful_terminator_jump] >>
  `middle.vs_current_bb <> L` by
    (`(s.vs_current_bb = L ==> LENGTH sa.cs_current_insts <= s.vs_inst_idx)` by
       (fs[abi_decode_fresh_context_def] >> metis_tac[abi_decode_fresh_region_entry_bound]) >>
     `step_inst_base inst s = OK middle` by metis_tac[step_inst_non_invoke] >>
     fs[abi_decode_fresh_context_def, EVERY_MEM] >>
     metis_tac[frag_relabel_jump_no_reentry, MEM]) >>
  drule eval_phis_preserves_current_bb >> strip_tac >>
  drule frag_relabel_observer_lookup_cases >> strip_tac >>
  fs[abi_decode_fresh_context_def] >> drule_all start_swap_fields >> strip_tac >>
  gvs[frag_observer_region_def, start_relabel_def, MEM_MAP] >> metis_tac[]
QED
