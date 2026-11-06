Theory exprSimAbiDecodeFreshTransfer
Ancestors
  exprSimAbiDecodeFreshBoundary exprSimAbiDecodeFreshControl exprSimAbiGasBridge
  fragExec fragGasPath gasCount abiEncoderObserver
  venomExecProofs venomInstProps venomInst venomExecSemantics venomState list
  instIdxIndep

Theorem abi_decode_fresh_exit_edge:
  abi_decode_fresh_context sa sb L ids fn /\
  (u.vs_current_bb,u.vs_inst_idx) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
  (u.vs_current_bb,u.vs_inst_idx) <> frag_observer_cut sb /\
  frag_relabel_state L sa.cs_current_bb u v /\ ~u.vs_halted /\
  lookup_block u.vs_current_bb (frag_relabel_observer sa sb L ids fn id).fn_blocks = SOME bb /\
  get_instruction bb u.vs_inst_idx = SOME inst /\
  step_inst_base inst u = r /\ exit_result r /\ (!h. r <> Halt h) ==>
  ?b p. gas_path_edge ctx fn v 0
    (exec_result_map (\t. t with <|vs_current_bb := b; vs_prev_bb := p|>) r)
Proof
  strip_tac >> drule_all abi_decode_fresh_off_cut_opcodes >> strip_tac >>
  `(u.vs_current_bb = L ==> LENGTH sa.cs_current_insts <= u.vs_inst_idx)` by
    (fs[abi_decode_fresh_context_def] >> metis_tac[abi_decode_fresh_region_entry_bound]) >>
  `?original. lookup_block
    (if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb)
      fn.fn_blocks = SOME original /\
    get_instruction original u.vs_inst_idx = SOME inst` by
    (fs[abi_decode_fresh_context_def] >> drule_all frag_relabel_instruction_agrees >> simp[]) >>
  fs[frag_relabel_state_def] >> gvs[] >>
  qexistsl_tac [`if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb`, `p`] >>
  `step_inst_base inst (u with <|vs_current_bb :=
     (if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb);
     vs_prev_bb := p|>) = exec_result_map (\t. t with <|vs_current_bb :=
     (if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb);
     vs_prev_bb := p|>) (step_inst_base inst u)` by
    (irule abi_decode_fresh_base_exit >> simp[]) >>
  gvs[] >> simp[gas_path_edge_def] >> qexists_tac `0` >>
  simp[step_inst_non_invoke, gas_count_step_def] >>
  Cases_on `step_inst_base inst u` >>
  gvs[exit_result_def, instIdxIndepTheory.exec_result_map_def]
QED

Theorem abi_decode_fresh_jump_result[local]:
  MEM inst.inst_opcode [JMP; JNZ; DJMP] /\ step_inst_base inst s = OK t ==>
  t = jump_to t.vs_current_bb s
Proof
  simp[MEM] >> strip_tac >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs(), jump_to_def]
QED

Theorem abi_decode_fresh_terminator_jump[local]:
  step_inst 0 ctx inst s = OK middle /\ ~middle.vs_halted /\
  is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  inst.inst_opcode <> STOP /\ inst.inst_opcode <> RETURN ==>
  MEM inst.inst_opcode [JMP; JNZ; DJMP]
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >> fs[is_terminator_def] >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  pairarg_tac >> gvs[]
QED

Theorem abi_decode_fresh_step_edge:
  abi_decode_fresh_context sa sb L ids fn /\
  (u.vs_current_bb,u.vs_inst_idx) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
  frag_relabel_state L sa.cs_current_bb u v /\
  abi_observer_step ctx (frag_relabel_observer sa sb L ids fn id)
    (frag_observer_cut sb) u u' ==>
  ?v'. gas_path_edge ctx fn v 0 (OK v') /\ frag_relabel_state L sa.cs_current_bb u' v'
Proof
  strip_tac >> fs[abi_observer_step_def] >>
  drule_all abi_decode_fresh_off_cut_opcodes >> strip_tac >>
  `(u.vs_current_bb = L ==> LENGTH sa.cs_current_insts <= u.vs_inst_idx)` by
    (fs[abi_decode_fresh_context_def] >> metis_tac[abi_decode_fresh_region_entry_bound]) >>
  `?original. lookup_block
    (if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb)
      fn.fn_blocks = SOME original /\ get_instruction original u.vs_inst_idx = SOME inst` by
    (fs[abi_decode_fresh_context_def] >> drule_all frag_relabel_instruction_agrees >> simp[]) >>
  `step_inst_base inst u = OK middle` by metis_tac[step_inst_non_invoke] >>
  drule frag_relabel_state_fields >> strip_tac
  >- (irule abi_decode_fresh_ordinary_edge >> goal_assum (drule_at Any) >> gvs[]) >>
  `MEM inst.inst_opcode [JMP; JNZ; DJMP]` by
    metis_tac[abi_decode_fresh_terminator_jump] >>
  `middle.vs_current_bb <> L` by
    (fs[abi_decode_fresh_context_def, EVERY_MEM] >>
     metis_tac[frag_relabel_jump_no_reentry, MEM]) >>
  Cases_on `middle.vs_current_bb = sb.cs_current_bb /\ sb.cs_current_insts = []`
  >- suspend "empty_cut" >>
  `?original_target. lookup_block middle.vs_current_bb fn.fn_blocks = SOME original_target /\
      phi_prefix_length original_target.bb_instructions = 0 /\
      phi_prefix_length target.bb_instructions = 0` by
    (fs[abi_decode_fresh_context_def] >> metis_tac[abi_decode_fresh_target_phis]) >>
  qpat_x_assum `eval_phis _ _ = _` mp_tac >>
  once_rewrite_tac[GSYM eval_phis_prefix] >> simp[eval_phis_def] >> strip_tac >> gvs[] >>
  fs[frag_relabel_state_def] >> gvs[] >>
  `step_inst_base inst (u with <|vs_current_bb :=
       (if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb);
       vs_prev_bb := p|>) =
    OK (entered with vs_prev_bb :=
       SOME (if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb))` by
    metis_tac[abi_decode_fresh_jump_control, MEM] >>
  qexists_tac `entered with <|vs_prev_bb :=
       SOME (if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb);
       vs_inst_idx := 0|>` >>
  gvs[] >> (conj_tac
  >- (simp[gas_path_edge_def] >> qexists_tac `0` >>
      simp[step_inst_non_invoke, gas_count_step_def] >> disj1_tac >>
      once_rewrite_tac[GSYM eval_phis_prefix] >> simp[eval_phis_def]) >>
  qexists_tac `SOME (if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb)` >>
  simp[venom_state_component_equality])
QED

Resume abi_decode_fresh_step_edge[empty_cut]:
  `!b p. step_inst_base inst (u with <|vs_current_bb := b; vs_prev_bb := p|>) =
    OK (middle with vs_prev_bb := SOME b)` by
    metis_tac[abi_decode_fresh_jump_control] >>
  `middle = jump_to sb.cs_current_bb u` by
    metis_tac[abi_decode_fresh_jump_result] >>
  `phi_prefix_length target.bb_instructions = 0` by
    (fs[abi_decode_fresh_context_def] >> metis_tac[abi_decode_fresh_empty_cut_phis]) >>
  qpat_x_assum `eval_phis _ _ = _` mp_tac >>
  once_rewrite_tac[GSYM eval_phis_prefix] >> simp[eval_phis_def] >> strip_tac >> gvs[] >>
  (`step_inst_base inst v = OK (jump_to sb.cs_current_bb v)` by
    (fs[frag_relabel_state_def] >>
     simp[jump_to_def, venom_state_component_equality]) >>
  qexists_tac `jump_to sb.cs_current_bb v` >>
  conj_tac
  >- (simp[gas_path_edge_def] >> qexists_tac `0` >>
      simp[step_inst_non_invoke, gas_count_step_def] >>
      metis_tac[]) >>
  gvs[frag_relabel_state_def, jump_to_def] >>
  simp[venom_state_component_equality])
QED
Finalise abi_decode_fresh_step_edge

Theorem abi_decode_fresh_empty_cut_step:
  abi_decode_fresh_context sa sb L ids fn /\
  (u.vs_current_bb,u.vs_inst_idx) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
  frag_relabel_state L sa.cs_current_bb u v /\
  abi_observer_step ctx (frag_relabel_observer sa sb L ids fn id)
    (frag_observer_cut sb) u u' /\
  sb.cs_current_insts = [] /\ u'.vs_current_bb = sb.cs_current_bb ==>
  ?v'. gas_path_edge ctx fn v 0 (OK v') /\ frag_relabel_state L sa.cs_current_bb u' v'
Proof
  metis_tac[abi_decode_fresh_step_edge]
QED
