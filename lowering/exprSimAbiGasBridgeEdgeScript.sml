(* The relabeled-observer gas bridges without the end-block premise on the
   counted function: when the fragment ends in a fresh empty block, the
   counted path stops at the jump into it, at index 0, before any PHIs
   there run.  The observer-side (fn') premises are unchanged. *)
Theory exprSimAbiGasBridgeEdge
Ancestors
  exprSimAbiGasBridge
  fragGasMode fragExec exprLoweringProps abiDecoderLoop abiEncoderObserver
  venomInst venomExecSemantics venomState compileEnv list rich_list
  fragGasPath gasCount arithmetic venomExecProofs venomInstProps venomWf
  instIdxIndep

Definition frag_relabel_edge_context_def:
  frag_relabel_edge_context sa sb L ids fn <=>
    cs_extends sa sb /\ sa.cs_blocks <> sb.cs_blocks /\ frag_ops_free sa sb /\
    fn_has_code sa sb fn /\ LENGTH ids = LENGTH sa.cs_current_insts /\
    L <> sb.cs_current_bb /\
    ~MEM L (MAP (\bb. bb.bb_label) (emitted_blocks sa sb)) /\
    EVERY (\i. ~MEM (Label L) i.inst_operands) (frag_code sa sb)
End

Theorem frag_relabel_edge_observer_phis:
  cs_extends sa sb /\ sa.cs_blocks <> sb.cs_blocks /\ frag_ops_free sa sb /\
  lbl <> L /\
  lookup_block lbl (frag_relabel_observer sa sb L ids fn id).fn_blocks = SOME bb ==>
  phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >>
  `emitted_blocks sa sb <> []` by
    (drule frag_extends_emitted_shape >> strip_tac >> gvs[]) >>
  drule frag_relabel_observer_lookup_cases >> strip_tac
  >- (gvs[] >>
      `EVERY (\i. i.inst_opcode <> PHI) sb.cs_current_insts` by
        (fs[frag_ops_free_def, frag_code_def, NULL_EQ, EVERY_APPEND, EVERY_MEM] >>
         metis_tac[]) >>
      Cases_on `sb.cs_current_insts` >>
      fs[phi_prefix_length_def, mk_inst_def]) >>
  drule_all start_swap_emitted_blocks >> strip_tac >> fs[MEM_APPEND] >> gvs[] >>
  drule_all frag_relabel_front_nonphi >> strip_tac >>
  Cases_on `bb.bb_instructions` >> fs[phi_prefix_length_def]
QED

Theorem frag_relabel_edge_base_nonphi[local]:
  inst.inst_opcode <> PHI /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\ step_inst_base inst s = OK t ==>
  step_inst_base inst (s with <|vs_current_bb := b; vs_prev_bb := p|>) =
    OK (t with <|vs_current_bb := b; vs_prev_bb := p|>)
Proof
  Cases_on `is_pseudo inst.inst_opcode`
  >- (Cases_on `inst.inst_opcode` >>
      fs[is_pseudo_def] >>
      asm_simp_tac bool_ss [step_inst_base_opcode_eqs] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >> simp[update_var_def]) >>
  metis_tac[frag_relabel_base_ordinary]
QED

Theorem frag_relabel_edge_ordinary:
  frag_relabel_state L entry u v /\ ~u.vs_halted /\
  lookup_block v.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb u.vs_inst_idx = SOME inst /\
  inst.inst_opcode <> PHI /\ inst.inst_opcode <> GAS /\
  inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
  step_inst_base inst u = OK middle /\ ~middle.vs_halted ==>
  ?v'. gas_path_edge ctx fn v 0 (OK v') /\
       frag_relabel_state L entry
         (middle with vs_inst_idx := SUC u.vs_inst_idx) v'
Proof
  strip_tac >>
  `middle.vs_current_bb = u.vs_current_bb` by
    metis_tac[step_preserves_control_flow, step_inst_non_invoke] >>
  fs[frag_relabel_state_def] >> gvs[] >>
  drule_all frag_relabel_edge_base_nonphi >>
  disch_then (qspecl_then
    [`p`, `if u.vs_current_bb = L then entry else u.vs_current_bb`] assume_tac) >>
  qexists_tac `middle with <|vs_current_bb :=
     (if u.vs_current_bb = L then entry else u.vs_current_bb);
     vs_prev_bb := p; vs_inst_idx := SUC u.vs_inst_idx|>` >>
  gvs[] >> conj_tac
  >- (simp[gas_path_edge_def] >> qexists_tac `0` >>
      simp[step_inst_non_invoke, gas_count_step_def]) >>
  qexists_tac `p` >> simp[venom_state_component_equality]
QED

Theorem frag_relabel_edge_operand_control[local]:
  !op s b p.
    eval_operand op (s with <|vs_prev_bb := p; vs_current_bb := b|>) =
    eval_operand op s
Proof
  Cases >> simp[eval_operand_def, lookup_var_def]
QED

Theorem frag_relabel_edge_jump_control:
  MEM inst.inst_opcode [JMP; JNZ; DJMP] /\ step_inst_base inst u = OK middle ==>
  step_inst_base inst (u with <|vs_current_bb := b; vs_prev_bb := p|>) =
    OK (middle with vs_prev_bb := SOME b)
Proof
  simp[MEM] >> strip_tac >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs] >>
  simp[frag_relabel_edge_operand_control] >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  simp[jump_to_def, venom_state_component_equality]
QED

Theorem frag_relabel_edge_raw_jump:
  frag_relabel_state L entry u v /\ ~u.vs_halted /\
  lookup_block v.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb u.vs_inst_idx = SOME inst /\
  MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
  step_inst_base inst u = OK (jump_to lbl u) /\ lbl <> L ==>
  ?v'. gas_path_edge ctx fn v 0 (OK v') /\
       frag_relabel_state L entry (jump_to lbl u) v'
Proof
  strip_tac >> fs[frag_relabel_state_def] >> gvs[] >>
  `step_inst_base inst (u with <|vs_current_bb :=
    (if u.vs_current_bb = L then entry else u.vs_current_bb); vs_prev_bb := p|>) =
    OK ((jump_to lbl u) with vs_prev_bb :=
      SOME (if u.vs_current_bb = L then entry else u.vs_current_bb))` by
    metis_tac[frag_relabel_edge_jump_control, MEM] >>
  (qexists_tac `jump_to lbl (u with <|vs_current_bb :=
    (if u.vs_current_bb = L then entry else u.vs_current_bb); vs_prev_bb := p|>)` >>
  conj_tac
  >- (simp[gas_path_edge_def] >> qexists_tac `0` >>
      gvs[jump_to_def, step_inst_non_invoke, gas_count_step_def, MEM,
          is_terminator_def] >>
      disj2_tac >> disj1_tac >> qexists_tac `lbl` >> simp[]) >>
  simp[frag_relabel_state_def, jump_to_def, venom_state_component_equality])
QED

Theorem frag_edge_successful_terminator_jump[local]:
  step_inst 0 ctx inst s = OK middle /\ ~middle.vs_halted /\
  is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  inst.inst_opcode <> STOP /\ inst.inst_opcode <> RETURN ==>
  MEM inst.inst_opcode [JMP; JNZ; DJMP]
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >> fs[is_terminator_def] >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  pairarg_tac >> gvs[]
QED

Theorem frag_relabel_edge_region_entry_bound:
  (u.vs_current_bb,u.vs_inst_idx) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
  LENGTH ids = LENGTH sa.cs_current_insts ==>
  (u.vs_current_bb = L ==> LENGTH sa.cs_current_insts <= u.vs_inst_idx)
Proof
  simp[frag_observer_region_def, start_relabel_def] >> metis_tac[]
QED

Theorem frag_relabel_edge_off_cut_opcodes:
  frag_relabel_edge_context sa sb L ids fn /\
  (u.vs_current_bb,u.vs_inst_idx) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
  (u.vs_current_bb,u.vs_inst_idx) <> frag_observer_cut sb /\
  lookup_block u.vs_current_bb (frag_relabel_observer sa sb L ids fn id).fn_blocks = SOME bb /\
  get_instruction bb u.vs_inst_idx = SOME inst ==>
  inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
  inst.inst_opcode <> PHI /\ inst.inst_opcode <> STOP /\ inst.inst_opcode <> RETURN
Proof
  strip_tac >> fs[frag_relabel_edge_context_def] >>
  `(u.vs_current_bb = L ==> LENGTH sa.cs_current_insts <= u.vs_inst_idx)` by
    metis_tac[frag_relabel_edge_region_entry_bound] >>
  drule_all frag_relabel_code_provenance >> strip_tac >>
  fs[frag_ops_free_def, EVERY_MEM]
QED

Theorem frag_relabel_edge_region_closed:
  frag_relabel_edge_context sa sb L ids fn ==>
  observer_region_closed ctx (frag_relabel_observer sa sb L ids fn id)
    (frag_observer_cut sb)
    (frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb))
Proof
  strip_tac >> rw[observer_region_closed_def] >>
  fs[abi_observer_step_def] >>
  drule_all frag_relabel_edge_off_cut_opcodes >> strip_tac
  >- (drule_all step_preserves_control_flow >> strip_tac >>
      gvs[frag_observer_region_def] >> metis_tac[LESS_EQ_SUC_REFL, LESS_EQ_TRANS]) >>
  `MEM inst.inst_opcode [JMP; JNZ; DJMP]` by
    metis_tac[frag_edge_successful_terminator_jump] >>
  `middle.vs_current_bb <> L` by
    (`(s.vs_current_bb = L ==> LENGTH sa.cs_current_insts <= s.vs_inst_idx)` by
       (fs[frag_relabel_edge_context_def] >> metis_tac[frag_relabel_edge_region_entry_bound]) >>
     `step_inst_base inst s = OK middle` by metis_tac[step_inst_non_invoke] >>
     fs[frag_relabel_edge_context_def, EVERY_MEM] >>
     metis_tac[frag_relabel_jump_no_reentry, MEM]) >>
  drule eval_phis_preserves_current_bb >> strip_tac >>
  drule frag_relabel_observer_lookup_cases >> strip_tac >>
  fs[frag_relabel_edge_context_def] >> drule_all start_swap_fields >> strip_tac >>
  gvs[frag_observer_region_def, start_relabel_def, MEM_MAP] >> metis_tac[]
QED

Theorem frag_relabel_edge_step:
  frag_relabel_edge_context sa sb L ids fn /\
  (u.vs_current_bb,u.vs_inst_idx) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
  frag_relabel_state L sa.cs_current_bb u v /\
  abi_observer_step ctx (frag_relabel_observer sa sb L ids fn id)
    (frag_observer_cut sb) u u' ==>
  ?v'. gas_path_edge ctx fn v 0 (OK v') /\ frag_relabel_state L sa.cs_current_bb u' v'
Proof
  strip_tac >> fs[abi_observer_step_def] >>
  drule_all frag_relabel_edge_off_cut_opcodes >> strip_tac >>
  `(u.vs_current_bb = L ==> LENGTH sa.cs_current_insts <= u.vs_inst_idx)` by
    (fs[frag_relabel_edge_context_def] >> metis_tac[frag_relabel_edge_region_entry_bound]) >>
  `?original. lookup_block
    (if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb)
      fn.fn_blocks = SOME original /\
    get_instruction original u.vs_inst_idx = SOME inst` by
    (fs[frag_relabel_edge_context_def] >> drule_all frag_relabel_instruction_agrees >> simp[]) >>
  `step_inst_base inst u = OK middle` by metis_tac[step_inst_non_invoke] >>
  drule frag_relabel_state_fields >> strip_tac
  >- (irule frag_relabel_edge_ordinary >> goal_assum (drule_at Any) >> gvs[]) >>
  `MEM inst.inst_opcode [JMP; JNZ; DJMP]` by
    metis_tac[frag_edge_successful_terminator_jump] >>
  `middle.vs_current_bb <> L` by
    (fs[frag_relabel_edge_context_def, EVERY_MEM] >>
     metis_tac[frag_relabel_jump_no_reentry, MEM]) >>
  `phi_prefix_length target.bb_instructions = 0` by
    (fs[frag_relabel_edge_context_def] >> metis_tac[frag_relabel_edge_observer_phis]) >>
  qpat_x_assum `eval_phis _ _ = _` mp_tac >>
  once_rewrite_tac[GSYM eval_phis_prefix] >> simp[eval_phis_def] >> strip_tac >> gvs[] >>
  rename1 `step_inst_base inst u = OK jumped` >>
  `jumped = jump_to jumped.vs_current_bb u` by
    (gvs[MEM] >>
     gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
     simp[jump_to_def]) >>
  `jumped.vs_inst_idx = 0` by
    (qpat_x_assum `jumped = jump_to _ _` mp_tac >>
     simp[jump_to_def, venom_state_component_equality] >> metis_tac[]) >>
  `jumped with vs_inst_idx := 0 = jumped` by
    simp[venom_state_component_equality] >>
  gvs[] >> metis_tac[frag_relabel_edge_raw_jump, MEM]
QED

Theorem edge_eval_operands_control[local]:
  !ops s b p.
    eval_operands ops (s with <|vs_prev_bb := p; vs_current_bb := b|>) =
    eval_operands ops s
Proof
  Induct >> simp[eval_operands_def, frag_relabel_edge_operand_control]
QED

Theorem edge_pure1_control[local]:
  exec_pure1 f inst (s with <|vs_prev_bb := p; vs_current_bb := b|>) =
    exec_result_map (\t. t with <|vs_prev_bb := p; vs_current_bb := b|>)
      (exec_pure1 f inst s)
Proof
  namedCases_on `inst.inst_operands` ["", "a ops"]
  >- simp[exec_pure1_def, instIdxIndepTheory.exec_result_map_def] >>
  Cases_on `ops`
  >- (simp[exec_pure1_def, frag_relabel_edge_operand_control] >>
      Cases_on `eval_operand a s` >>
      simp[instIdxIndepTheory.exec_result_map_def] >>
      namedCases_on `inst.inst_outputs` ["", "out outs"] >>
      simp[instIdxIndepTheory.exec_result_map_def] >>
      Cases_on `outs` >>
      simp[instIdxIndepTheory.exec_result_map_def, update_var_def]) >>
  simp[exec_pure1_def, instIdxIndepTheory.exec_result_map_def]
QED

Theorem edge_pure2_control[local]:
  exec_pure2 f inst (s with <|vs_prev_bb := p; vs_current_bb := b|>) =
    exec_result_map (\t. t with <|vs_prev_bb := p; vs_current_bb := b|>)
      (exec_pure2 f inst s)
Proof
  namedCases_on `inst.inst_operands` ["", "a ops"]
  >- simp[exec_pure2_def, instIdxIndepTheory.exec_result_map_def] >>
  namedCases_on `ops` ["", "c rest"]
  >- simp[exec_pure2_def, instIdxIndepTheory.exec_result_map_def] >>
  Cases_on `rest`
  >- (simp[exec_pure2_def, frag_relabel_edge_operand_control] >>
      Cases_on `eval_operand a s` >>
      simp[instIdxIndepTheory.exec_result_map_def] >>
      Cases_on `eval_operand c s` >>
      simp[instIdxIndepTheory.exec_result_map_def] >>
      namedCases_on `inst.inst_outputs` ["", "out outs"] >>
      simp[instIdxIndepTheory.exec_result_map_def] >>
      Cases_on `outs` >>
      simp[instIdxIndepTheory.exec_result_map_def, update_var_def]) >>
  simp[exec_pure2_def, instIdxIndepTheory.exec_result_map_def]
QED

Theorem edge_pure3_control[local]:
  exec_pure3 f inst (s with <|vs_prev_bb := p; vs_current_bb := b|>) =
    exec_result_map (\t. t with <|vs_prev_bb := p; vs_current_bb := b|>)
      (exec_pure3 f inst s)
Proof
  namedCases_on `inst.inst_operands` ["", "a ops"]
  >- simp[exec_pure3_def, instIdxIndepTheory.exec_result_map_def] >>
  namedCases_on `ops` ["", "c rest"]
  >- simp[exec_pure3_def, instIdxIndepTheory.exec_result_map_def] >>
  namedCases_on `rest` ["", "d tail"]
  >- simp[exec_pure3_def, instIdxIndepTheory.exec_result_map_def] >>
  Cases_on `tail`
  >- (simp[exec_pure3_def, frag_relabel_edge_operand_control] >>
      Cases_on `eval_operand a s` >>
      simp[instIdxIndepTheory.exec_result_map_def] >>
      Cases_on `eval_operand c s` >>
      simp[instIdxIndepTheory.exec_result_map_def] >>
      Cases_on `eval_operand d s` >>
      simp[instIdxIndepTheory.exec_result_map_def] >>
      namedCases_on `inst.inst_outputs` ["", "out outs"] >>
      simp[instIdxIndepTheory.exec_result_map_def] >>
      Cases_on `outs` >>
      simp[instIdxIndepTheory.exec_result_map_def, update_var_def]) >>
  simp[exec_pure3_def, instIdxIndepTheory.exec_result_map_def]
QED

Theorem edge_call_request_control[local]:
  venom_call_request (s with <|vs_prev_bb := p; vs_current_bb := b|>)
    addr value off sz static = venom_call_request s addr value off sz static
Proof
  simp[venomCallOracleDefsTheory.venom_call_request_def, read_memory_def]
QED

Theorem edge_create_request_control[local]:
  venom_create_request (s with <|vs_prev_bb := p; vs_current_bb := b|>)
    value off sz salt = venom_create_request s value off sz salt
Proof
  simp[venomCallOracleDefsTheory.venom_create_request_def, read_memory_def]
QED

Theorem edge_ext_call_control[local]:
  exec_ext_call inst (s with <|vs_prev_bb := p; vs_current_bb := b|>)
    gas addr value ao az ro rz static =
    exec_result_map (\t. t with <|vs_prev_bb := p; vs_current_bb := b|>)
      (exec_ext_call inst s gas addr value ao az ro rz static)
Proof
  namedCases_on `inst.inst_outputs` ["", "out outs"]
  >- simp[exec_ext_call_def, instIdxIndepTheory.exec_result_map_def] >>
  Cases_on `outs` >>
  simp[exec_ext_call_def, edge_call_request_control,
       venomCallOracleDefsTheory.consume_call_outcome_eq,
       write_memory_with_expansion_def, update_var_def,
       instIdxIndepTheory.exec_result_map_def]
QED

Theorem edge_create_control[local]:
  exec_create inst (s with <|vs_prev_bb := p; vs_current_bb := b|>)
    value off sz salt =
    exec_result_map (\t. t with <|vs_prev_bb := p; vs_current_bb := b|>)
      (exec_create inst s value off sz salt)
Proof
  namedCases_on `inst.inst_outputs` ["", "out outs"]
  >- simp[exec_create_def, instIdxIndepTheory.exec_result_map_def] >>
  Cases_on `outs` >>
  simp[exec_create_def, edge_create_request_control,
       venomCallOracleDefsTheory.consume_create_outcome_eq,
       update_var_def, halt_state_def, set_returndata_def,
       instIdxIndepTheory.exec_result_map_def] >>
  IF_CASES_TAC >> simp[instIdxIndepTheory.exec_result_map_def]
QED

Theorem edge_delegate_state_control[local]:
  make_venom_delegatecall_state
    (s with <|vs_prev_bb := p; vs_current_bb := b|>) target gas data code static =
  make_venom_delegatecall_state s target gas data code static
Proof
  simp[make_venom_delegatecall_state_def, venom_to_tx_params_def]
QED

Theorem edge_extract_control[local]:
  extract_venom_result (s with <|vs_prev_bb := p; vs_current_bb := b|>)
    output ro rz result =
  OPTION_MAP (\v. (FST v, SND v with <|vs_prev_bb := p; vs_current_bb := b|>))
    (extract_venom_result s output ro rz result)
Proof
  Cases_on `result` >- simp[extract_venom_result_def] >>
  rename1 `SOME pair` >> PairCases_on `pair` >>
  simp[extract_venom_result_def] >>
  namedCases_on `pair1.contexts` ["", "ctxt rest"] >> simp[] >>
  Cases_on `rest` >> simp[] >>
  PairCases_on `ctxt` >>
  Cases_on `pair0` >> simp[write_memory_with_expansion_def] >>
  qmatch_goalsub_rename_tac `case outcome of NONE => _ | SOME _ => _` >>
  Cases_on `outcome` >> simp[write_memory_with_expansion_def]
QED

Theorem edge_delegatecall_control[local]:
  exec_delegatecall inst (s with <|vs_prev_bb := p; vs_current_bb := b|>)
    gas addr ao az ro rz =
    exec_result_map (\t. t with <|vs_prev_bb := p; vs_current_bb := b|>)
      (exec_delegatecall inst s gas addr ao az ro rz)
Proof
  simp[exec_delegatecall_def, read_memory_def, edge_delegate_state_control,
       edge_extract_control] >>
  qmatch_goalsub_abbrev_tac `extract_venom_result s 1w (w2n ro) (w2n rz) run_result` >>
  Cases_on `extract_venom_result s 1w (w2n ro) (w2n rz) run_result` >>
  simp[instIdxIndepTheory.exec_result_map_def] >>
  rename1 `_ = SOME pair` >> PairCases_on `pair` >> simp[] >>
  namedCases_on `inst.inst_outputs` ["", "out outs"] >>
  simp[instIdxIndepTheory.exec_result_map_def] >>
  Cases_on `outs` >> simp[instIdxIndepTheory.exec_result_map_def, update_var_def]
QED

Theorem edge_read0_control[local]:
  f (s with <|vs_prev_bb := p; vs_current_bb := b|>) = f s ==>
  exec_read0 f inst (s with <|vs_prev_bb := p; vs_current_bb := b|>) =
    exec_result_map (\t. t with <|vs_prev_bb := p; vs_current_bb := b|>)
      (exec_read0 f inst s)
Proof
  strip_tac >> namedCases_on `inst.inst_outputs` ["", "out outs"] >>
  simp[exec_read0_def, instIdxIndepTheory.exec_result_map_def] >>
  Cases_on `outs` >>
  simp[exec_read0_def, instIdxIndepTheory.exec_result_map_def, update_var_def]
QED

Theorem edge_read1_control[local]:
  (!v. f v (s with <|vs_prev_bb := p; vs_current_bb := b|>) = f v s) ==>
  exec_read1 f inst (s with <|vs_prev_bb := p; vs_current_bb := b|>) =
    exec_result_map (\t. t with <|vs_prev_bb := p; vs_current_bb := b|>)
      (exec_read1 f inst s)
Proof
  strip_tac >> namedCases_on `inst.inst_operands` ["", "a ops"]
  >- simp[exec_read1_def, instIdxIndepTheory.exec_result_map_def] >>
  Cases_on `ops`
  >- (simp[exec_read1_def, frag_relabel_edge_operand_control] >>
      Cases_on `eval_operand a s` >> simp[instIdxIndepTheory.exec_result_map_def] >>
      namedCases_on `inst.inst_outputs` ["", "out outs"] >>
      simp[instIdxIndepTheory.exec_result_map_def] >>
      Cases_on `outs` >>
      simp[instIdxIndepTheory.exec_result_map_def, update_var_def]) >>
  simp[exec_read1_def, instIdxIndepTheory.exec_result_map_def]
QED

Theorem edge_write2_control[local]:
  (!v w. f v w (s with <|vs_prev_bb := p; vs_current_bb := b|>) =
     f v w s with <|vs_prev_bb := p; vs_current_bb := b|>) ==>
  exec_write2 f inst (s with <|vs_prev_bb := p; vs_current_bb := b|>) =
    exec_result_map (\t. t with <|vs_prev_bb := p; vs_current_bb := b|>)
      (exec_write2 f inst s)
Proof
  strip_tac >> namedCases_on `inst.inst_operands` ["", "a ops"]
  >- simp[exec_write2_def, instIdxIndepTheory.exec_result_map_def] >>
  namedCases_on `ops` ["", "c rest"]
  >- simp[exec_write2_def, instIdxIndepTheory.exec_result_map_def] >>
  Cases_on `rest`
  >- (simp[exec_write2_def, frag_relabel_edge_operand_control] >>
      Cases_on `eval_operand a s` >> simp[instIdxIndepTheory.exec_result_map_def] >>
      Cases_on `eval_operand c s` >> simp[instIdxIndepTheory.exec_result_map_def]) >>
  simp[exec_write2_def, instIdxIndepTheory.exec_result_map_def]
QED

Theorem edge_base_abort[local]:
  inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> PHI /\
  step_inst_base inst s = Abort a t ==>
  step_inst_base inst (s with <|vs_current_bb := b; vs_prev_bb := p|>) =
    Abort a (t with <|vs_current_bb := b; vs_prev_bb := p|>)
Proof
  Cases_on `inst.inst_opcode` >> simp[] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs] >>
  simp[edge_pure1_control, edge_pure2_control, edge_pure3_control,
       edge_ext_call_control, edge_create_control, edge_delegatecall_control,
       edge_read0_control, edge_read1_control, edge_write2_control,
       mload_def, sload_def, tload_def, contract_storage_def, contract_transient_def,
       mstore_def, mstore8_def, istore_def, sstore_def, tstore_def,
       write_memory_with_expansion_def, instIdxIndepTheory.exec_result_map_def] >>
  simp[frag_relabel_edge_operand_control, edge_eval_operands_control] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  gvs[instIdxIndepTheory.exec_result_map_def, halt_state_def, set_returndata_def,
      revert_state_def, exec_alloca_def, exec_gas_def, AllCaseEqs()] >>
  qpat_x_assum `_ = Abort _ _` mp_tac >> pairarg_tac >> simp[]
QED

Theorem edge_mcopy_control[local]:
  mcopy dst src sz (s with <|vs_prev_bb := p; vs_current_bb := b|>) =
    (mcopy dst src sz s) with <|vs_prev_bb := p; vs_current_bb := b|>
Proof
  simp[mcopy_def, read_memory_def, write_memory_with_expansion_def]
QED

Theorem edge_pack_dret_control[local]:
  !pairs cursor s b p.
  pack_dret_dynamic cursor pairs (s with <|vs_prev_bb := p; vs_current_bb := b|>) =
    (FST (pack_dret_dynamic cursor pairs s),
     FST (SND (pack_dret_dynamic cursor pairs s)),
     (SND (SND (pack_dret_dynamic cursor pairs s))) with
       <|vs_current_bb := b; vs_prev_bb := p|>)
Proof
  Induct >- simp[pack_dret_dynamic_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[pack_dret_dynamic_def, edge_mcopy_control] >>
  first_x_assum (fn th => rewrite_tac[th]) >> pairarg_tac >> simp[]
QED

Theorem edge_base_intret[local]:
  inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> PHI /\
  step_inst_base inst s = IntRet vals t ==>
  step_inst_base inst (s with <|vs_current_bb := b; vs_prev_bb := p|>) =
    IntRet vals (t with <|vs_current_bb := b; vs_prev_bb := p|>)
Proof
  Cases_on `inst.inst_opcode` >> simp[] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs] >>
  simp[edge_pure1_control, edge_pure2_control, edge_pure3_control,
       edge_ext_call_control, edge_create_control, edge_delegatecall_control,
       edge_read0_control, edge_read1_control, edge_write2_control,
       mload_def, sload_def, tload_def, contract_storage_def, contract_transient_def,
       mstore_def, mstore8_def, istore_def, sstore_def, tstore_def,
       write_memory_with_expansion_def, instIdxIndepTheory.exec_result_map_def] >>
  simp[frag_relabel_edge_operand_control, edge_eval_operands_control] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  gvs[instIdxIndepTheory.exec_result_map_def, halt_state_def, set_returndata_def,
      revert_state_def, exec_alloca_def, exec_gas_def, AllCaseEqs()] >>
  rewrite_tac[edge_pack_dret_control] >>
  qpat_x_assum `_ = IntRet _ _` mp_tac >> pairarg_tac >> simp[] >> strip_tac >> gvs[]
QED

Theorem edge_base_exit[local]:
  inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> PHI /\
  step_inst_base inst u = r /\ exit_result r /\ (!h. r <> Halt h) ==>
  step_inst_base inst (u with <|vs_current_bb := b; vs_prev_bb := p|>) =
    exec_result_map (\t. t with <|vs_current_bb := b; vs_prev_bb := p|>) r
Proof
  Cases_on `r` >> simp[exit_result_def, instIdxIndepTheory.exec_result_map_def] >>
  (rpt strip_tac)
  >- (irule (SRULE [] edge_base_abort) >> simp[]) >>
  irule (SRULE [] edge_base_intret) >> simp[]
QED

Theorem frag_relabel_edge_exit_edge:
  frag_relabel_edge_context sa sb L ids fn /\
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
  strip_tac >> drule_all frag_relabel_edge_off_cut_opcodes >> strip_tac >>
  `(u.vs_current_bb = L ==> LENGTH sa.cs_current_insts <= u.vs_inst_idx)` by
    (fs[frag_relabel_edge_context_def] >> metis_tac[frag_relabel_edge_region_entry_bound]) >>
  `?original. lookup_block
    (if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb)
      fn.fn_blocks = SOME original /\
    get_instruction original u.vs_inst_idx = SOME inst` by
    (fs[frag_relabel_edge_context_def] >> drule_all frag_relabel_instruction_agrees >> simp[]) >>
  fs[frag_relabel_state_def] >> gvs[] >>
  qexistsl_tac [`if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb`, `p`] >>
  `step_inst_base inst (u with <|vs_current_bb :=
     (if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb);
     vs_prev_bb := p|>) = exec_result_map (\t. t with <|vs_current_bb :=
     (if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb);
     vs_prev_bb := p|>) (step_inst_base inst u)` by
    (irule edge_base_exit >> simp[]) >>
  gvs[] >> simp[gas_path_edge_def] >> qexists_tac `0` >>
  simp[step_inst_non_invoke, gas_count_step_def] >>
  Cases_on `step_inst_base inst u` >>
  gvs[exit_result_def, instIdxIndepTheory.exec_result_map_def]
QED

Theorem frag_relabel_edge_exit_path_aux[local]:
  frag_relabel_edge_context sa sb L ids fn ==>
  !fuel n u bb r v.
    (u.vs_current_bb,u.vs_inst_idx) IN
      frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
    ~u.vs_halted /\
    lookup_block u.vs_current_bb (frag_relabel_observer sa sb L ids fn id).fn_blocks = SOME bb /\
    LENGTH bb.bb_instructions - u.vs_inst_idx = n /\
    run_from fuel ctx (frag_relabel_observer sa sb L ids fn id) u = r /\
    exit_result r /\ (!h. r <> Halt h) /\
    frag_relabel_state L sa.cs_current_bb u v ==>
    ?b p. gas_path ctx fn v 0
      (exec_result_map (\t. t with <|vs_current_bb := b; vs_prev_bb := p|>) r)
Proof
  strip_tac >> completeInduct_on `fuel` >> completeInduct_on `n` >>
  rpt strip_tac >>
  Cases_on `(u.vs_current_bb,u.vs_inst_idx) = frag_observer_cut sb`
  >- (`lookup_block u.vs_current_bb (frag_relabel_observer sa sb L ids fn id).fn_blocks =
         SOME <|bb_label := sb.cs_current_bb;
                bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []]|>` by
        gvs[frag_observer_cut_def, frag_relabel_observer_cut] >>
      `get_instruction bb u.vs_inst_idx = SOME (mk_inst id STOP [] [])` by
        (gvs[frag_observer_cut_def] >> simp[frag_observer_cut_instruction]) >>
      `run_from fuel ctx (frag_relabel_observer sa sb L ids fn id) u = Halt (stop_view u)` by
        (rewrite_tac[stop_view_def] >> irule run_from_halt >>
         qexistsl_tac [`bb`, `mk_inst id STOP [] []`] >>
         simp[step_inst_base_opcode_eqs, mk_inst_def] >> gvs[mk_inst_def]) >>
      metis_tac[]) >>
  Cases_on `get_instruction bb u.vs_inst_idx`
  >- (qpat_x_assum `run_from fuel _ _ u = r` mp_tac >>
      simp[Once run_from_def, Once exec_block_def] >>
      strip_tac >> gvs[exit_result_def]) >>
  rename1 `get_instruction bb u.vs_inst_idx = SOME inst` >>
  `inst.inst_opcode <> INVOKE` by metis_tac[frag_relabel_edge_off_cut_opcodes] >>
  Cases_on `step_inst_base inst u` >>
  qpat_x_assum `run_from fuel ctx (frag_relabel_observer sa sb L ids fn id) u = _` mp_tac >>
  simp[Once run_from_def, Once exec_block_def, step_inst_non_invoke] >> strip_tac
  >- (rename1 `step_inst_base inst u = OK middle` >>
      `~middle.vs_halted` by metis_tac[step_inst_base_OK_preserves_halted] >>
      Cases_on `is_terminator inst.inst_opcode`
      >- suspend "jump" >> suspend "ordinary")
  >- suspend "abort"
  >- suspend "intret" >> metis_tac[exit_result_def]
QED

Resume frag_relabel_edge_exit_path_aux[abort]:
  gvs[] >>
  `?b p. gas_path_edge ctx fn v 0
    (exec_result_map (\t. t with <|vs_current_bb := b; vs_prev_bb := p|>)
      (step_inst_base inst u))` by
    (irule frag_relabel_edge_exit_edge >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`b`, `p`] >> irule (cj 3 gas_path_rules) >>
  Cases_on `step_inst_base inst u` >>
  gvs[exit_result_def, instIdxIndepTheory.exec_result_map_def]
QED

Resume frag_relabel_edge_exit_path_aux[intret]:
  gvs[] >>
  `?b p. gas_path_edge ctx fn v 0
    (exec_result_map (\t. t with <|vs_current_bb := b; vs_prev_bb := p|>)
      (step_inst_base inst u))` by
    (irule frag_relabel_edge_exit_edge >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`b`, `p`] >> irule (cj 3 gas_path_rules) >>
  Cases_on `step_inst_base inst u` >>
  gvs[exit_result_def, instIdxIndepTheory.exec_result_map_def]
QED

Resume frag_relabel_edge_exit_path_aux[ordinary]:
  `middle.vs_current_bb = u.vs_current_bb` by
    metis_tac[venomInstProofsTheory.step_preserves_control_flow, step_inst_non_invoke] >>
  `abi_observer_step ctx (frag_relabel_observer sa sb L ids fn id) (frag_observer_cut sb) u
     (middle with vs_inst_idx := SUC u.vs_inst_idx)` by
    (simp[abi_observer_step_def, step_inst_non_invoke] >> metis_tac[]) >>
  drule_all frag_relabel_edge_step >> strip_tac >>
  `(u.vs_current_bb,SUC u.vs_inst_idx) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb)` by
    (drule_all frag_relabel_edge_region_closed >>
     rewrite_tac[observer_region_closed_def] >> disch_then drule >> simp[]) >>
  qpat_x_assum `!m. m < n ==> _`
    (qspec_then `LENGTH bb.bb_instructions - SUC u.vs_inst_idx` mp_tac) >>
  impl_tac >- gvs[get_instruction_def] >>
  disch_then (qspecl_then
    [`middle with vs_inst_idx := SUC u.vs_inst_idx`, `bb`, `r`, `v'`] mp_tac) >>
  simp[] >> impl_tac >- (gvs[run_from_def] >> metis_tac[]) >>
  strip_tac >> qexistsl_tac [`b`, `p`] >>
  metis_tac[cj 2 gas_path_rules, ADD]
QED

Resume frag_relabel_edge_exit_path_aux[jump]:
  gs[] >> Cases_on `fuel`
  >- gvs[Once run_blocks_def, exit_result_def] >>
  rename1 `run_blocks (SUC remaining) ctx (frag_relabel_observer sa sb L ids fn id) middle = r` >>
  qpat_x_assum `run_blocks _ _ _ _ = _` mp_tac >>
  simp[Once run_blocks_def] >>
  Cases_on `lookup_block middle.vs_current_bb (frag_relabel_observer sa sb L ids fn id).fn_blocks` >>
  simp[] >- (strip_tac >> gvs[exit_result_def]) >>
  rename1 `lookup_block middle.vs_current_bb (frag_relabel_observer sa sb L ids fn id).fn_blocks = SOME target` >>
  qspecl_then [`middle`, `target.bb_instructions`]
    strip_assume_tac eval_phis_ok_or_error_defs >> simp[] >> strip_tac
  >- suspend "entered" >> metis_tac[exit_result_def]
QED

Resume frag_relabel_edge_exit_path_aux[entered]:
  rename1 `eval_phis middle target.bb_instructions = OK entered` >>
  `entered.vs_current_bb = middle.vs_current_bb /\ ~entered.vs_halted` by
    metis_tac[eval_phis_preserves_current_bb, eval_phis_preserves_halted] >>
  `abi_observer_step ctx (frag_relabel_observer sa sb L ids fn id) (frag_observer_cut sb) u
     (entered with vs_inst_idx := phi_prefix_length target.bb_instructions)` by
    (simp[abi_observer_step_def, step_inst_non_invoke] >>
     qexistsl_tac [`bb`, `inst`, `middle`] >> simp[] >> metis_tac[]) >>
  drule_all frag_relabel_edge_step >> strip_tac >>
  `(middle.vs_current_bb,phi_prefix_length target.bb_instructions) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb)` by
    (drule_all frag_relabel_edge_region_closed >>
     rewrite_tac[observer_region_closed_def] >> disch_then drule >> simp[]) >>
  qpat_x_assum `!m. m < SUC remaining ==> _`
    (qspec_then `remaining` mp_tac) >> simp[] >>
  disch_then (qspecl_then
    [`entered with vs_inst_idx := phi_prefix_length target.bb_instructions`,
     `target`, `v'`] mp_tac) >>
  simp[] >> impl_tac >- (gvs[run_from_def] >> metis_tac[]) >>
  strip_tac >>
  `run_from remaining ctx (frag_relabel_observer sa sb L ids fn id)
     (entered with vs_inst_idx := phi_prefix_length target.bb_instructions) = r` by
    simp[run_from_def] >>
  qpat_x_assum `gas_path _ _ v' _ _` mp_tac >> simp[] >> strip_tac >>
  qexistsl_tac [`b`, `p`] >> qpat_x_assum `!m. _` kall_tac >>
  metis_tac[cj 2 gas_path_rules, ADD]
QED

Finalise frag_relabel_edge_exit_path_aux

Theorem frag_relabel_edge_exit_path:
  frag_relabel_edge_context sa sb L ids fn /\
  (u.vs_current_bb,u.vs_inst_idx) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
  ~u.vs_halted /\
  run_from fuel ctx (frag_relabel_observer sa sb L ids fn id) u = r /\
  exit_result r /\ (!h. r <> Halt h) /\
  frag_relabel_state L sa.cs_current_bb u v ==>
  ?b p. gas_path ctx fn v 0
    (exec_result_map (\t. t with <|vs_current_bb := b; vs_prev_bb := p|>) r)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `lookup_block u.vs_current_bb (frag_relabel_observer sa sb L ids fn id).fn_blocks`
  >- gvs[Once run_from_def, exit_result_def] >>
  irule frag_relabel_edge_exit_path_aux >> metis_tac[]
QED

Theorem frag_relabel_edge_prefix_path:
  !ctx observed cut u t. local_prefix ctx observed cut u t ==>
  !sa sb L ids fn id v.
    observed = frag_relabel_observer sa sb L ids fn id /\
    cut = frag_observer_cut sb /\
    frag_relabel_edge_context sa sb L ids fn /\
    (u.vs_current_bb,u.vs_inst_idx) IN
      frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
    frag_relabel_state L sa.cs_current_bb u v ==>
    ?t'. gas_path ctx fn v 0 (OK t') /\
         frag_relabel_state L sa.cs_current_bb t t'
Proof
  ho_match_mp_tac local_prefix_ind >> conj_tac
  >- (rpt strip_tac >> qexists_tac `v` >> simp[] >>
      irule (cj 1 gas_path_rules) >>
      drule frag_relabel_state_fields >> simp[]) >>
  rpt strip_tac >> gvs[] >>
  drule_all frag_relabel_edge_step >> strip_tac >>
  `observer_region_closed ctx (frag_relabel_observer sa sb L ids fn id)
    (frag_observer_cut sb)
    (frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb))` by
      (irule frag_relabel_edge_region_closed >> simp[]) >>
  `?t'. gas_path ctx fn v' 0 (OK t') /\
        frag_relabel_state L sa.cs_current_bb t t'` by
    (first_x_assum irule >> simp[] >>
     fs[observer_region_closed_def] >> metis_tac[]) >>
  qexists_tac `t'` >> simp[] >>
  metis_tac[cj 2 gas_path_rules, ADD]
QED

Theorem frag_relabel_edge_halt_prefix:
  frag_relabel_edge_context sa sb L ids fn /\
  (s.vs_current_bb,s.vs_inst_idx) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
  ~s.vs_halted /\
  run_from fuel ctx (frag_relabel_observer sa sb L ids fn id) s = Halt h /\
  (h.vs_current_bb,h.vs_inst_idx) = frag_observer_cut sb ==>
  ?u. local_prefix ctx (frag_relabel_observer sa sb L ids fn id)
       (frag_observer_cut sb) s u /\ stop_view u = h
Proof
  rpt strip_tac >>
  Cases_on `lookup_block s.vs_current_bb (frag_relabel_observer sa sb L ids fn id).fn_blocks`
  >- gvs[run_from_def] >>
  irule frag_cut_run_prefix_aux >> simp[] >> conj_tac
  >- (simp[frag_observer_cut_def, frag_relabel_observer_cut] >>
      rpt strip_tac >> gvs[] >> metis_tac[frag_observer_cut_instruction]) >>
  conj_tac >- metis_tac[] >>
  qexists_tac `frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb)` >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      mp_tac (Q.INST [`u` |-> `s with <|vs_current_bb := lbl; vs_inst_idx := idx|>`]
        (cj 2 frag_relabel_edge_off_cut_opcodes)) >> simp[]) >>
  metis_tac[frag_relabel_edge_region_closed]
QED

Theorem frag_exec_gas_path_relabel_edge:
  !ctx sa sb Q R fn s.
    (!L ids fn'.
       LENGTH ids = LENGTH sa.cs_current_insts /\
       fn_has_code (start_relabel L ids sa) (start_swap sa L ids sb) fn' /\
       fn_inst_ids_distinct fn' /\ fn'.fn_name = fn.fn_name /\
       (!i. MEM i (fn_insts fn') /\ i.inst_opcode <> STOP /\
            i.inst_opcode <> NOP ==> MEM i (fn_insts fn)) /\
       (!i. MEM i (fn_insts fn') ==> i.inst_opcode <> INVOKE) /\
       (sb.cs_current_insts <> [] \/
        !bb. lookup_block sb.cs_current_bb fn'.fn_blocks = SOME bb ==>
             phi_prefix_length bb.bb_instructions = 0) ==>
       (?t. Q t /\ ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
            t.vs_inst_idx = LENGTH sb.cs_current_insts /\
            !fuel r. run_from fuel ctx fn' t = r /\ (!e. r <> Error e) ==>
                     ?fuel'. run_from fuel' ctx fn' (s with vs_current_bb := L) = r) \/
       (?fuel r. run_from fuel ctx fn' (s with vs_current_bb := L) = r /\
                 exit_result r /\ R r)) /\
    sa.cs_blocks <> sb.cs_blocks /\ cs_extends sa sb /\ frag_ops_free sa sb /\
    ~MEM sb.cs_current_bb (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks sa sb))) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (frag_code sa sb)) /\
    (!t rd. Q t ==> Q (t with vs_returndata := rd)) /\
    (!t p. Q t ==> Q (t with vs_prev_bb := p)) /\ (!h. ~R (Halt h)) /\
    (!a t b p. R (Abort a t) ==>
       R (Abort a (t with <| vs_current_bb := b; vs_prev_bb := p |>))) /\
    (!v t b p. R (IntRet v t) ==>
       R (IntRet v (t with <| vs_current_bb := b; vs_prev_bb := p |>))) /\
    fn_has_code sa sb fn /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    (?t. gas_marked_path F ctx fn s 0 (OK t) /\ Q t /\ ~t.vs_halted /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts) \/
    (?r. gas_marked_path F ctx fn s 0 r /\ exit_result r /\ R r)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all frag_relabel_observer_exists >> strip_tac >>
  `frag_relabel_edge_context sa sb L ids fn` by simp[frag_relabel_edge_context_def] >>
  `(s with vs_current_bb := L).vs_inst_idx = LENGTH (start_relabel L ids sa).cs_current_insts` by
    simp[start_relabel_def] >>
  `((s with vs_current_bb := L).vs_current_bb,
     (s with vs_current_bb := L).vs_inst_idx) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb)` by
    (mp_tac (Q.INST [`sa` |-> `start_relabel L ids sa`,
       `sb` |-> `start_swap sa L ids sb`] frag_observer_start_region) >>
     simp[start_relabel_def, start_relabel_extends]) >>
  `frag_relabel_state L sa.cs_current_bb (s with vs_current_bb := L) s` by
    (irule frag_relabel_state_initial >> simp[]) >>
  `(frag_relabel_observer sa sb L ids fn id).fn_name = fn.fn_name` by
    simp[frag_relabel_observer_def] >>
  qpat_x_assum `!L ids fn'. _`
    (qspecl_then [`L`, `ids`, `frag_relabel_observer sa sb L ids fn id`] mp_tac) >>
  simp[] >> strip_tac
  >- suspend "normal" >> suspend "exit"
QED

Resume frag_exec_gas_path_relabel_edge[normal]:
  rename1 `Q t` >>
  `run_from 0 ctx (frag_relabel_observer sa sb L ids fn id) t = Halt (stop_view t)` by
    (irule run_from_stop_view >>
     qexistsl_tac [`<|bb_label := sb.cs_current_bb;
       bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []]|>`, `id`] >>
     simp[frag_relabel_observer_cut, frag_observer_cut_instruction]) >>
  `?fuel. run_from fuel ctx (frag_relabel_observer sa sb L ids fn id)
     (s with vs_current_bb := L) = Halt (stop_view t)` by
    (qpat_x_assum `!fuel. _` (qspec_then `0` mp_tac) >> simp[]) >>
  `?u. local_prefix ctx (frag_relabel_observer sa sb L ids fn id)
     (frag_observer_cut sb) (s with vs_current_bb := L) u /\ stop_view u = stop_view t` by
    (irule frag_relabel_edge_halt_prefix >>
     gvs[frag_observer_cut_def, stop_view_def, halt_state_def] >> metis_tac[]) >>
  `?v. gas_path ctx fn s 0 (OK v) /\ frag_relabel_state L sa.cs_current_bb u v` by
    (drule frag_relabel_edge_prefix_path >> disch_then irule >> simp[] >>
     qexistsl_tac [`id`, `ids`, `sb`] >> gvs[]) >>
  drule local_prefix_endpoint >> strip_tac >>
  `Q u` by (irule stop_view_closed_post >> metis_tac[]) >>
  `Q v` by (irule frag_relabel_state_post >> gvs[frag_observer_cut_def] >> metis_tac[]) >>
  drule frag_relabel_state_fields >> strip_tac >>
  disj1_tac >> qexists_tac `v` >>
  gvs[gas_marked_path_def, frag_observer_cut_def]
QED

Resume frag_exec_gas_path_relabel_edge[exit]:
  qmatch_asmsub_abbrev_tac `R r` >>
  `!h. r <> Halt h` by metis_tac[] >>
  `?b p. gas_path ctx fn s 0
    (exec_result_map (\t. t with <|vs_current_bb := b; vs_prev_bb := p|>) r)` by
    (irule frag_relabel_edge_exit_path >> simp[Abbr `r`] >>
     qpat_assum `frag_relabel_edge_context _ _ _ _ _`
       (irule_at (Pat `frag_relabel_edge_context _ _ _ _ _`)) >>
     qexistsl_tac [`s with vs_current_bb := L`, `id`, `fuel`] >> gvs[]) >>
  disj2_tac >>
  qexists_tac `exec_result_map (\t. t with <|vs_current_bb := b; vs_prev_bb := p|>) r` >>
  simp[gas_marked_path_def] >>
  Cases_on `r` >> gvs[exit_result_def, instIdxIndepTheory.exec_result_map_def] >> metis_tac[]
QED

Finalise frag_exec_gas_path_relabel_edge

Theorem abi_decode_sim_gas_path_relabel_edge:
  !ctx sa sb Q fn s.
    (!L ids fn'.
       LENGTH ids = LENGTH sa.cs_current_insts /\
       fn_has_code (start_relabel L ids sa) (start_swap sa L ids sb) fn' /\
       fn_inst_ids_distinct fn' /\ fn'.fn_name = fn.fn_name /\
       (!i. MEM i (fn_insts fn') /\ i.inst_opcode <> STOP /\
            i.inst_opcode <> NOP ==> MEM i (fn_insts fn)) /\
       (!i. MEM i (fn_insts fn') ==> i.inst_opcode <> INVOKE) /\
       (!bb. lookup_block sb.cs_current_bb fn'.fn_blocks = SOME bb ==>
             phi_prefix_length bb.bb_instructions = 0) ==>
       ?t. Q t /\ ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
           t.vs_inst_idx = LENGTH sb.cs_current_insts /\
           abi_decode_sim ctx fn' (s with vs_current_bb := L) t) /\
    sa.cs_blocks <> sb.cs_blocks /\ cs_extends sa sb /\ frag_ops_free sa sb /\
    ~MEM sb.cs_current_bb (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks sa sb))) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (frag_code sa sb)) /\
    (!t rd. Q t ==> Q (t with vs_returndata := rd)) /\
    (!t p. Q t ==> Q (t with vs_prev_bb := p)) /\
    fn_has_code sa sb fn /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path F ctx fn s 0 (OK t) /\ Q t /\ ~t.vs_halted /\
        t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all frag_relabel_observer_exists >> strip_tac >>
  `frag_relabel_edge_context sa sb L ids fn` by simp[frag_relabel_edge_context_def] >>
  `(s with vs_current_bb := L).vs_inst_idx = LENGTH (start_relabel L ids sa).cs_current_insts` by
    simp[start_relabel_def] >>
  `((s with vs_current_bb := L).vs_current_bb,
    (s with vs_current_bb := L).vs_inst_idx) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb)` by
    (mp_tac (Q.INST [`sa` |-> `start_relabel L ids sa`,
       `sb` |-> `start_swap sa L ids sb`] frag_observer_start_region) >>
     simp[start_relabel_def, start_relabel_extends]) >>
  `frag_relabel_state L sa.cs_current_bb (s with vs_current_bb := L) s` by
    (irule frag_relabel_state_initial >> simp[]) >>
  `(frag_relabel_observer sa sb L ids fn id).fn_name = fn.fn_name` by
    simp[frag_relabel_observer_def] >>
  qpat_x_assum `!L ids fn'. _`
    (qspecl_then [`L`, `ids`, `frag_relabel_observer sa sb L ids fn id`] mp_tac) >>
  simp[] >> strip_tac >> rename1 `Q t` >>
  `?fuel. run_from fuel ctx (frag_relabel_observer sa sb L ids fn id)
     (s with vs_current_bb := L) = Halt (stop_view t)` by
    (irule abi_decode_sim_stop_run >> simp[] >>
     qexistsl_tac [`<|bb_label := sb.cs_current_bb;
       bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []]|>`, `id`] >>
     simp[frag_relabel_observer_cut, frag_observer_cut_instruction]) >>
  `?u. local_prefix ctx (frag_relabel_observer sa sb L ids fn id)
     (frag_observer_cut sb) (s with vs_current_bb := L) u /\ stop_view u = stop_view t` by
    (irule frag_relabel_edge_halt_prefix >>
     gvs[frag_observer_cut_def, stop_view_def, halt_state_def] >> metis_tac[]) >>
  `?v. gas_path ctx fn s 0 (OK v) /\ frag_relabel_state L sa.cs_current_bb u v` by
    (drule frag_relabel_edge_prefix_path >> disch_then irule >> simp[] >>
     qexistsl_tac [`id`, `ids`, `sb`] >> gvs[]) >>
  drule local_prefix_endpoint >> strip_tac >>
  `Q u` by (irule stop_view_closed_post >> metis_tac[]) >>
  `Q v` by (irule frag_relabel_state_post >> gvs[frag_observer_cut_def] >> metis_tac[]) >>
  drule frag_relabel_state_fields >> strip_tac >>
  qexists_tac `v` >> gvs[gas_marked_path_def, frag_observer_cut_def]
QED
