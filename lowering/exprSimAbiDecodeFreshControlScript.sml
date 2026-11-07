Theory exprSimAbiDecodeFreshControl
Ancestors
  exprSimAbiDecodeFreshBoundary exprSimAbiGasBridge
  fragGasPath gasCount venomExecProofs venomInstProps venomInst
  venomExecSemantics venomState list instIdxIndep fragExec

Theorem abi_decode_fresh_base_nonphi[local]:
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

Theorem abi_decode_fresh_ordinary_edge:
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
  drule_all abi_decode_fresh_base_nonphi >>
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

Theorem abi_decode_fresh_eval_operand_control[local]:
  !op s b p.
    eval_operand op (s with <|vs_prev_bb := p; vs_current_bb := b|>) =
    eval_operand op s
Proof
  Cases >> simp[eval_operand_def, lookup_var_def]
QED

Theorem abi_decode_fresh_jump_control:
  MEM inst.inst_opcode [JMP; JNZ; DJMP] /\ step_inst_base inst u = OK middle ==>
  step_inst_base inst (u with <|vs_current_bb := b; vs_prev_bb := p|>) =
    OK (middle with vs_prev_bb := SOME b)
Proof
  simp[MEM] >> strip_tac >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs] >>
  simp[abi_decode_fresh_eval_operand_control] >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  simp[jump_to_def, venom_state_component_equality]
QED

Theorem abi_decode_fresh_eval_operands_control[local]:
  !ops s b p.
    eval_operands ops (s with <|vs_prev_bb := p; vs_current_bb := b|>) =
    eval_operands ops s
Proof
  Induct >> simp[eval_operands_def, abi_decode_fresh_eval_operand_control]
QED

Theorem abi_decode_fresh_pure1_control[local]:
  exec_pure1 f inst (s with <|vs_prev_bb := p; vs_current_bb := b|>) =
    exec_result_map (\t. t with <|vs_prev_bb := p; vs_current_bb := b|>)
      (exec_pure1 f inst s)
Proof
  namedCases_on `inst.inst_operands` ["", "a ops"]
  >- simp[exec_pure1_def, instIdxIndepTheory.exec_result_map_def] >>
  Cases_on `ops`
  >- (simp[exec_pure1_def, abi_decode_fresh_eval_operand_control] >>
      Cases_on `eval_operand a s` >>
      simp[instIdxIndepTheory.exec_result_map_def] >>
      namedCases_on `inst.inst_outputs` ["", "out outs"] >>
      simp[instIdxIndepTheory.exec_result_map_def] >>
      Cases_on `outs` >>
      simp[instIdxIndepTheory.exec_result_map_def, update_var_def]) >>
  simp[exec_pure1_def, instIdxIndepTheory.exec_result_map_def]
QED

Theorem abi_decode_fresh_pure2_control[local]:
  exec_pure2 f inst (s with <|vs_prev_bb := p; vs_current_bb := b|>) =
    exec_result_map (\t. t with <|vs_prev_bb := p; vs_current_bb := b|>)
      (exec_pure2 f inst s)
Proof
  namedCases_on `inst.inst_operands` ["", "a ops"]
  >- simp[exec_pure2_def, instIdxIndepTheory.exec_result_map_def] >>
  namedCases_on `ops` ["", "c rest"]
  >- simp[exec_pure2_def, instIdxIndepTheory.exec_result_map_def] >>
  Cases_on `rest`
  >- (simp[exec_pure2_def, abi_decode_fresh_eval_operand_control] >>
      Cases_on `eval_operand a s` >> simp[instIdxIndepTheory.exec_result_map_def] >>
      Cases_on `eval_operand c s` >> simp[instIdxIndepTheory.exec_result_map_def] >>
      namedCases_on `inst.inst_outputs` ["", "out outs"] >>
      simp[instIdxIndepTheory.exec_result_map_def] >> Cases_on `outs` >>
      simp[instIdxIndepTheory.exec_result_map_def, update_var_def]) >>
  simp[exec_pure2_def, instIdxIndepTheory.exec_result_map_def]
QED

Theorem abi_decode_fresh_pure3_control[local]:
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
  >- (simp[exec_pure3_def, abi_decode_fresh_eval_operand_control] >>
      Cases_on `eval_operand a s` >> simp[instIdxIndepTheory.exec_result_map_def] >>
      Cases_on `eval_operand c s` >> simp[instIdxIndepTheory.exec_result_map_def] >>
      Cases_on `eval_operand d s` >> simp[instIdxIndepTheory.exec_result_map_def] >>
      namedCases_on `inst.inst_outputs` ["", "out outs"] >>
      simp[instIdxIndepTheory.exec_result_map_def] >> Cases_on `outs` >>
      simp[instIdxIndepTheory.exec_result_map_def, update_var_def]) >>
  simp[exec_pure3_def, instIdxIndepTheory.exec_result_map_def]
QED

Theorem abi_decode_fresh_call_request_control[local]:
  venom_call_request (s with <|vs_prev_bb := p; vs_current_bb := b|>)
    addr value off sz static = venom_call_request s addr value off sz static
Proof
  simp[venomCallOracleDefsTheory.venom_call_request_def, read_memory_def]
QED

Theorem abi_decode_fresh_create_request_control[local]:
  venom_create_request (s with <|vs_prev_bb := p; vs_current_bb := b|>)
    value off sz salt = venom_create_request s value off sz salt
Proof
  simp[venomCallOracleDefsTheory.venom_create_request_def, read_memory_def]
QED

Theorem abi_decode_fresh_ext_call_control[local]:
  exec_ext_call inst (s with <|vs_prev_bb := p; vs_current_bb := b|>)
    gas addr value ao az ro rz static =
    exec_result_map (\t. t with <|vs_prev_bb := p; vs_current_bb := b|>)
      (exec_ext_call inst s gas addr value ao az ro rz static)
Proof
  namedCases_on `inst.inst_outputs` ["", "out outs"]
  >- simp[exec_ext_call_def, instIdxIndepTheory.exec_result_map_def] >>
  Cases_on `outs` >>
  simp[exec_ext_call_def, abi_decode_fresh_call_request_control,
       venomCallOracleDefsTheory.consume_call_outcome_eq,
       write_memory_with_expansion_def, update_var_def,
       instIdxIndepTheory.exec_result_map_def]
QED

Theorem abi_decode_fresh_create_control[local]:
  exec_create inst (s with <|vs_prev_bb := p; vs_current_bb := b|>)
    value off sz salt =
    exec_result_map (\t. t with <|vs_prev_bb := p; vs_current_bb := b|>)
      (exec_create inst s value off sz salt)
Proof
  namedCases_on `inst.inst_outputs` ["", "out outs"]
  >- simp[exec_create_def, instIdxIndepTheory.exec_result_map_def] >>
  Cases_on `outs` >>
  simp[exec_create_def, abi_decode_fresh_create_request_control,
       venomCallOracleDefsTheory.consume_create_outcome_eq,
       update_var_def, halt_state_def, set_returndata_def,
       instIdxIndepTheory.exec_result_map_def] >>
  IF_CASES_TAC >> simp[instIdxIndepTheory.exec_result_map_def]
QED

Theorem abi_decode_fresh_delegate_state_control[local]:
  make_venom_delegatecall_state
    (s with <|vs_prev_bb := p; vs_current_bb := b|>) target gas data code static =
  make_venom_delegatecall_state s target gas data code static
Proof
  simp[make_venom_delegatecall_state_def, venom_to_tx_params_def]
QED

Theorem abi_decode_fresh_extract_control[local]:
  extract_venom_result (s with <|vs_prev_bb := p; vs_current_bb := b|>)
    output ro rz result =
  OPTION_MAP (\v. (FST v, SND v with <|vs_prev_bb := p; vs_current_bb := b|>))
    (extract_venom_result s output ro rz result)
Proof
  Cases_on `result` >- simp[extract_venom_result_def] >>
  rename1 `SOME pair` >> PairCases_on `pair` >>
  simp[extract_venom_result_def] >>
  namedCases_on `pair1.contexts` ["", "ctxt rest"] >> simp[] >>
  Cases_on `rest` >> simp[] >> PairCases_on `ctxt` >>
  Cases_on `pair0` >> simp[write_memory_with_expansion_def] >>
  qmatch_goalsub_rename_tac `case outcome of NONE => _ | SOME _ => _` >>
  Cases_on `outcome` >> simp[write_memory_with_expansion_def]
QED

Theorem abi_decode_fresh_delegatecall_control[local]:
  exec_delegatecall inst (s with <|vs_prev_bb := p; vs_current_bb := b|>)
    gas addr ao az ro rz =
    exec_result_map (\t. t with <|vs_prev_bb := p; vs_current_bb := b|>)
      (exec_delegatecall inst s gas addr ao az ro rz)
Proof
  simp[exec_delegatecall_def, read_memory_def, abi_decode_fresh_delegate_state_control,
       abi_decode_fresh_extract_control] >>
  qmatch_goalsub_abbrev_tac `extract_venom_result s 1w (w2n ro) (w2n rz) run_result` >>
  Cases_on `extract_venom_result s 1w (w2n ro) (w2n rz) run_result` >>
  simp[instIdxIndepTheory.exec_result_map_def] >>
  rename1 `_ = SOME pair` >> PairCases_on `pair` >> simp[] >>
  namedCases_on `inst.inst_outputs` ["", "out outs"] >>
  simp[instIdxIndepTheory.exec_result_map_def] >>
  Cases_on `outs` >> simp[instIdxIndepTheory.exec_result_map_def, update_var_def]
QED

Theorem abi_decode_fresh_read0_control[local]:
  f (s with <|vs_prev_bb := p; vs_current_bb := b|>) = f s ==>
  exec_read0 f inst (s with <|vs_prev_bb := p; vs_current_bb := b|>) =
    exec_result_map (\t. t with <|vs_prev_bb := p; vs_current_bb := b|>)
      (exec_read0 f inst s)
Proof
  strip_tac >> namedCases_on `inst.inst_outputs` ["", "out outs"] >>
  simp[exec_read0_def, instIdxIndepTheory.exec_result_map_def] >> Cases_on `outs` >>
  simp[exec_read0_def, instIdxIndepTheory.exec_result_map_def, update_var_def]
QED

Theorem abi_decode_fresh_read1_control[local]:
  (!v. f v (s with <|vs_prev_bb := p; vs_current_bb := b|>) = f v s) ==>
  exec_read1 f inst (s with <|vs_prev_bb := p; vs_current_bb := b|>) =
    exec_result_map (\t. t with <|vs_prev_bb := p; vs_current_bb := b|>)
      (exec_read1 f inst s)
Proof
  strip_tac >> namedCases_on `inst.inst_operands` ["", "a ops"]
  >- simp[exec_read1_def, instIdxIndepTheory.exec_result_map_def] >>
  Cases_on `ops`
  >- (simp[exec_read1_def, abi_decode_fresh_eval_operand_control] >>
      Cases_on `eval_operand a s` >> simp[instIdxIndepTheory.exec_result_map_def] >>
      namedCases_on `inst.inst_outputs` ["", "out outs"] >>
      simp[instIdxIndepTheory.exec_result_map_def] >> Cases_on `outs` >>
      simp[instIdxIndepTheory.exec_result_map_def, update_var_def]) >>
  simp[exec_read1_def, instIdxIndepTheory.exec_result_map_def]
QED

Theorem abi_decode_fresh_write2_control[local]:
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
  >- (simp[exec_write2_def, abi_decode_fresh_eval_operand_control] >>
      Cases_on `eval_operand a s` >> simp[instIdxIndepTheory.exec_result_map_def] >>
      Cases_on `eval_operand c s` >> simp[instIdxIndepTheory.exec_result_map_def]) >>
  simp[exec_write2_def, instIdxIndepTheory.exec_result_map_def]
QED

Theorem abi_decode_fresh_base_abort[local]:
  inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> PHI /\
  step_inst_base inst s = Abort a t ==>
  step_inst_base inst (s with <|vs_current_bb := b; vs_prev_bb := p|>) =
    Abort a (t with <|vs_current_bb := b; vs_prev_bb := p|>)
Proof
  Cases_on `inst.inst_opcode` >> simp[] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs] >>
  simp[abi_decode_fresh_pure1_control, abi_decode_fresh_pure2_control,
       abi_decode_fresh_pure3_control, abi_decode_fresh_ext_call_control,
       abi_decode_fresh_create_control, abi_decode_fresh_delegatecall_control,
       abi_decode_fresh_read0_control, abi_decode_fresh_read1_control,
       abi_decode_fresh_write2_control,
       mload_def, sload_def, tload_def, contract_storage_def, contract_transient_def,
       mstore_def, mstore8_def, istore_def, sstore_def, tstore_def,
       write_memory_with_expansion_def,
       instIdxIndepTheory.exec_result_map_def] >>
  simp[abi_decode_fresh_eval_operand_control, abi_decode_fresh_eval_operands_control] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  gvs[instIdxIndepTheory.exec_result_map_def, halt_state_def, set_returndata_def,
      revert_state_def, exec_alloca_def, exec_gas_def, AllCaseEqs()] >>
  qpat_x_assum `_ = Abort _ _` mp_tac >> pairarg_tac >> simp[]
QED

Theorem abi_decode_fresh_mcopy_control[local]:
  mcopy dst src sz (s with <|vs_prev_bb := p; vs_current_bb := b|>) =
    (mcopy dst src sz s) with <|vs_prev_bb := p; vs_current_bb := b|>
Proof
  simp[mcopy_def, read_memory_def, write_memory_with_expansion_def]
QED

Theorem abi_decode_fresh_pack_dret_control[local]:
  !pairs cursor s b p.
  pack_dret_dynamic cursor pairs (s with <|vs_prev_bb := p; vs_current_bb := b|>) =
    (FST (pack_dret_dynamic cursor pairs s),
     FST (SND (pack_dret_dynamic cursor pairs s)),
     (SND (SND (pack_dret_dynamic cursor pairs s))) with
       <|vs_current_bb := b; vs_prev_bb := p|>)
Proof
  Induct >- simp[pack_dret_dynamic_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[pack_dret_dynamic_def, abi_decode_fresh_mcopy_control] >>
  first_x_assum (fn th => rewrite_tac[th]) >>
  pairarg_tac >> simp[]
QED

Theorem abi_decode_fresh_base_intret[local]:
  inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> PHI /\
  step_inst_base inst s = IntRet vals t ==>
  step_inst_base inst (s with <|vs_current_bb := b; vs_prev_bb := p|>) =
    IntRet vals (t with <|vs_current_bb := b; vs_prev_bb := p|>)
Proof
  Cases_on `inst.inst_opcode` >> simp[] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs] >>
  simp[abi_decode_fresh_pure1_control, abi_decode_fresh_pure2_control,
       abi_decode_fresh_pure3_control, abi_decode_fresh_ext_call_control,
       abi_decode_fresh_create_control, abi_decode_fresh_delegatecall_control,
       abi_decode_fresh_read0_control, abi_decode_fresh_read1_control,
       abi_decode_fresh_write2_control,
       mload_def, sload_def, tload_def, contract_storage_def, contract_transient_def,
       mstore_def, mstore8_def, istore_def, sstore_def, tstore_def,
       write_memory_with_expansion_def,
       instIdxIndepTheory.exec_result_map_def] >>
  simp[abi_decode_fresh_eval_operand_control, abi_decode_fresh_eval_operands_control] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  gvs[instIdxIndepTheory.exec_result_map_def, halt_state_def, set_returndata_def,
      revert_state_def, exec_alloca_def, exec_gas_def, AllCaseEqs()] >>
  rewrite_tac[abi_decode_fresh_pack_dret_control] >>
  qpat_x_assum `_ = IntRet _ _` mp_tac >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[]
QED

Theorem abi_decode_fresh_base_exit:
  inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> PHI /\
  step_inst_base inst u = r /\ exit_result r /\ (!h. r <> Halt h) ==>
  step_inst_base inst (u with <|vs_current_bb := b; vs_prev_bb := p|>) =
    exec_result_map (\t. t with <|vs_current_bb := b; vs_prev_bb := p|>) r
Proof
  Cases_on `r` >> simp[exit_result_def, instIdxIndepTheory.exec_result_map_def] >>
  (rpt strip_tac)
  >- (irule (SRULE [] abi_decode_fresh_base_abort) >> simp[])
  >> irule (SRULE [] abi_decode_fresh_base_intret) >> simp[]
QED
