(* Opcode boundary for replacing exactly the three FMP fields. *)
Theory ctxFmpBaseHelpers
Ancestors
  ctxFmpUpdateHelpers instIdxIndep venomExecSemantics venomState venomInst venomCallOracleDefs
Libs
  listTheory pairTheory BasicProvers

val fmp_rw = map (SRULE []) [eval_operand_fmp_update, eval_operands_fmp_update,
  update_var_fmp_update, read_memory_fmp_update,
  write_memory_with_expansion_fmp_update, halt_state_fmp_update,
  revert_state_fmp_update, set_returndata_fmp_update,
  mstore_fmp_update, mstore8_fmp_update, istore_fmp_update,
  mcopy_fmp_update, sload_fmp_update, tload_fmp_update,
  sstore_fmp_update, tstore_fmp_update, mload_fmp_update,
  jump_to_fmp_update, exec_result_map_def];

Theorem exec_pure1_fmp_update[local]:
  !f inst s p i c.
  exec_pure1 f inst (s with <|vs_fmp := p; vs_call_entry_fmp := c; vs_initial_fmp := i|>) =
  exec_result_map (\t. t with <|vs_fmp := p; vs_call_entry_fmp := c; vs_initial_fmp := i|>) (exec_pure1 f inst s)
Proof
  rpt gen_tac >> simp ([exec_pure1_def] @ fmp_rw) >>
  EVERY_CASE_TAC >> simp fmp_rw
QED

Theorem exec_pure2_fmp_update[local]:
  !f inst s p i c.
  exec_pure2 f inst (s with <|vs_fmp := p; vs_call_entry_fmp := c; vs_initial_fmp := i|>) =
  exec_result_map (\t. t with <|vs_fmp := p; vs_call_entry_fmp := c; vs_initial_fmp := i|>) (exec_pure2 f inst s)
Proof
  rpt gen_tac >> simp ([exec_pure2_def] @ fmp_rw) >>
  EVERY_CASE_TAC >> simp fmp_rw
QED

Theorem exec_pure3_fmp_update[local]:
  !f inst s p i c.
  exec_pure3 f inst (s with <|vs_fmp := p; vs_call_entry_fmp := c; vs_initial_fmp := i|>) =
  exec_result_map (\t. t with <|vs_fmp := p; vs_call_entry_fmp := c; vs_initial_fmp := i|>) (exec_pure3 f inst s)
Proof
  rpt gen_tac >> simp ([exec_pure3_def] @ fmp_rw) >>
  EVERY_CASE_TAC >> simp fmp_rw
QED

Theorem exec_read0_fmp_update[local]:
  !g inst s p i c.
  (!s p i c. g (s with <|vs_fmp := p; vs_call_entry_fmp := c; vs_initial_fmp := i|>) = g s) ==>
  exec_read0 g inst (s with <|vs_fmp := p; vs_call_entry_fmp := c; vs_initial_fmp := i|>) =
  exec_result_map (\t. t with <|vs_fmp := p; vs_call_entry_fmp := c; vs_initial_fmp := i|>) (exec_read0 g inst s)
Proof
  rpt strip_tac >> simp ([exec_read0_def] @ fmp_rw) >>
  EVERY_CASE_TAC >> simp fmp_rw
QED

Theorem exec_read1_fmp_update[local]:
  !g inst s p i c.
  (!v s p i c. g v (s with <|vs_fmp := p; vs_call_entry_fmp := c; vs_initial_fmp := i|>) = g v s) ==>
  exec_read1 g inst (s with <|vs_fmp := p; vs_call_entry_fmp := c; vs_initial_fmp := i|>) =
  exec_result_map (\t. t with <|vs_fmp := p; vs_call_entry_fmp := c; vs_initial_fmp := i|>) (exec_read1 g inst s)
Proof
  rpt strip_tac >> simp ([exec_read1_def] @ fmp_rw) >>
  EVERY_CASE_TAC >> simp fmp_rw
QED

Theorem exec_write2_fmp_update[local]:
  !f inst s p i c.
  (!v w s p i c. f v w (s with <|vs_fmp := p; vs_call_entry_fmp := c; vs_initial_fmp := i|>) =
    (f v w s) with <|vs_fmp := p; vs_call_entry_fmp := c; vs_initial_fmp := i|>) ==>
  exec_write2 f inst (s with <|vs_fmp := p; vs_call_entry_fmp := c; vs_initial_fmp := i|>) =
  exec_result_map (\t. t with <|vs_fmp := p; vs_call_entry_fmp := c; vs_initial_fmp := i|>) (exec_write2 f inst s)
Proof
  rpt strip_tac >> simp ([exec_write2_def] @ fmp_rw) >>
  EVERY_CASE_TAC >> simp fmp_rw
QED

Theorem exec_gas_fmp_update[local]:
  !inst s p i c.
  exec_gas inst (s with <|vs_fmp := p; vs_call_entry_fmp := c; vs_initial_fmp := i|>) =
  exec_result_map (\t. t with <|vs_fmp := p; vs_call_entry_fmp := c; vs_initial_fmp := i|>) (exec_gas inst s)
Proof
  rpt gen_tac >> simp[exec_gas_def, update_var_def, exec_result_map_def] >>
  EVERY_CASE_TAC >> simp[exec_result_map_def]
QED

Theorem exec_alloca_fmp_update[local]:
  !inst s sz p i c.
  exec_alloca inst (s with <|vs_fmp := p; vs_call_entry_fmp := c; vs_initial_fmp := i|>) sz =
  exec_result_map (\t. t with <|vs_fmp := p; vs_call_entry_fmp := c; vs_initial_fmp := i|>) (exec_alloca inst s sz)
Proof
  rpt gen_tac >> simp[exec_alloca_def] >> EVERY_CASE_TAC >>
  simp[exec_result_map_def, update_var_def, venom_state_component_equality]
QED

Theorem venom_to_tx_params_fmp_update[local]:
  !s p i c.
  venom_to_tx_params (s with <|vs_fmp := p; vs_call_entry_fmp := c; vs_initial_fmp := i|>) = venom_to_tx_params s
Proof
  simp[venom_to_tx_params_def]
QED

Theorem make_venom_call_state_fmp_update[local]:
  !s target gas value calldata code is_static p i c.
  make_venom_call_state (s with <|vs_fmp := p; vs_call_entry_fmp := c; vs_initial_fmp := i|>) target gas value calldata code is_static =
  make_venom_call_state s target gas value calldata code is_static
Proof
  simp[make_venom_call_state_def, venom_to_tx_params_fmp_update]
QED

Theorem extract_venom_result_fmp_update[local]:
  !s output_val retOff retSize run_result p i c.
  extract_venom_result (s with <|vs_fmp := p; vs_call_entry_fmp := c; vs_initial_fmp := i|>) output_val retOff retSize run_result =
  OPTION_MAP (\v. (FST v, (SND v) with <|vs_fmp := p; vs_call_entry_fmp := c; vs_initial_fmp := i|>))
    (extract_venom_result s output_val retOff retSize run_result)
Proof
  rpt gen_tac >> simp[extract_venom_result_def] >>
  Cases_on `run_result` >> simp[] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `x1.contexts` >> simp[] >>
  Cases_on `h` >> Cases_on `t` >> simp[] >>
  Cases_on `x0` >>
  simp[write_memory_with_expansion_def, venom_state_component_equality] >>
  Cases_on `y` >>
  simp[write_memory_with_expansion_def, venom_state_component_equality]
QED

val ext_rw = map (SRULE []) [read_memory_fmp_update, extract_venom_result_fmp_update,
  update_var_fmp_update, exec_result_map_def, update_var_def,
  venom_state_component_equality];

Theorem exec_ext_call_fmp_update[local]:
  !inst s gas addr value ao az ro rz is_static p i c.
  exec_ext_call inst (s with <|vs_fmp := p; vs_call_entry_fmp := c; vs_initial_fmp := i|>) gas addr value ao az ro rz is_static =
  exec_result_map (\t. t with <|vs_fmp := p; vs_call_entry_fmp := c; vs_initial_fmp := i|>) (exec_ext_call inst s gas addr value ao az ro rz is_static)
Proof
  rpt gen_tac >>
  simp([exec_ext_call_def, venom_call_request_def,
    write_memory_with_expansion_def, make_venom_call_state_fmp_update] @ ext_rw) >>
  EVERY_CASE_TAC >> simp ext_rw
QED

Theorem exec_delegatecall_fmp_update[local]:
  !inst s gas addr ao az ro rz p i c.
  exec_delegatecall inst (s with <|vs_fmp := p; vs_call_entry_fmp := c; vs_initial_fmp := i|>) gas addr ao az ro rz =
  exec_result_map (\t. t with <|vs_fmp := p; vs_call_entry_fmp := c; vs_initial_fmp := i|>) (exec_delegatecall inst s gas addr ao az ro rz)
Proof
  rpt gen_tac >>
  simp([exec_delegatecall_def, venom_call_request_def,
    write_memory_with_expansion_def] @ ext_rw) >>
  EVERY_CASE_TAC >> simp ext_rw
QED

Theorem exec_create_fmp_update[local]:
  !inst s value offset sz salt_opt p i c.
  exec_create inst (s with <|vs_fmp := p; vs_call_entry_fmp := c; vs_initial_fmp := i|>) value offset sz salt_opt =
  exec_result_map (\t. t with <|vs_fmp := p; vs_call_entry_fmp := c; vs_initial_fmp := i|>) (exec_create inst s value offset sz salt_opt)
Proof
  rpt gen_tac >>
  simp([exec_create_def, venom_create_request_def, halt_state_def,
    set_returndata_def] @ ext_rw) >>
  EVERY_CASE_TAC >> simp ext_rw
QED

Theorem step_inst_base_fmp_update:
  !inst s p i c.
    ~is_raw_fmp_opcode inst.inst_opcode /\ inst.inst_opcode <> INITIAL_FMP ==>
    step_inst_base inst (s with <|vs_fmp := p; vs_call_entry_fmp := c; vs_initial_fmp := i|>) =
    exec_result_map (\t. t with <|vs_fmp := p; vs_call_entry_fmp := c; vs_initial_fmp := i|>) (step_inst_base inst s)
Proof
  rpt gen_tac >> Cases_on `inst.inst_opcode` >>
  (simp[is_raw_fmp_opcode_def] >>
   simp[step_inst_base_def, exec_pure1_fmp_update, exec_pure2_fmp_update,
     exec_pure3_fmp_update, exec_gas_fmp_update, exec_alloca_fmp_update] >>
   TRY (irule exec_read0_fmp_update >> simp fmp_rw >> NO_TAC) >>
   TRY (irule exec_read1_fmp_update >> simp fmp_rw >> NO_TAC) >>
   TRY (irule exec_write2_fmp_update >> simp fmp_rw >> NO_TAC) >>
   simp[eval_operand_fmp_update, eval_operands_fmp_update,
     exec_ext_call_fmp_update, exec_delegatecall_fmp_update, exec_create_fmp_update] >>
   simp fmp_rw >>
   EVERY_CASE_TAC >>
   simp(fmp_rw @ [halt_state_def, set_returndata_def, venom_state_component_equality]) >>
   irule exec_write2_fmp_update >> simp fmp_rw)
QED
