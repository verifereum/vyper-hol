Theory dftGasTransferAudit
Ancestors
  passSharedDefs venomExecSemantics venomEffects venomState venomInst
  venomInstProps list

(* GAS cannot instantiate the effect-free transfer theorem: its classification
   premise is false under the current semantics. *)
Theorem gas_transfer_audit:
  !s i x.
  let inst = i with <| inst_opcode := GAS; inst_operands := []; inst_outputs := [x] |>;
      s1 = s with vs_gas_readings := [0w];
      s2 = s with vs_gas_readings := [1w];
      v1 = update_var x 0w (s with vs_gas_readings := []);
      v2 = update_var x 1w (s with vs_gas_readings := [])
  in
    step_inst_base inst s1 = OK v1 /\
    step_inst_base inst s2 = OK v2 /\
    ~is_effect_free_op inst.inst_opcode /\
    inst.inst_opcode <> NOP /\ inst.inst_opcode <> PHI /\
    (!op. MEM op inst.inst_operands ==> eval_operand op s1 = eval_operand op s2) /\
    (inst.inst_opcode = PHI ==> s1.vs_prev_bb = s2.vs_prev_bb) /\
    (inst.inst_opcode = PARAM ==> s1.vs_params = s2.vs_params) /\
    (inst.inst_opcode = FMP_PARAM ==> s1.vs_params = s2.vs_params) /\
    (inst.inst_opcode = GETFMP ==> s1.vs_fmp = s2.vs_fmp) /\
    (inst.inst_opcode = INITIAL_FMP ==> s1.vs_initial_fmp = s2.vs_initial_fmp) /\
    (inst.inst_opcode = RETPC_PARAM ==> s1.vs_return_pc_token = s2.vs_return_pc_token) /\
    s1.vs_call_ctx = s2.vs_call_ctx /\
    s1.vs_tx_ctx = s2.vs_tx_ctx /\
    s1.vs_block_ctx = s2.vs_block_ctx /\
    s1.vs_data_section = s2.vs_data_section /\
    s1.vs_labels = s2.vs_labels /\ s1.vs_code = s2.vs_code /\
    s1.vs_prev_hashes = s2.vs_prev_hashes /\
    (Eff_MEMORY IN read_effects inst.inst_opcode ==> s1.vs_memory = s2.vs_memory) /\
    (Eff_TRANSIENT IN read_effects inst.inst_opcode ==> s1.vs_transient = s2.vs_transient) /\
    (Eff_STORAGE IN read_effects inst.inst_opcode ==> s1.vs_accounts = s2.vs_accounts) /\
    (Eff_BALANCE IN read_effects inst.inst_opcode ==> s1.vs_accounts = s2.vs_accounts) /\
    (Eff_EXTCODE IN read_effects inst.inst_opcode ==> s1.vs_accounts = s2.vs_accounts) /\
    (Eff_IMMUTABLES IN read_effects inst.inst_opcode ==> s1.vs_immutables = s2.vs_immutables) /\
    (Eff_RETURNDATA IN read_effects inst.inst_opcode ==> s1.vs_returndata = s2.vs_returndata) /\
    (Eff_LOG IN read_effects inst.inst_opcode ==> s1.vs_logs = s2.vs_logs) /\
    MEM x inst.inst_outputs /\ lookup_var x v1 <> lookup_var x v2
Proof
  simp[step_inst_base_def, exec_gas_def, is_effect_free_op_def,
       is_terminator_def, read_effects_def, write_effects_def,
       empty_effects_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED
