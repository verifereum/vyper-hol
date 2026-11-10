Theory cseRootReplayProps
Ancestors cseReplayProps cseObservationProps availExprDefs venomWf venomInst venomEffects venomExecSemantics venomInstProps venomState
Libs cseReplayLib

Theorem exec_pure1_output_replay:
 src.inst_outputs = [y] /\ inst.inst_outputs = [x] /\
 exec_pure1 f src u = OK v /\ exec_pure1 f inst s = OK t /\
 MAP (\op. eval_operand op u) src.inst_operands =
 MAP (\op. eval_operand op s) inst.inst_operands ==>
 lookup_var x t = lookup_var y v
Proof
 simp[exec_pure1_def, AllCaseEqs()] >> rpt strip_tac >>
 gvs[lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem exec_pure2_output_replay:
 src.inst_outputs = [y] /\ inst.inst_outputs = [x] /\
 exec_pure2 f src u = OK v /\ exec_pure2 f inst s = OK t /\
 (MAP (\op. eval_operand op u) src.inst_operands =
    MAP (\op. eval_operand op s) inst.inst_operands \/
  ((!a b. f a b = f b a) /\
   MAP (\op. eval_operand op u) src.inst_operands =
   REVERSE (MAP (\op. eval_operand op s) inst.inst_operands))) ==>
 lookup_var x t = lookup_var y v
Proof
 simp[exec_pure2_def, AllCaseEqs()] >> rpt strip_tac >>
 gvs[lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem exec_pure3_output_replay:
 src.inst_outputs = [y] /\ inst.inst_outputs = [x] /\
 exec_pure3 f src u = OK v /\ exec_pure3 f inst s = OK t /\
 MAP (\op. eval_operand op u) src.inst_operands =
 MAP (\op. eval_operand op s) inst.inst_operands ==>
 lookup_var x t = lookup_var y v
Proof
 simp[exec_pure3_def, AllCaseEqs()] >> rpt strip_tac >>
 gvs[lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem exec_read0_output_replay:
 src.inst_outputs = [y] /\ inst.inst_outputs = [x] /\
 exec_read0 f src u = OK v /\ exec_read0 g inst s = OK t /\
 f u = g s ==>
 lookup_var x t = lookup_var y v
Proof
 simp[exec_read0_def] >> rpt strip_tac >>
 gvs[lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem exec_read1_output_replay:
 src.inst_outputs = [y] /\ inst.inst_outputs = [x] /\
 exec_read1 f src u = OK v /\ exec_read1 g inst s = OK t /\
 (!a. f a u = g a s) /\
 MAP (\op. eval_operand op u) src.inst_operands =
 MAP (\op. eval_operand op s) inst.inst_operands ==>
 lookup_var x t = lookup_var y v
Proof
 simp[exec_read1_def, AllCaseEqs()] >> rpt strip_tac >>
 gvs[lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem selected_MLOAD_output_replay:
 src.inst_opcode = MLOAD /\ inst.inst_opcode = MLOAD /\
 src.inst_outputs = [y] /\ inst.inst_outputs = [x] /\
 u.vs_memory = s.vs_memory /\
 MAP (\op. eval_operand op u) src.inst_operands =
 MAP (\op. eval_operand op s) inst.inst_operands ==>
 step_inst_base inst s = OK t ==>
 step_inst_base src u = OK v ==>
 lookup_var x t = lookup_var y v
Proof
 strip_tac >> cseReplayLib.selected_base_tac >> rpt strip_tac >>
 irule exec_read1_output_replay >>
 qexistsl [`\addr s. mload (w2n addr) s`, `\addr s. mload (w2n addr) s`] >>
 qexistsl [`inst`, `s`, `src`, `u`] >>
 simp[] >> simp[mload_def]
QED

(* The dynamic boundary deliberately knows no producer IDs or expressions. *)
Theorem cse_singleton_two_state_replay:
 inst_wf src /\ inst_wf inst /\
 src.inst_opcode = inst.inst_opcode /\
 ~is_pseudo inst.inst_opcode /\ inst.inst_opcode <> ASSIGN /\
 ~is_terminator inst.inst_opcode /\ ~avail_nonidempotent inst.inst_opcode /\
 ~is_alloca_op inst.inst_opcode /\
 src.inst_outputs = [y] /\ inst.inst_outputs = [x] /\
 step_inst m ctx src u = OK v /\ step_inst n ctx inst s = OK t /\
 (MAP (\op. eval_operand op u) src.inst_operands =
    MAP (\op. eval_operand op s) inst.inst_operands \/
  (is_commutative inst.inst_opcode /\ LENGTH src.inst_operands = 2 /\
   LENGTH inst.inst_operands = 2 /\
   MAP (\op. eval_operand op u) src.inst_operands =
    REVERSE (MAP (\op. eval_operand op s) inst.inst_operands))) /\
 u.vs_call_ctx = s.vs_call_ctx /\ u.vs_tx_ctx = s.vs_tx_ctx /\
 u.vs_block_ctx = s.vs_block_ctx /\ u.vs_data_section = s.vs_data_section /\
 u.vs_labels = s.vs_labels /\ u.vs_code = s.vs_code /\
 u.vs_prev_hashes = s.vs_prev_hashes /\
 u.vs_initial_fmp = s.vs_initial_fmp /\
 (Eff_MEMORY IN read_effects inst.inst_opcode ==> u.vs_memory = s.vs_memory) /\
 (Eff_STORAGE IN read_effects inst.inst_opcode ==>
    contract_storage u = contract_storage s) /\
 (Eff_BALANCE IN read_effects inst.inst_opcode ==>
    !addr. (lookup_account addr u.vs_accounts).balance =
           (lookup_account addr s.vs_accounts).balance) /\
 (Eff_EXTCODE IN read_effects inst.inst_opcode ==>
    !addr. (lookup_account addr u.vs_accounts).code =
           (lookup_account addr s.vs_accounts).code /\
           (account_empty (lookup_account addr u.vs_accounts) <=>
            account_empty (lookup_account addr s.vs_accounts))) /\
 (Eff_TRANSIENT IN read_effects inst.inst_opcode ==> u.vs_transient = s.vs_transient) /\
 (Eff_IMMUTABLES IN read_effects inst.inst_opcode ==> u.vs_immutables = s.vs_immutables) /\
 (Eff_RETURNDATA IN read_effects inst.inst_opcode ==> u.vs_returndata = s.vs_returndata) /\
 (Eff_FMP IN read_effects inst.inst_opcode ==> u.vs_fmp = s.vs_fmp) ==>
 lookup_var x t = lookup_var y v
Proof
 strip_tac >>
 `inst.inst_opcode <> INVOKE` by
   (Cases_on `inst.inst_opcode = INVOKE` >>
    gvs[avail_nonidempotent_def, is_nonidempotent_def]) >>
 `src.inst_opcode <> INVOKE` by metis_tac[] >>
 gvs[step_inst_non_invoke] >>
 Cases_on `inst.inst_opcode` >>
 gvs[is_pseudo_def, is_terminator_def, avail_nonidempotent_def,
     is_nonidempotent_def, is_commutative_def, is_alloca_op_def]
 >- suspend "ADD_direct"
 >- suspend "SUB_direct"
 >- suspend "MUL_direct"
 >- suspend "Div_direct"
 >- suspend "SDIV_direct"
 >- suspend "Mod_direct"
 >- suspend "SMOD_direct"
 >- suspend "Exp_direct"
 >- suspend "ADDMOD_direct"
 >- suspend "MULMOD_direct"
 >- suspend "EQ_direct"
 >- suspend "LT_direct"
 >- suspend "GT_direct"
 >- suspend "SLT_direct"
 >- suspend "SGT_direct"
 >- suspend "ISZERO_direct"
 >- suspend "AND_direct"
 >- suspend "OR_direct"
 >- suspend "XOR_direct"
 >- suspend "NOT_direct"
 >- suspend "SHL_direct"
 >- suspend "SHR_direct"
 >- suspend "SAR_direct"
 >- suspend "SIGNEXTEND_direct"
 >- suspend "BYTE_direct"
 >- suspend "MLOAD_direct"
 >- suspend "MSTORE_direct"
 >- suspend "MSTORE8_direct"
 >- suspend "MCOPY_direct"
 >- suspend "MEMTOP_direct"
 >- suspend "SLOAD_direct"
 >- suspend "SSTORE_direct"
 >- suspend "TLOAD_direct"
 >- suspend "TSTORE_direct"
 >- suspend "ILOAD_direct"
 >- suspend "ISTORE_direct"
 >- suspend "NOP_direct"
 >- suspend "GETFMP_direct"
 >- suspend "INITIAL_FMP_direct"
 >- suspend "CALLER_direct"
 >- suspend "CALLVALUE_direct"
 >- suspend "CALLDATALOAD_direct"
 >- suspend "CALLDATASIZE_direct"
 >- suspend "CALLDATACOPY_direct"
 >- suspend "ADDRESS_direct"
 >- suspend "ORIGIN_direct"
 >- suspend "GASPRICE_direct"
 >- suspend "GASLIMIT_direct"
 >- suspend "COINBASE_direct"
 >- suspend "TIMESTAMP_direct"
 >- suspend "NUMBER_direct"
 >- suspend "PREVRANDAO_direct"
 >- suspend "CHAINID_direct"
 >- suspend "SELFBALANCE_direct"
 >- suspend "BALANCE_direct"
 >- suspend "BLOCKHASH_direct"
 >- suspend "BASEFEE_direct"
 >- suspend "CODESIZE_direct"
 >- suspend "CODECOPY_direct"
 >- suspend "EXTCODESIZE_direct"
 >- suspend "EXTCODEHASH_direct"
 >- suspend "EXTCODECOPY_direct"
 >- suspend "RETURNDATASIZE_direct"
 >- suspend "RETURNDATACOPY_direct"
 >- suspend "BLOBHASH_direct"
 >- suspend "BLOBBASEFEE_direct"
 >- suspend "SHA3_direct"
 >- suspend "ASSERT_direct"
 >- suspend "ASSERT_UNREACHABLE_direct"
 >- suspend "DLOAD_direct"
 >- suspend "DLOADBYTES_direct"
 >- suspend "OFFSET_direct"
 >- suspend "ADD_reverse"
 >- suspend "MUL_reverse"
 >- suspend "EQ_reverse"
 >- suspend "AND_reverse"
 >- suspend "OR_reverse"
 >> suspend "XOR_reverse"
QED

Resume cse_singleton_two_state_replay[ADD_direct]:
 cseReplayLib.selected_base_tac >>
 irule exec_pure2_output_replay >> metis_tac[]
QED

Resume cse_singleton_two_state_replay[SUB_direct]:
 cseReplayLib.selected_base_tac >>
 irule exec_pure2_output_replay >> metis_tac[]
QED
Resume cse_singleton_two_state_replay[MUL_direct]:
 cseReplayLib.selected_base_tac >>
 irule exec_pure2_output_replay >> metis_tac[]
QED
Resume cse_singleton_two_state_replay[Div_direct]:
 cseReplayLib.selected_base_tac >>
 irule exec_pure2_output_replay >> metis_tac[]
QED
Resume cse_singleton_two_state_replay[SDIV_direct]:
 cseReplayLib.selected_base_tac >>
 irule exec_pure2_output_replay >> metis_tac[]
QED
Resume cse_singleton_two_state_replay[Mod_direct]:
 cseReplayLib.selected_base_tac >>
 irule exec_pure2_output_replay >> metis_tac[]
QED
Resume cse_singleton_two_state_replay[SMOD_direct]:
 cseReplayLib.selected_base_tac >>
 irule exec_pure2_output_replay >> metis_tac[]
QED
Resume cse_singleton_two_state_replay[Exp_direct]:
 cseReplayLib.selected_base_tac >>
 irule exec_pure2_output_replay >> metis_tac[]
QED
Resume cse_singleton_two_state_replay[ADDMOD_direct]:
 cseReplayLib.selected_base_tac >>
 irule exec_pure3_output_replay >> metis_tac[]
QED
Resume cse_singleton_two_state_replay[MULMOD_direct]:
 cseReplayLib.selected_base_tac >>
 irule exec_pure3_output_replay >> metis_tac[]
QED

Resume cse_singleton_two_state_replay[EQ_direct]:
 cseReplayLib.selected_base_tac >> irule exec_pure2_output_replay >> metis_tac[]
QED
Resume cse_singleton_two_state_replay[LT_direct]:
 cseReplayLib.selected_base_tac >> irule exec_pure2_output_replay >> metis_tac[]
QED
Resume cse_singleton_two_state_replay[GT_direct]:
 cseReplayLib.selected_base_tac >> irule exec_pure2_output_replay >> metis_tac[]
QED
Resume cse_singleton_two_state_replay[SLT_direct]:
 cseReplayLib.selected_base_tac >> irule exec_pure2_output_replay >> metis_tac[]
QED
Resume cse_singleton_two_state_replay[SGT_direct]:
 cseReplayLib.selected_base_tac >> irule exec_pure2_output_replay >> metis_tac[]
QED
Resume cse_singleton_two_state_replay[ISZERO_direct]:
 cseReplayLib.selected_base_tac >> irule exec_pure1_output_replay >> metis_tac[]
QED
Resume cse_singleton_two_state_replay[AND_direct]:
 cseReplayLib.selected_base_tac >> irule exec_pure2_output_replay >> metis_tac[]
QED
Resume cse_singleton_two_state_replay[OR_direct]:
 cseReplayLib.selected_base_tac >> irule exec_pure2_output_replay >> metis_tac[]
QED
Resume cse_singleton_two_state_replay[XOR_direct]:
 cseReplayLib.selected_base_tac >> irule exec_pure2_output_replay >> metis_tac[]
QED
Resume cse_singleton_two_state_replay[NOT_direct]:
 cseReplayLib.selected_base_tac >> irule exec_pure1_output_replay >> metis_tac[]
QED
Resume cse_singleton_two_state_replay[SHL_direct]:
 cseReplayLib.selected_base_tac >> irule exec_pure2_output_replay >> metis_tac[]
QED
Resume cse_singleton_two_state_replay[SHR_direct]:
 cseReplayLib.selected_base_tac >> irule exec_pure2_output_replay >> metis_tac[]
QED
Resume cse_singleton_two_state_replay[SAR_direct]:
 cseReplayLib.selected_base_tac >> irule exec_pure2_output_replay >> metis_tac[]
QED
Resume cse_singleton_two_state_replay[SIGNEXTEND_direct]:
 cseReplayLib.selected_base_tac >> irule exec_pure2_output_replay >> metis_tac[]
QED
Resume cse_singleton_two_state_replay[BYTE_direct]:
 cseReplayLib.selected_base_tac >> irule exec_pure2_output_replay >> metis_tac[]
QED

Resume cse_singleton_two_state_replay[MLOAD_direct]:
 gvs[read_effects_def] >> irule selected_MLOAD_output_replay >> metis_tac[]
QED
Resume cse_singleton_two_state_replay[MSTORE_direct]:
 gvs[inst_wf_def]
QED
Resume cse_singleton_two_state_replay[MSTORE8_direct]:
 gvs[inst_wf_def]
QED
Resume cse_singleton_two_state_replay[MCOPY_direct]:
 gvs[inst_wf_def]
QED
Resume cse_singleton_two_state_replay[MEMTOP_direct]:
 cseReplayLib.selected_base_tac >> gvs[read_effects_def] >>
 irule exec_read0_output_replay >>
 rpt (goal_assum $ drule_at (Pat `exec_read0 _ _ _ = _`)) >> simp[]
QED
Resume cse_singleton_two_state_replay[SLOAD_direct]:
 cseReplayLib.selected_base_tac >> gvs[read_effects_def] >>
 irule exec_read1_output_replay >>
 rpt (goal_assum $ drule_at (Pat `exec_read1 _ _ _ = _`)) >>
 simp[sload_def]
QED
Resume cse_singleton_two_state_replay[SSTORE_direct]:
 gvs[inst_wf_def]
QED
Resume cse_singleton_two_state_replay[TLOAD_direct]:
 cseReplayLib.selected_base_tac >> gvs[read_effects_def] >>
 irule exec_read1_output_replay >>
 rpt (goal_assum $ drule_at (Pat `exec_read1 _ _ _ = _`)) >>
 simp[tload_def, contract_transient_def]
QED
Resume cse_singleton_two_state_replay[TSTORE_direct]:
 gvs[inst_wf_def]
QED
Resume cse_singleton_two_state_replay[ILOAD_direct]:
 cseReplayLib.selected_base_tac >> gvs[read_effects_def] >>
 irule exec_read1_output_replay >>
 rpt (goal_assum $ drule_at (Pat `exec_read1 _ _ _ = _`)) >>
 simp[mload_def]
QED
Resume cse_singleton_two_state_replay[ISTORE_direct]:
 gvs[inst_wf_def]
QED

Resume cse_singleton_two_state_replay[NOP_direct]:
 gvs[inst_wf_def]
QED

Resume cse_singleton_two_state_replay[GETFMP_direct]:
 cseReplayLib.selected_base_tac >> gvs[read_effects_def, AllCaseEqs()] >>
 simp[lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Resume cse_singleton_two_state_replay[INITIAL_FMP_direct]:
 cseReplayLib.selected_base_tac >> gvs[read_effects_def, AllCaseEqs()] >>
 simp[lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Resume cse_singleton_two_state_replay[CALLER_direct]:
 cseReplayLib.selected_base_tac >> gvs[read_effects_def] >>
 irule exec_read0_output_replay >>
 rpt (goal_assum $ drule_at (Pat `exec_read0 _ _ _ = _`)) >> simp[]
QED

Resume cse_singleton_two_state_replay[CALLVALUE_direct]:
 cseReplayLib.selected_base_tac >> irule exec_read0_output_replay >>
 rpt (goal_assum $ drule_at (Pat `exec_read0 _ _ _ = _`)) >> simp[]
QED
Resume cse_singleton_two_state_replay[CALLDATALOAD_direct]:
 cseReplayLib.selected_base_tac >> irule exec_read1_output_replay >>
 rpt (goal_assum $ drule_at (Pat `exec_read1 _ _ _ = _`)) >> simp[]
QED
Resume cse_singleton_two_state_replay[CALLDATASIZE_direct]:
 cseReplayLib.selected_base_tac >> irule exec_read0_output_replay >>
 rpt (goal_assum $ drule_at (Pat `exec_read0 _ _ _ = _`)) >> simp[]
QED
Resume cse_singleton_two_state_replay[CALLDATACOPY_direct]:
 gvs[inst_wf_def]
QED
Resume cse_singleton_two_state_replay[ADDRESS_direct]:
 cseReplayLib.selected_base_tac >> irule exec_read0_output_replay >>
 rpt (goal_assum $ drule_at (Pat `exec_read0 _ _ _ = _`)) >> simp[]
QED
Resume cse_singleton_two_state_replay[ORIGIN_direct]:
 cseReplayLib.selected_base_tac >> irule exec_read0_output_replay >>
 rpt (goal_assum $ drule_at (Pat `exec_read0 _ _ _ = _`)) >> simp[]
QED
Resume cse_singleton_two_state_replay[GASPRICE_direct]:
 cseReplayLib.selected_base_tac >> irule exec_read0_output_replay >>
 rpt (goal_assum $ drule_at (Pat `exec_read0 _ _ _ = _`)) >> simp[]
QED

Resume cse_singleton_two_state_replay[GASLIMIT_direct]:
 cseReplayLib.selected_base_tac >> irule exec_read0_output_replay >>
 rpt (goal_assum $ drule_at (Pat `exec_read0 _ _ _ = _`)) >> simp[]
QED
Resume cse_singleton_two_state_replay[COINBASE_direct]:
 cseReplayLib.selected_base_tac >> irule exec_read0_output_replay >>
 rpt (goal_assum $ drule_at (Pat `exec_read0 _ _ _ = _`)) >> simp[]
QED
Resume cse_singleton_two_state_replay[TIMESTAMP_direct]:
 cseReplayLib.selected_base_tac >> irule exec_read0_output_replay >>
 rpt (goal_assum $ drule_at (Pat `exec_read0 _ _ _ = _`)) >> simp[]
QED
Resume cse_singleton_two_state_replay[NUMBER_direct]:
 cseReplayLib.selected_base_tac >> irule exec_read0_output_replay >>
 rpt (goal_assum $ drule_at (Pat `exec_read0 _ _ _ = _`)) >> simp[]
QED
Resume cse_singleton_two_state_replay[PREVRANDAO_direct]:
 cseReplayLib.selected_base_tac >> irule exec_read0_output_replay >>
 rpt (goal_assum $ drule_at (Pat `exec_read0 _ _ _ = _`)) >> simp[]
QED
Resume cse_singleton_two_state_replay[CHAINID_direct]:
 cseReplayLib.selected_base_tac >> irule exec_read0_output_replay >>
 rpt (goal_assum $ drule_at (Pat `exec_read0 _ _ _ = _`)) >> simp[]
QED
Resume cse_singleton_two_state_replay[SELFBALANCE_direct]:
 cseReplayLib.selected_base_tac >> gvs[read_effects_def] >>
 irule exec_read0_output_replay >>
 rpt (goal_assum $ drule_at (Pat `exec_read0 _ _ _ = _`)) >> simp[]
QED
Resume cse_singleton_two_state_replay[BALANCE_direct]:
 cseReplayLib.selected_base_tac >> gvs[read_effects_def] >>
 irule exec_read1_output_replay >>
 rpt (goal_assum $ drule_at (Pat `exec_read1 _ _ _ = _`)) >> simp[]
QED
Resume cse_singleton_two_state_replay[BLOCKHASH_direct]:
 cseReplayLib.selected_base_tac >> irule exec_read1_output_replay >>
 rpt (goal_assum $ drule_at (Pat `exec_read1 _ _ _ = _`)) >> simp[]
QED
Resume cse_singleton_two_state_replay[BASEFEE_direct]:
 cseReplayLib.selected_base_tac >> irule exec_read0_output_replay >>
 rpt (goal_assum $ drule_at (Pat `exec_read0 _ _ _ = _`)) >> simp[]
QED

Resume cse_singleton_two_state_replay[CODESIZE_direct]:
 cseReplayLib.selected_base_tac >> irule exec_read0_output_replay >>
 rpt (goal_assum $ drule_at (Pat `exec_read0 _ _ _ = _`)) >> simp[]
QED
Resume cse_singleton_two_state_replay[CODECOPY_direct]:
 gvs[inst_wf_def]
QED
Resume cse_singleton_two_state_replay[EXTCODESIZE_direct]:
 cseReplayLib.selected_base_tac >> gvs[read_effects_def] >>
 irule exec_read1_output_replay >>
 rpt (goal_assum $ drule_at (Pat `exec_read1 _ _ _ = _`)) >> simp[]
QED
Resume cse_singleton_two_state_replay[EXTCODEHASH_direct]:
 cseReplayLib.selected_base_tac >> gvs[read_effects_def] >>
 irule exec_read1_output_replay >>
 rpt (goal_assum $ drule_at (Pat `exec_read1 _ _ _ = _`)) >> simp[]
QED
Resume cse_singleton_two_state_replay[EXTCODECOPY_direct]:
 gvs[inst_wf_def]
QED
Resume cse_singleton_two_state_replay[RETURNDATASIZE_direct]:
 cseReplayLib.selected_base_tac >> gvs[read_effects_def] >>
 irule exec_read0_output_replay >>
 rpt (goal_assum $ drule_at (Pat `exec_read0 _ _ _ = _`)) >> simp[]
QED
Resume cse_singleton_two_state_replay[RETURNDATACOPY_direct]:
 gvs[inst_wf_def]
QED
Resume cse_singleton_two_state_replay[BLOBHASH_direct]:
 cseReplayLib.selected_base_tac >> irule exec_read1_output_replay >>
 rpt (goal_assum $ drule_at (Pat `exec_read1 _ _ _ = _`)) >> simp[]
QED
Resume cse_singleton_two_state_replay[BLOBBASEFEE_direct]:
 cseReplayLib.selected_base_tac >> irule exec_read0_output_replay >>
 rpt (goal_assum $ drule_at (Pat `exec_read0 _ _ _ = _`)) >> simp[]
QED

Resume cse_singleton_two_state_replay[SHA3_direct]:
 cseReplayLib.selected_base_tac >> gvs[read_effects_def, AllCaseEqs()] >>
 gvs[lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Resume cse_singleton_two_state_replay[ASSERT_direct]:
 gvs[inst_wf_def]
QED
Resume cse_singleton_two_state_replay[ASSERT_UNREACHABLE_direct]:
 gvs[inst_wf_def]
QED
Resume cse_singleton_two_state_replay[DLOAD_direct]:
 cseReplayLib.selected_base_tac >> irule exec_read1_output_replay >>
 rpt (goal_assum $ drule_at (Pat `exec_read1 _ _ _ = _`)) >> simp[]
QED
Resume cse_singleton_two_state_replay[DLOADBYTES_direct]:
 gvs[inst_wf_def]
QED
Resume cse_singleton_two_state_replay[OFFSET_direct]:
 cseReplayLib.selected_base_tac >> irule exec_pure2_output_replay >> metis_tac[]
QED

Resume cse_singleton_two_state_replay[ADD_reverse]:
 cseReplayLib.selected_base_tac >> irule exec_pure2_output_replay >>
 rpt (goal_assum $ drule_at (Pat `exec_pure2 _ _ _ = _`)) >>
 simp[wordsTheory.WORD_ADD_COMM]
QED

Resume cse_singleton_two_state_replay[MUL_reverse]:
 cseReplayLib.selected_base_tac >> irule exec_pure2_output_replay >>
 rpt (goal_assum $ drule_at (Pat `exec_pure2 _ _ _ = _`)) >>
 simp[wordsTheory.WORD_MULT_COMM]
QED
Resume cse_singleton_two_state_replay[EQ_reverse]:
 cseReplayLib.selected_base_tac >> irule exec_pure2_output_replay >>
 rpt (goal_assum $ drule_at (Pat `exec_pure2 _ _ _ = _`)) >>
 simp[EQ_SYM_EQ]
QED
Resume cse_singleton_two_state_replay[AND_reverse]:
 cseReplayLib.selected_base_tac >> irule exec_pure2_output_replay >>
 rpt (goal_assum $ drule_at (Pat `exec_pure2 _ _ _ = _`)) >>
 simp[wordsTheory.WORD_AND_COMM]
QED
Resume cse_singleton_two_state_replay[OR_reverse]:
 cseReplayLib.selected_base_tac >> irule exec_pure2_output_replay >>
 rpt (goal_assum $ drule_at (Pat `exec_pure2 _ _ _ = _`)) >>
 simp[wordsTheory.WORD_OR_COMM]
QED
Resume cse_singleton_two_state_replay[XOR_reverse]:
 cseReplayLib.selected_base_tac >> irule exec_pure2_output_replay >>
 rpt (goal_assum $ drule_at (Pat `exec_pure2 _ _ _ = _`)) >>
 simp[wordsTheory.WORD_XOR_COMM]
QED

Finalise cse_singleton_two_state_replay


Theorem cse_singleton_history_replay:
 wf_function fn /\ fn_inst_wf fn /\
 EVERY (\i. ~is_alloca_op i.inst_opcode) (fn_insts fn) /\
 cse_prefix ctx fn fuel0 s0 pre (CseExec m sb u) /\
 cse_prefix ctx fn fuel0 s0 (pre ++ [CseStep m sb src u v] ++ post)
   (CseExec n ib s) /\
 get_instruction sb u.vs_inst_idx = SOME src /\
 get_instruction ib s.vs_inst_idx = SOME inst /\
 inst_wf src /\ inst_wf inst /\ src.inst_opcode = inst.inst_opcode /\
 ~is_pseudo inst.inst_opcode /\ inst.inst_opcode <> ASSIGN /\
 ~is_terminator inst.inst_opcode /\ ~avail_nonidempotent inst.inst_opcode /\
 ~has_conflicting_effects inst.inst_opcode /\
 src.inst_outputs = [y] /\ inst.inst_outputs = [x] /\
 step_inst m ctx src u = OK v /\ step_inst n ctx inst s = OK t /\
 (MAP (\op. eval_operand op u) src.inst_operands =
    MAP (\op. eval_operand op s) inst.inst_operands \/
  (is_commutative inst.inst_opcode /\ LENGTH src.inst_operands = 2 /\
   LENGTH inst.inst_operands = 2 /\
   MAP (\op. eval_operand op u) src.inst_operands =
    REVERSE (MAP (\op. eval_operand op s) inst.inst_operands))) /\
 EVERY (cse_event_survives (mk_expr (dfg_build_function fn) inst)) post ==>
 lookup_var x t = lookup_var y v
Proof
 strip_tac >>
 `~is_alloca_op src.inst_opcode` by
   (irule cse_prefix_step_allocation_free >>
    goal_assum (drule_at Any) >> simp[] >>
    qexistsl [`sb`, `m`, `u`, `v`] >> simp[]) >>
 `cse_prefix ctx fn fuel0 s0 (pre ++ [CseStep m sb src u v])
    (CseExec m sb (v with vs_inst_idx := SUC u.vs_inst_idx))` by
   (irule cseHistoryPropsTheory.cse_prefix_ordinary_extend >> simp[]) >>
 qpat_assum `step_inst m ctx src u = OK v`
   (mp_then Any mp_tac cse_step_read_observations) >>
 simp[] >> strip_tac >>
 `root_effects (mk_expr (dfg_build_function fn) inst) =
    read_effects inst.inst_opcode UNION write_effects inst.inst_opcode` by
   (simp[mk_expr_def, Once mk_operand_expr_def, canon_expr_def,
         root_effects_def] >> IF_CASES_TAC >> simp[root_effects_def]) >>
 qpat_assum `cse_prefix _ _ _ _ (pre ++ [CseStep m sb src u v]) _`
   (mp_then Any mp_tac cse_prefix_interval_observations) >>
 simp[cseHistoryPropsTheory.cse_phase_state_def, listTheory.APPEND_ASSOC] >>
 disch_then (qspecl_then [`post`, `CseExec n ib s`,
   `mk_expr (dfg_build_function fn) inst`] mp_tac) >>
 simp[cseHistoryPropsTheory.cse_phase_state_def,
      venomStateTheory.contract_storage_def] >> strip_tac >>
 irule cse_singleton_two_state_replay >>
 qexistsl [`ctx`, `inst`, `m`, `n`, `s`, `src`, `u`] >>
 gvs[cse_fixed_observation_def, cse_effect_observation_def] >>
 rpt conj_tac >> rpt strip_tac >> gvs[] >>
 metis_tac[venomStateTheory.contract_storage_def]
QED
