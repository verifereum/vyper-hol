Theory makeSsaCurrentForwardBase
Ancestors
  makeSsaCurrentForwardRuntime makeSsaCurrentExecRuntime makeSsaCurrentRuntime o1FrameLockstep
  venomExecSemantics venomExecProofs opcodeClass venomState stateFrame venomWf list
Libs
  stepInstBaseLib

Theorem current_exec_pure_opcodes_pair_forward:
  MEM inst.inst_opcode
    [ADD; SUB; MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD;
     EQ; LT; GT; SLT; SGT; ISZERO; AND; OR; XOR; NOT; SHL; SHR; SAR;
     SIGNEXTEND; BYTE; OFFSET] /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  step_inst_base inst st = OK t ==>
  ?t'. step_inst_base inst' st' = OK t' /\ state_rel sg1 t t'
Proof
  strip_tac >> `inst'.inst_opcode = inst.inst_opcode` by fs[inst_pair_def] >>
  fs[MEM] >>
  qpat_x_assum `inst'.inst_opcode = inst.inst_opcode` mp_tac >> simp[] >>
  strip_tac >> stepInstBaseLib.with_opcode_clause gvs >>
  metis_tac[current_exec_pure1_pair_forward, current_exec_pure2_pair_forward,
            current_exec_pure3_pair_forward]
QED

Theorem current_exec_read0_opcodes_pair_forward:
  MEM inst.inst_opcode
    [CALLER; ADDRESS; CALLVALUE; ORIGIN; GASPRICE; CHAINID; COINBASE;
     TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE; BLOBBASEFEE;
     SELFBALANCE; CALLDATASIZE; RETURNDATASIZE; MEMTOP; CODESIZE] /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  step_inst_base inst st = OK t ==>
  ?t'. step_inst_base inst' st' = OK t' /\ state_rel sg1 t t'
Proof
  strip_tac >> `inst'.inst_opcode = inst.inst_opcode` by fs[inst_pair_def] >>
  fs[MEM] >>
  qpat_x_assum `inst'.inst_opcode = inst.inst_opcode` mp_tac >> simp[] >>
  strip_tac >> stepInstBaseLib.with_opcode_clause gvs >>
  ho_match_mp_tac current_exec_read0_pair_forward >> asm_rewrite_tac[] >>
  rpt strip_tac >> fs[execution_frame_def]
QED

Theorem current_exec_read1_opcodes_pair_forward:
  MEM inst.inst_opcode
    [MLOAD; SLOAD; TLOAD; BLOCKHASH; BLOBHASH; BALANCE; CALLDATALOAD;
     EXTCODESIZE; EXTCODEHASH; ILOAD; DLOAD] /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  step_inst_base inst st = OK t ==>
  ?t'. step_inst_base inst' st' = OK t' /\ state_rel sg1 t t'
Proof
  strip_tac >> `inst'.inst_opcode = inst.inst_opcode` by fs[inst_pair_def] >>
  fs[MEM] >>
  qpat_x_assum `inst'.inst_opcode = inst.inst_opcode` mp_tac >> simp[] >>
  strip_tac >> stepInstBaseLib.with_opcode_clause gvs >>
  ho_match_mp_tac current_exec_read1_pair_forward >> asm_rewrite_tac[] >>
  rpt strip_tac >>
  fs[execution_frame_def, mload_def, sload_def, tload_def,
     contract_storage_def, contract_transient_def]
QED

Theorem current_exec_write2_opcodes_pair_forward:
  MEM inst.inst_opcode [MSTORE; MSTORE8; SSTORE; TSTORE] /\
  inst.inst_outputs = [] /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  step_inst_base inst st = OK t ==>
  ?t'. step_inst_base inst' st' = OK t' /\ state_rel sg1 t t'
Proof
  strip_tac >>
  `inst'.inst_opcode = inst.inst_opcode` by fs[inst_pair_def] >>
  `st'.vs_call_ctx = st.vs_call_ctx` by fs[state_rel_def, execution_frame_def] >>
  `eval_operands inst'.inst_operands st' = eval_operands inst.inst_operands st` by
    (drule_all inst_pair_ops >> simp[ops_pair_def] >>
     metis_tac[eval_operands_rel]) >>
  fs[MEM] >>
  qpat_x_assum `inst'.inst_opcode = inst.inst_opcode` mp_tac >> simp[] >>
  strip_tac >> stepInstBaseLib.with_opcode_clause gvs >>
  gvs[AllCaseEqs()] >>
  ho_match_mp_tac current_exec_write2_pair_forward >> asm_rewrite_tac[] >>
  rpt strip_tac >> metis_tac[current_exec_store_state_rel]
QED

Theorem current_exec_copy3_opcodes_pair_forward:
  MEM inst.inst_opcode [MCOPY; CALLDATACOPY; RETURNDATACOPY; DLOADBYTES; CODECOPY] /\
  inst.inst_outputs = [] /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  step_inst_base inst st = OK t ==>
  ?t'. step_inst_base inst' st' = OK t' /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >> simp[ops_pair_def] >> strip_tac >>
  `inst'.inst_opcode = inst.inst_opcode` by fs[inst_pair_def] >>
  `st'.vs_call_ctx = st.vs_call_ctx /\ st'.vs_returndata = st.vs_returndata /\
   st'.vs_data_section = st.vs_data_section /\ st'.vs_code = st.vs_code` by
    fs[state_rel_def, execution_frame_def] >>
  `inst'.inst_outputs = []` by gvs[current_last_output_slots_def] >>
  fs[MEM] >>
  qpat_x_assum `inst'.inst_opcode = inst.inst_opcode` mp_tac >> simp[] >>
  strip_tac >> stepInstBaseLib.with_opcode_clause gvs >>
  gvs[AllCaseEqs()] >>
  metis_tac[current_exec_empty_last_slots, current_exec_memory_state_rel]
QED

Theorem current_exec_istore_extcodecopy_pair_forward:
  MEM inst.inst_opcode [ISTORE; EXTCODECOPY] /\ inst.inst_outputs = [] /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  step_inst_base inst st = OK t ==>
  ?t'. step_inst_base inst' st' = OK t' /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >> simp[ops_pair_def] >> strip_tac >>
  `inst'.inst_opcode = inst.inst_opcode` by fs[inst_pair_def] >>
  `st'.vs_accounts = st.vs_accounts` by fs[state_rel_def, execution_frame_def] >>
  `inst'.inst_outputs = []` by gvs[current_last_output_slots_def] >>
  fs[MEM] >>
  qpat_x_assum `inst'.inst_opcode = inst.inst_opcode` mp_tac >> simp[] >>
  strip_tac >> stepInstBaseLib.with_opcode_clause gvs >>
  gvs[AllCaseEqs()] >>
  metis_tac[current_exec_empty_last_slots, current_exec_memory_state_rel]
QED

Theorem current_exec_assign_sha3_pair_forward:
  MEM inst.inst_opcode [ASSIGN; SHA3] /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  step_inst_base inst st = OK t ==>
  ?t'. step_inst_base inst' st' = OK t' /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >> simp[ops_pair_def] >> strip_tac >>
  `inst'.inst_opcode = inst.inst_opcode` by fs[inst_pair_def] >>
  `st'.vs_memory = st.vs_memory` by fs[state_rel_def, execution_frame_def] >>
  fs[MEM] >>
  qpat_x_assum `inst'.inst_opcode = inst.inst_opcode` mp_tac >> simp[] >>
  strip_tac >> stepInstBaseLib.with_opcode_clause gvs >>
  gvs[AllCaseEqs()] >>
  `LENGTH inst'.inst_outputs = 1` by fs[current_last_output_slots_def] >>
  Cases_on `inst'.inst_outputs` >> gvs[] >>
  metis_tac[current_exec_update_last_slots]
QED

Theorem current_exec_fmp_read_pair_forward:
  MEM inst.inst_opcode [GETFMP; INITIAL_FMP; PARAM; FMP_PARAM; RETPC_PARAM] /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  step_inst_base inst st = OK t ==>
  ?t'. step_inst_base inst' st' = OK t' /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >> simp[ops_pair_def] >> strip_tac >>
  `inst'.inst_opcode = inst.inst_opcode` by fs[inst_pair_def] >>
  `st'.vs_fmp = st.vs_fmp /\ st'.vs_initial_fmp = st.vs_initial_fmp /\
   st'.vs_params = st.vs_params /\ st'.vs_return_pc_token = st.vs_return_pc_token` by
    fs[state_rel_def, execution_frame_def] >>
  fs[MEM] >>
  qpat_x_assum `inst'.inst_opcode = inst.inst_opcode` mp_tac >> simp[] >>
  strip_tac >> stepInstBaseLib.with_opcode_clause gvs >>
  gvs[AllCaseEqs(), op_rename_lit] >>
  `LENGTH inst'.inst_outputs = 1` by fs[current_last_output_slots_def] >>
  Cases_on `inst'.inst_outputs` >> gvs[] >>
  gvs[op_rename_lit_src] >>
  irule current_exec_update_last_slots >> qexists_tac `sg` >> simp[]
QED

Theorem current_exec_setfmp_pair_forward:
  inst.inst_opcode = SETFMP /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  step_inst_base inst st = OK t ==>
  ?t'. step_inst_base inst' st' = OK t' /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >> simp[ops_pair_def] >> strip_tac >>
  `inst'.inst_opcode = SETFMP` by fs[inst_pair_def] >>
  stepInstBaseLib.with_opcode_clause gvs >> gvs[AllCaseEqs()] >>
  `inst'.inst_outputs = []` by gvs[current_last_output_slots_def] >>
  gvs[] >> metis_tac[current_exec_empty_last_slots, current_exec_fmp_state_rel]
QED

Theorem current_exec_dalloca_pair_forward:
  inst.inst_opcode = DALLOCA /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  step_inst_base inst st = OK t ==>
  ?t'. step_inst_base inst' st' = OK t' /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >> simp[ops_pair_def] >> strip_tac >>
  `inst'.inst_opcode = DALLOCA` by fs[inst_pair_def] >>
  `st'.vs_fmp = st.vs_fmp` by fs[state_rel_def, execution_frame_def] >>
  stepInstBaseLib.with_opcode_clause gvs >> gvs[AllCaseEqs()] >>
  `LENGTH inst'.inst_outputs = 1` by fs[current_last_output_slots_def] >>
  Cases_on `inst'.inst_outputs` >> gvs[] >>
  metis_tac[current_exec_update_last_slots, current_exec_fmp_state_rel]
QED

Theorem current_exec_nop_pair_forward:
  inst.inst_opcode = NOP /\ inst.inst_outputs = [] /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  step_inst_base inst st = OK t ==>
  ?t'. step_inst_base inst' st' = OK t' /\ state_rel sg1 t t'
Proof
  strip_tac >> `inst'.inst_opcode = NOP` by fs[inst_pair_def] >>
  stepInstBaseLib.with_opcode_clause gvs >> gvs[] >>
  `inst'.inst_outputs = []` by gvs[current_last_output_slots_def] >>
  metis_tac[current_exec_empty_last_slots]
QED

Theorem current_exec_alloca_pair_forward:
  inst.inst_opcode = ALLOCA /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  step_inst_base inst st = OK t ==>
  ?t'. step_inst_base inst' st' = OK t' /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >> simp[ops_pair_def] >> strip_tac >>
  `inst'.inst_opcode = ALLOCA /\ inst'.inst_id = inst.inst_id` by fs[inst_pair_def] >>
  `st'.vs_allocas = st.vs_allocas /\ st'.vs_alloca_next = st.vs_alloca_next` by
    fs[state_rel_def, execution_frame_def] >>
  stepInstBaseLib.with_opcode_clause gvs >>
  gvs[exec_alloca_def, AllCaseEqs(), op_rename_lit_src] >>
  `LENGTH inst'.inst_outputs = 1` by fs[current_last_output_slots_def] >>
  Cases_on `inst'.inst_outputs` >> gvs[op_rename_lit_src] >>
  irule current_exec_update_last_slots >> qexists_tac `sg` >> simp[] >>
  fs[state_rel_def, execution_frame_def, vars_rel_def, lookup_var_def]
QED

Theorem current_op_rename_label_src:
  op_rename sg (Label l) op' <=> op' = Label l
Proof
  Cases_on `op'` >> simp[op_rename_def]
QED

Theorem current_exec_jumps_pair_forward:
  MEM inst.inst_opcode [JMP; JNZ; DJMP] /\ inst.inst_outputs = [] /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  step_inst_base inst st = OK t ==>
  ?t'. step_inst_base inst' st' = OK t' /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >> simp[ops_pair_def] >> strip_tac >>
  `inst'.inst_opcode = inst.inst_opcode` by fs[inst_pair_def] >>
  `inst'.inst_outputs = []` by gvs[current_last_output_slots_def] >>
  fs[MEM] >>
  qpat_x_assum `inst'.inst_opcode = inst.inst_opcode` mp_tac >> simp[] >>
  strip_tac >> stepInstBaseLib.with_opcode_clause gvs >>
  gvs[AllCaseEqs(), current_op_rename_label_src] >>
  metis_tac[current_exec_empty_last_slots, current_exec_jump_state_rel,
            current_exec_extract_labels_pair, ops_pair_rename, ops_pair_def]
QED

Theorem current_exec_assertions_pair_forward:
  MEM inst.inst_opcode [ASSERT; ASSERT_UNREACHABLE] /\ inst.inst_outputs = [] /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  step_inst_base inst st = OK t ==>
  ?t'. step_inst_base inst' st' = OK t' /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >> simp[ops_pair_def] >> strip_tac >>
  `inst'.inst_opcode = inst.inst_opcode` by fs[inst_pair_def] >>
  `inst'.inst_outputs = []` by gvs[current_last_output_slots_def] >>
  fs[MEM] >>
  qpat_x_assum `inst'.inst_opcode = inst.inst_opcode` mp_tac >> simp[] >>
  strip_tac >> stepInstBaseLib.with_opcode_clause gvs >> gvs[AllCaseEqs()] >>
  metis_tac[current_exec_empty_last_slots]
QED

Theorem current_exec_bump_pair_forward:
  inst.inst_opcode = BUMP /\ inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  step_inst_base inst st = OK t ==>
  ?t'. step_inst_base inst' st' = OK t' /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >> simp[ops_pair_def] >> strip_tac >>
  `inst'.inst_opcode = BUMP` by fs[inst_pair_def] >>
  stepInstBaseLib.with_opcode_clause gvs >> gvs[AllCaseEqs()] >>
  `LENGTH inst'.inst_outputs = 2` by fs[current_last_output_slots_def] >>
  Cases_on `inst'.inst_outputs` >> gvs[] >>
  rename1 `inst'.inst_outputs = out1'::rest` >> Cases_on `rest` >> gvs[] >>
  rename1 `inst'.inst_outputs = [out1';out2']` >>
  rename1 `update_var out2 (bv + szv) (update_var out1 bv st)` >>
  `bind_outputs [out1;out2] [bv;word_add bv szv] st =
    SOME (update_var out2 (word_add bv szv) (update_var out1 bv st))` by
    simp[bind_outputs_def] >>
  drule_all current_runtime_bind_last_slots_forward >>
  simp[bind_outputs_def] >> metis_tac[]
QED

Theorem current_exec_ext_call_pair_forward:
  state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  exec_ext_call inst st gas addr value ao sz ro rs static = OK t ==>
  ?t'. exec_ext_call inst' st' gas addr value ao sz ro rs static = OK t' /\
       state_rel sg1 t t'
Proof
  strip_tac >>
  `venom_call_request st addr value ao sz static =
   venom_call_request st' addr value ao sz static` by
    metis_tac[current_exec_oracle_requests_pair] >>
  qmatch_asmsub_abbrev_tac `venom_call_request st addr value ao sz static = rq` >>
  `FST (consume_call_outcome rq (w2n ro) (w2n rs) st) = FST (consume_call_outcome rq (w2n ro) (w2n rs) st') /\
   state_rel sg (SND (consume_call_outcome rq (w2n ro) (w2n rs) st))
                (SND (consume_call_outcome rq (w2n ro) (w2n rs) st'))` by
    metis_tac[current_exec_consume_call_pair] >>
  gvs[exec_ext_call_def, AllCaseEqs()] >>
  `LENGTH inst'.inst_outputs = 1` by fs[current_last_output_slots_def] >>
  Cases_on `inst'.inst_outputs` >> gvs[] >>
  (* FIRST_PROVE gives each goal its own timed step. *)
  FIRST_PROVE [metis_tac[current_exec_update_last_slots]]
QED

Theorem current_exec_create_pair_forward:
  state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  exec_create inst st value off sz salt = OK t ==>
  ?t'. exec_create inst' st' value off sz salt = OK t' /\ state_rel sg1 t t'
Proof
  strip_tac >>
  `venom_create_request st value off sz salt =
   venom_create_request st' value off sz salt` by
    metis_tac[current_exec_oracle_requests_pair] >>
  qmatch_asmsub_abbrev_tac `venom_create_request st value off sz salt = rq` >>
  `FST (consume_create_outcome rq st) = FST (consume_create_outcome rq st') /\
   state_rel sg (SND (consume_create_outcome rq st))
                (SND (consume_create_outcome rq st'))` by
    metis_tac[current_exec_consume_create_pair] >>
  gvs[exec_create_def, AllCaseEqs()] >>
  `LENGTH inst'.inst_outputs = 1` by fs[current_last_output_slots_def] >>
  Cases_on `inst'.inst_outputs` >> gvs[] >>
  metis_tac[current_exec_update_last_slots]
QED

Theorem current_exec_call_opcodes_pair_forward:
  MEM inst.inst_opcode [CALL; STATICCALL] /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  step_inst_base inst st = OK t ==>
  ?t'. step_inst_base inst' st' = OK t' /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >> simp[ops_pair_def] >> strip_tac >>
  `inst'.inst_opcode = inst.inst_opcode` by fs[inst_pair_def] >>
  `st'.vs_call_ctx = st.vs_call_ctx` by fs[state_rel_def, execution_frame_def] >>
  fs[MEM] >>
  qpat_x_assum `inst'.inst_opcode = inst.inst_opcode` mp_tac >> simp[] >>
  strip_tac >> stepInstBaseLib.with_opcode_clause gvs >> gvs[AllCaseEqs()] >>
  metis_tac[current_exec_ext_call_pair_forward]
QED

Theorem current_exec_create_opcodes_pair_forward:
  MEM inst.inst_opcode [CREATE; CREATE2] /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  step_inst_base inst st = OK t ==>
  ?t'. step_inst_base inst' st' = OK t' /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >> simp[ops_pair_def] >> strip_tac >>
  `inst'.inst_opcode = inst.inst_opcode` by fs[inst_pair_def] >>
  `st'.vs_call_ctx = st.vs_call_ctx` by fs[state_rel_def, execution_frame_def] >>
  `eval_operands inst'.inst_operands st' = eval_operands inst.inst_operands st` by
    metis_tac[eval_operands_rel] >>
  fs[MEM] >>
  qpat_x_assum `inst'.inst_opcode = inst.inst_opcode` mp_tac >> simp[] >>
  strip_tac >> stepInstBaseLib.with_opcode_clause gvs >> gvs[AllCaseEqs()] >>
  metis_tac[current_exec_create_pair_forward]
QED

Theorem current_exec_extract_result_pair_forward:
  state_rel sg a b /\
  extract_venom_result a output ro rs result = SOME (v,t) ==>
  ?t'. extract_venom_result b output ro rs result = SOME (v,t') /\ state_rel sg t t'
Proof
  strip_tac >> gvs[extract_venom_result_def, AllCaseEqs()] >>
  fs[state_rel_def, execution_frame_def] >>
  pairarg_tac >> gvs[] >>
  simp[state_rel_def, execution_frame_def, vars_rel_def, lookup_var_def,
       write_memory_with_expansion_def] >>
  fs[vars_rel_def, lookup_var_def]
QED

Theorem current_exec_delegatecall_pair_forward:
  state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  exec_delegatecall inst st gas addr ao sz ro rs = OK t ==>
  ?t'. exec_delegatecall inst' st' gas addr ao sz ro rs = OK t' /\ state_rel sg1 t t'
Proof
  strip_tac >>
  `venom_call_request st addr 0w ao sz F =
   venom_call_request st' addr 0w ao sz F` by
    metis_tac[current_exec_oracle_requests_pair] >>
  qmatch_asmsub_abbrev_tac `venom_call_request st addr 0w ao sz F = rq` >>
  `FST (consume_call_outcome (rq with cr_kind := DelegateMessageCall) (w2n ro) (w2n rs) st) =
   FST (consume_call_outcome (rq with cr_kind := DelegateMessageCall) (w2n ro) (w2n rs) st') /\
   state_rel sg (SND (consume_call_outcome (rq with cr_kind := DelegateMessageCall) (w2n ro) (w2n rs) st))
                (SND (consume_call_outcome (rq with cr_kind := DelegateMessageCall) (w2n ro) (w2n rs) st'))` by
    metis_tac[current_exec_consume_call_pair] >>
  gvs[exec_delegatecall_def, AllCaseEqs()] >>
  `LENGTH inst'.inst_outputs = 1` by fs[current_last_output_slots_def] >>
  Cases_on `inst'.inst_outputs` >> gvs[] >>
  (* The oracle terms are too big for metis: name the instance directly. *)
  irule current_exec_update_last_slots >> qexists_tac `sg` >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem current_exec_delegatecall_opcode_pair_forward:
  inst.inst_opcode = DELEGATECALL /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  step_inst_base inst st = OK t ==>
  ?t'. step_inst_base inst' st' = OK t' /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >> simp[ops_pair_def] >> strip_tac >>
  `inst'.inst_opcode = DELEGATECALL` by fs[inst_pair_def] >>
  stepInstBaseLib.with_opcode_clause gvs >> gvs[AllCaseEqs()] >>
  metis_tac[current_exec_delegatecall_pair_forward]
QED

Theorem current_exec_log_pair_forward:
  inst.inst_opcode = LOG /\ inst.inst_outputs = [] /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  step_inst_base inst st = OK t ==>
  ?t'. step_inst_base inst' st' = OK t' /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >> simp[ops_pair_def] >> strip_tac >>
  `inst'.inst_opcode = LOG` by fs[inst_pair_def] >>
  `st'.vs_call_ctx = st.vs_call_ctx /\ st'.vs_memory = st.vs_memory /\
   st'.vs_logs = st.vs_logs` by fs[state_rel_def, execution_frame_def] >>
  `eval_operands inst'.inst_operands st' = eval_operands inst.inst_operands st` by
    metis_tac[eval_operands_rel] >>
  `inst'.inst_outputs = []` by gvs[current_last_output_slots_def] >>
  stepInstBaseLib.with_opcode_clause gvs >> gvs[AllCaseEqs(), op_rename_lit_src] >>
  rename1 `LIST_REL (\op op'. op_rename sg op op' /\
    eval_operand op' st' = eval_operand op st) source_ops target_ops` >>
  `LENGTH source_ops = LENGTH target_ops` by metis_tac[LIST_REL_LENGTH] >>
  `LIST_REL (\op op'. op_rename sg op op' /\
       eval_operand op' st' = eval_operand op st)
       (REVERSE source_ops) (REVERSE target_ops)` by
    metis_tac[LIST_REL_REVERSE] >>
  `eval_operand (EL 0 (REVERSE target_ops)) st' =
   eval_operand (EL 0 (REVERSE source_ops)) st /\
   eval_operand (EL 1 (REVERSE target_ops)) st' =
   eval_operand (EL 1 (REVERSE source_ops)) st` by
    (gvs[LIST_REL_EL_EQN, EL_REVERSE] >> metis_tac[]) >>
  `eval_operands (DROP 2 (REVERSE target_ops)) st' =
   eval_operands (DROP 2 (REVERSE source_ops)) st` by
    (irule eval_operands_rel >> qexists_tac `sg` >>
     irule rich_listTheory.LIST_REL_DROP >> first_assum MATCH_ACCEPT_TAC) >>
  gvs[] >>
  rpt (qpat_x_assum `SOME _ = eval_operand _ _` (assume_tac o SYM)) >> simp[] >>
  irule current_exec_empty_last_slots >> qexists_tac `sg` >> simp[] >>
  fs[state_rel_def, execution_frame_def, vars_rel_def, lookup_var_def]
QED

Theorem current_exec_noninvoke_ok_pair_forward:
  inst_wf inst /\ inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> PHI /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  step_inst_base inst st = OK t ==>
  ?t'. step_inst_base inst' st' = OK t' /\ state_rel sg1 t t'
Proof
  strip_tac >>
  Cases_on `MEM inst.inst_opcode
    [ADD; SUB; MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD;
     EQ; LT; GT; SLT; SGT; ISZERO; AND; OR; XOR; NOT; SHL; SHR; SAR;
     SIGNEXTEND; BYTE; OFFSET]`
  >- metis_tac[current_exec_pure_opcodes_pair_forward] >>
  Cases_on `MEM inst.inst_opcode
    [CALLER; ADDRESS; CALLVALUE; ORIGIN; GASPRICE; CHAINID; COINBASE;
     TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE; BLOBBASEFEE;
     SELFBALANCE; CALLDATASIZE; RETURNDATASIZE; MEMTOP; CODESIZE]`
  >- metis_tac[current_exec_read0_opcodes_pair_forward] >>
  Cases_on `MEM inst.inst_opcode
    [MLOAD; SLOAD; TLOAD; BLOCKHASH; BLOBHASH; BALANCE; CALLDATALOAD;
     EXTCODESIZE; EXTCODEHASH; ILOAD; DLOAD]`
  >- metis_tac[current_exec_read1_opcodes_pair_forward] >>
  Cases_on `MEM inst.inst_opcode [MSTORE; MSTORE8; SSTORE; TSTORE]`
  >- (`inst.inst_outputs = []` by (fs[MEM] >> fs[inst_wf_def]) >>
      drule_all current_exec_write2_opcodes_pair_forward >> simp[]) >>
  Cases_on `MEM inst.inst_opcode [MCOPY; CALLDATACOPY; RETURNDATACOPY; DLOADBYTES; CODECOPY]`
  >- (`inst.inst_outputs = []` by (fs[MEM] >> fs[inst_wf_def]) >>
      drule_all current_exec_copy3_opcodes_pair_forward >> simp[]) >>
  Cases_on `MEM inst.inst_opcode [ASSIGN; SHA3]`
  >- metis_tac[current_exec_assign_sha3_pair_forward] >>
  Cases_on `MEM inst.inst_opcode [GETFMP; INITIAL_FMP; PARAM; FMP_PARAM; RETPC_PARAM]`
  >- metis_tac[current_exec_fmp_read_pair_forward] >>
  Cases_on `MEM inst.inst_opcode [CALL; STATICCALL]`
  >- metis_tac[current_exec_call_opcodes_pair_forward] >>
  Cases_on `MEM inst.inst_opcode [CREATE; CREATE2]`
  >- metis_tac[current_exec_create_opcodes_pair_forward] >>
  suspend "remaining_opcodes"
QED

Resume current_exec_noninvoke_ok_pair_forward[remaining_opcodes]:
  `inst'.inst_opcode = inst.inst_opcode` by fs[inst_pair_def] >>
  Cases_on `inst.inst_opcode` >> gvs[MEM]
  >~ [`inst.inst_opcode = ISTORE`]
  >- (`inst.inst_outputs = []` by fs[inst_wf_def] >>
      metis_tac[current_exec_istore_extcodecopy_pair_forward, MEM])
  >~ [`inst.inst_opcode = EXTCODECOPY`]
  >- (`inst.inst_outputs = []` by fs[inst_wf_def] >>
      metis_tac[current_exec_istore_extcodecopy_pair_forward, MEM])
  >~ [`inst.inst_opcode = GAS`]
  >- (stepInstBaseLib.with_opcode_clause gvs >> drule_all current_exec_gas_pair_forward >> simp[])
  >~ [`inst.inst_opcode = DELEGATECALL`]
  >- (drule_all current_exec_delegatecall_opcode_pair_forward >> simp[])
  >~ [`inst.inst_opcode = LOG`]
  >- (`inst.inst_outputs = []` by fs[inst_wf_def] >>
      drule_all current_exec_log_pair_forward >> simp[])
  >~ [`inst.inst_opcode = ALLOCA`]
  >- (drule_all current_exec_alloca_pair_forward >> simp[])
  >~ [`inst.inst_opcode = BUMP`]
  >- (drule_all current_exec_bump_pair_forward >> simp[])
  >~ [`inst.inst_opcode = SETFMP`]
  >- (drule_all current_exec_setfmp_pair_forward >> simp[])
  >~ [`inst.inst_opcode = DALLOCA`]
  >- (drule_all current_exec_dalloca_pair_forward >> simp[])
  >~ [`inst.inst_opcode = NOP`]
  >- (`inst.inst_outputs = []` by fs[inst_wf_def] >>
      drule_all current_exec_nop_pair_forward >> simp[])
  >~ [`inst.inst_opcode = JMP`]
  >- (`inst.inst_outputs = []` by fs[inst_wf_def] >>
      metis_tac[current_exec_jumps_pair_forward, MEM])
  >~ [`inst.inst_opcode = JNZ`]
  >- (`inst.inst_outputs = []` by fs[inst_wf_def] >>
      metis_tac[current_exec_jumps_pair_forward, MEM])
  >~ [`inst.inst_opcode = DJMP`]
  >- (`inst.inst_outputs = []` by fs[inst_wf_def] >>
      metis_tac[current_exec_jumps_pair_forward, MEM])
  >~ [`inst.inst_opcode = ASSERT`]
  >- (`inst.inst_outputs = []` by fs[inst_wf_def] >>
      metis_tac[current_exec_assertions_pair_forward, MEM])
  >~ [`inst.inst_opcode = ASSERT_UNREACHABLE`]
  >- (`inst.inst_outputs = []` by fs[inst_wf_def] >>
      metis_tac[current_exec_assertions_pair_forward, MEM]) >>
  stepInstBaseLib.with_opcode_clause gvs >> gvs[AllCaseEqs()] >>
  qpat_x_assum `_ = OK t` mp_tac >> pairarg_tac >> simp[]
QED

Finalise current_exec_noninvoke_ok_pair_forward

Theorem current_exec_pack_dret_pair_forward:
  !pairs cursor a b ptrs final t.
  state_rel sg a b /\ pack_dret_dynamic cursor pairs a = (ptrs,final,t) ==>
  ?t'. pack_dret_dynamic cursor pairs b = (ptrs,final,t') /\ state_rel sg t t'
Proof
  Induct >> simp[pack_dret_dynamic_def] >> rpt strip_tac >> gvs[] >>
  PairCases_on `h` >> gvs[pack_dret_dynamic_def] >>
  qpat_x_assum `_ = (ptrs,final,t)` mp_tac >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  `state_rel sg (mcopy (w2n cursor) (w2n h0) (w2n h1) a)
                (mcopy (w2n cursor) (w2n h0) (w2n h1) b)` by
    metis_tac[current_exec_memory_state_rel] >>
  first_x_assum drule_all >> strip_tac >> simp[]
QED

Theorem current_exec_ret_pair_forward:
  MEM inst.inst_opcode [RET; RETFMP] /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  step_inst_base inst st = IntRet v t ==>
  ?t'. step_inst_base inst' st' = IntRet v t' /\ execution_frame t' = execution_frame t
Proof
  strip_tac >> drule_all inst_pair_ops >> simp[ops_pair_def] >> strip_tac >>
  `inst'.inst_opcode = inst.inst_opcode` by fs[inst_pair_def] >>
  `eval_operands inst'.inst_operands st' = eval_operands inst.inst_operands st` by
    metis_tac[eval_operands_rel] >>
  `st'.vs_fmp = st.vs_fmp` by fs[state_rel_def, execution_frame_def] >>
  fs[MEM] >>
  qpat_x_assum `inst'.inst_opcode = inst.inst_opcode` mp_tac >> simp[] >>
  strip_tac >> stepInstBaseLib.with_opcode_clause gvs >> gvs[AllCaseEqs()] >>
  fs[state_rel_def]
QED

Theorem current_exec_dret_pair_forward:
  inst.inst_opcode = DRET /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  step_inst_base inst st = IntRet v t ==>
  ?t'. step_inst_base inst' st' = IntRet v t' /\ execution_frame t' = execution_frame t
Proof
  strip_tac >> drule_all inst_pair_ops >> simp[ops_pair_def] >> strip_tac >>
  `inst'.inst_opcode = DRET` by fs[inst_pair_def] >>
  `eval_operands inst'.inst_operands st' = eval_operands inst.inst_operands st` by
    metis_tac[eval_operands_rel] >>
  `st'.vs_call_entry_fmp = st.vs_call_entry_fmp` by
    fs[state_rel_def, execution_frame_def] >>
  `parse_dret_shape inst' = parse_dret_shape inst` by
    (irule parse_dret_shape_rename >> qexists_tac `sg` >> fs[inst_pair_def]) >>
  stepInstBaseLib.with_opcode_clause gvs >> gvs[AllCaseEqs()] >>
  `inst'.inst_outputs = []` by gvs[inst_pair_def] >>
  gvs[] >> qpat_x_assum `_ = IntRet v t` mp_tac >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule_all current_exec_pack_dret_pair_forward >> strip_tac >> simp[] >>
  fs[state_rel_def, execution_frame_def]
QED

Theorem current_exec_halt_opcodes_pair_forward:
  MEM inst.inst_opcode [STOP; RETURN; SINK; SELFDESTRUCT] /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  step_inst_base inst st = Halt t ==>
  ?t'. step_inst_base inst' st' = Halt t' /\ execution_frame t' = execution_frame t
Proof
  strip_tac >> drule_all inst_pair_ops >> simp[ops_pair_def] >> strip_tac >>
  `inst'.inst_opcode = inst.inst_opcode` by fs[inst_pair_def] >>
  `eval_operands inst'.inst_operands st' = eval_operands inst.inst_operands st` by
    metis_tac[eval_operands_rel] >>
  `st'.vs_call_ctx = st.vs_call_ctx /\ st'.vs_memory = st.vs_memory /\
   st'.vs_accounts = st.vs_accounts` by fs[state_rel_def, execution_frame_def] >>
  fs[MEM] >>
  qpat_x_assum `inst'.inst_opcode = inst.inst_opcode` mp_tac >> simp[] >>
  strip_tac >> stepInstBaseLib.with_opcode_clause gvs >> gvs[AllCaseEqs()] >>
  rpt (qpat_x_assum `SOME _ = eval_operand _ _` (assume_tac o SYM)) >> simp[] >>
  fs[state_rel_def, execution_frame_def, halt_state_def, set_returndata_def]
QED

Theorem current_exec_simple_abort_pair_forward:
  MEM inst.inst_opcode [REVERT; INVALID; ASSERT; ASSERT_UNREACHABLE;
                       SSTORE; TSTORE; LOG; SELFDESTRUCT; CALL; CREATE; CREATE2;
                       RETURNDATACOPY] /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  step_inst_base inst st = Abort reason t ==>
  ?t'. step_inst_base inst' st' = Abort reason t' /\ execution_frame t' = execution_frame t
Proof
  strip_tac >> drule_all inst_pair_ops >> simp[ops_pair_def] >> strip_tac >>
  `inst'.inst_opcode = inst.inst_opcode` by fs[inst_pair_def] >>
  `eval_operands inst'.inst_operands st' = eval_operands inst.inst_operands st` by
    metis_tac[eval_operands_rel] >>
  `st'.vs_call_ctx = st.vs_call_ctx /\ st'.vs_memory = st.vs_memory /\
   st'.vs_returndata = st.vs_returndata` by fs[state_rel_def, execution_frame_def] >>
  fs[MEM] >>
  qpat_x_assum `inst'.inst_opcode = inst.inst_opcode` mp_tac >> simp[] >>
  strip_tac >> stepInstBaseLib.with_opcode_clause gvs >>
  gvs[current_exec_ext_call_not_abort, exec_write2_def, exec_create_abort_iff,
      AllCaseEqs()] >>
  rpt (qpat_x_assum `SOME _ = eval_operand _ _` (assume_tac o SYM)) >> simp[] >>
  fs[state_rel_def, execution_frame_def, halt_state_def, revert_state_def,
     set_returndata_def] >>
  gvs[inst_pair_def, LENGTH_EQ_NUM_compute] >>
  qexists_tac `halt_state (set_returndata [] st')` >>
  simp[halt_state_def, set_returndata_def]
QED

Theorem current_exec_noninvoke_intret_pair_forward:
  inst.inst_opcode <> INVOKE /\ inst_pair sg inst inst' /\ state_rel sg st st' /\
  step_inst_base inst st = IntRet v t ==>
  ?t'. step_inst_base inst' st' = IntRet v t' /\ execution_frame t' = execution_frame t
Proof
  strip_tac >> drule step_inst_base_intret_opcodes >> strip_tac
  >- metis_tac[current_exec_ret_pair_forward, MEM]
  >- metis_tac[current_exec_ret_pair_forward, MEM] >>
  `inst.inst_opcode = DRET` by metis_tac[] >>
  drule_all current_exec_dret_pair_forward >> simp[]
QED

Theorem current_exec_noninvoke_halt_pair_forward:
  inst.inst_opcode <> INVOKE /\ inst_pair sg inst inst' /\ state_rel sg st st' /\
  step_inst_base inst st = Halt t ==>
  ?t'. step_inst_base inst' st' = Halt t' /\ execution_frame t' = execution_frame t
Proof
  strip_tac >> drule step_inst_base_halt_opcodes >> strip_tac >>
  metis_tac[current_exec_halt_opcodes_pair_forward, MEM]
QED

Theorem current_exec_noninvoke_abort_pair_forward:
  inst.inst_opcode <> INVOKE /\ inst_pair sg inst inst' /\ state_rel sg st st' /\
  step_inst_base inst st = Abort reason t ==>
  ?t'. step_inst_base inst' st' = Abort reason t' /\ execution_frame t' = execution_frame t
Proof
  strip_tac >>
  `MEM inst.inst_opcode [REVERT; INVALID; ASSERT; ASSERT_UNREACHABLE;
                        SSTORE; TSTORE; LOG; SELFDESTRUCT; CALL; CREATE; CREATE2;
                        RETURNDATACOPY]` by
    (drule step_inst_base_abort_opcodes >> simp[MEM] >> metis_tac[]) >>
  drule_all current_exec_simple_abort_pair_forward >> simp[]
QED

Theorem current_exec_step_noninvoke_ok_pair_forward:
  inst_wf inst /\ inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> PHI /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  step_inst fuel C inst st = OK t ==>
  ?t'. step_inst fuel C' inst' st' = OK t' /\ state_rel sg1 t t'
Proof
  strip_tac >> `inst'.inst_opcode <> INVOKE` by fs[inst_pair_def] >>
  gvs[step_inst_non_invoke] >> drule_all current_exec_noninvoke_ok_pair_forward >> simp[]
QED

Theorem current_exec_step_noninvoke_intret_pair_forward:
  inst.inst_opcode <> INVOKE /\ inst_pair sg inst inst' /\ state_rel sg st st' /\
  step_inst fuel C inst st = IntRet v t ==>
  ?t'. step_inst fuel C' inst' st' = IntRet v t' /\ execution_frame t' = execution_frame t
Proof
  strip_tac >> `inst'.inst_opcode <> INVOKE` by fs[inst_pair_def] >>
  gvs[step_inst_non_invoke] >> drule_all current_exec_noninvoke_intret_pair_forward >> simp[]
QED

Theorem current_exec_step_noninvoke_halt_pair_forward:
  inst.inst_opcode <> INVOKE /\ inst_pair sg inst inst' /\ state_rel sg st st' /\
  step_inst fuel C inst st = Halt t ==>
  ?t'. step_inst fuel C' inst' st' = Halt t' /\ execution_frame t' = execution_frame t
Proof
  strip_tac >> `inst'.inst_opcode <> INVOKE` by fs[inst_pair_def] >>
  gvs[step_inst_non_invoke] >> drule_all current_exec_noninvoke_halt_pair_forward >> simp[]
QED

Theorem current_exec_step_noninvoke_abort_pair_forward:
  inst.inst_opcode <> INVOKE /\ inst_pair sg inst inst' /\ state_rel sg st st' /\
  step_inst fuel C inst st = Abort reason t ==>
  ?t'. step_inst fuel C' inst' st' = Abort reason t' /\ execution_frame t' = execution_frame t
Proof
  strip_tac >> `inst'.inst_opcode <> INVOKE` by fs[inst_pair_def] >>
  gvs[step_inst_non_invoke] >> drule_all current_exec_noninvoke_abort_pair_forward >> simp[]
QED
