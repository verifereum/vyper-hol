Theory makeSsaCurrentExecRuntime
Ancestors
  makeSsaCurrentRuntime o1FrameLockstep venomExecProps venomExecProofs
  venomCallOracleDefs
  venomInstProps venomWf venomState venomExecSemantics stateFrame finite_map list pred_set
Libs
  stepInstBaseLib

Theorem current_exec_lookup_unwritten:
  step_inst fuel C inst st = OK t /\ ~MEM v inst.inst_outputs ==>
  lookup_var v t = lookup_var v st
Proof
  strip_tac >> Cases_on `is_terminator inst.inst_opcode`
  >- metis_tac[step_terminator_preserves_vars] >>
  metis_tac[step_preserves_non_output_vars]
QED

Theorem current_exec_lookup_written:
  step_inst fuel C inst st = OK t /\ inst_wf inst /\
  inst.inst_opcode <> PHI /\ MEM v inst.inst_outputs ==>
  IS_SOME (lookup_var v t)
Proof
  strip_tac >>
  `~is_terminator inst.inst_opcode` by metis_tac[terminator_no_outputs, MEM] >>
  drule_all step_inst_fdom >> strip_tac >>
  fs[lookup_var_def, FLOOKUP_DEF]
QED

Theorem current_exec_update_last_slots:
  state_rel sg st st' /\ current_last_output_slots sg [out] [out'] sg1 ==>
  state_rel sg1 (update_var out value st) (update_var out' value st')
Proof
  strip_tac >>
  `bind_outputs [out'] [value] st' = SOME (update_var out' value st')` by
    simp[bind_outputs_def] >>
  drule_all current_runtime_bind_last_slots >> simp[bind_outputs_def]
QED

Theorem current_exec_pure1_pair:
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  exec_pure1 f inst' st' = OK t' ==>
  ?t. exec_pure1 f inst st = OK t /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >>
  simp[ops_pair_def] >> strip_tac >>
  fs[exec_pure1_def, AllCaseEqs()] >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  `LENGTH inst.inst_outputs = 1` by
    fs[current_last_output_slots_def] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  metis_tac[current_exec_update_last_slots]
QED

Theorem current_exec_pure2_pair:
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  exec_pure2 f inst' st' = OK t' ==>
  ?t. exec_pure2 f inst st = OK t /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >>
  simp[ops_pair_def] >> strip_tac >>
  fs[exec_pure2_def, AllCaseEqs()] >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  `LENGTH inst.inst_outputs = 1` by
    fs[current_last_output_slots_def] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  metis_tac[current_exec_update_last_slots]
QED

Theorem current_exec_pure3_pair:
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  exec_pure3 f inst' st' = OK t' ==>
  ?t. exec_pure3 f inst st = OK t /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >>
  simp[ops_pair_def] >> strip_tac >>
  fs[exec_pure3_def, AllCaseEqs()] >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  `LENGTH inst.inst_outputs = 1` by
    fs[current_last_output_slots_def] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  metis_tac[current_exec_update_last_slots]
QED

Theorem current_exec_read0_pair:
  (!a b. execution_frame a = execution_frame b ==> f a = f b) /\
  state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  exec_read0 f inst' st' = OK t' ==>
  ?t. exec_read0 f inst st = OK t /\ state_rel sg1 t t'
Proof
  strip_tac >> fs[exec_read0_def, AllCaseEqs()] >>
  `LENGTH inst.inst_outputs = 1` by fs[current_last_output_slots_def] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  `f st = f st'` by (first_x_assum irule >> fs[state_rel_def]) >>
  metis_tac[current_exec_update_last_slots]
QED

Theorem current_exec_read1_pair:
  (!v a b. execution_frame a = execution_frame b ==> f v a = f v b) /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  exec_read1 f inst' st' = OK t' ==>
  ?t. exec_read1 f inst st = OK t /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >>
  simp[ops_pair_def] >> strip_tac >>
  fs[exec_read1_def, AllCaseEqs()] >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  `LENGTH inst.inst_outputs = 1` by fs[current_last_output_slots_def] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  `!v. f v st = f v st'` by
    (gen_tac >> first_x_assum irule >> fs[state_rel_def]) >>
  metis_tac[current_exec_update_last_slots]
QED

Theorem current_exec_empty_last_slots:
  state_rel sg st st' /\ current_last_output_slots sg [] [] sg1 ==>
  state_rel sg1 st st'
Proof
  strip_tac >>
  `bind_outputs [] [] st' = SOME st'` by simp[bind_outputs_def] >>
  drule_all current_runtime_bind_last_slots >> simp[bind_outputs_def]
QED

Theorem current_exec_write2_pair:
  (!x y a b. state_rel sg a b ==> state_rel sg (f x y a) (f x y b)) /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  inst.inst_outputs = [] /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  exec_write2 f inst' st' = OK t' ==>
  ?t. exec_write2 f inst st = OK t /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >>
  simp[ops_pair_def] >> strip_tac >>
  fs[exec_write2_def, AllCaseEqs()] >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  `inst'.inst_outputs = []` by fs[current_last_output_slots_def] >>
  gvs[] >>
  metis_tac[current_exec_empty_last_slots]
QED

Theorem current_exec_gas_pair:
  state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  exec_gas inst' st' = OK t' ==>
  ?t. exec_gas inst st = OK t /\ state_rel sg1 t t'
Proof
  strip_tac >>
  `st'.vs_gas_readings = st.vs_gas_readings` by
    fs[state_rel_def, execution_frame_def] >>
  fs[exec_gas_def, AllCaseEqs()] >>
  `LENGTH inst.inst_outputs = 1` by fs[current_last_output_slots_def] >>
  Cases_on `inst.inst_outputs` >> gvs[]
  >- metis_tac[current_exec_update_last_slots] >>
  irule current_exec_update_last_slots >>
  qexists_tac `sg` >> simp[] >>
  fs[state_rel_def, execution_frame_def, vars_rel_def, lookup_var_def]
QED

Theorem current_exec_bump_pair:
  inst.inst_opcode = BUMP /\ inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  step_inst_base inst' st' = OK t' ==>
  ?t. step_inst_base inst st = OK t /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >>
  simp[ops_pair_def] >> strip_tac >>
  `inst'.inst_opcode = BUMP` by fs[inst_pair_def] >>
  fs[Once step_inst_base_def, AllCaseEqs()] >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  `LENGTH inst.inst_outputs = 2` by fs[current_last_output_slots_def] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  rename1 `inst.inst_outputs = out1::rest` >> Cases_on `rest` >> gvs[] >>
  rename1 `inst.inst_outputs = [out1;out2]` >>
  rename1 `inst'.inst_outputs = [out1';out2']` >>
  rename1 `update_var out2' (bv + szv) (update_var out1' bv st')` >>
  `bind_outputs [out1';out2'] [bv;word_add bv szv] st' =
    SOME (update_var out2' (word_add bv szv) (update_var out1' bv st'))` by
    simp[bind_outputs_def] >>
  drule_all current_runtime_bind_last_slots >>
  simp[bind_outputs_def, Once step_inst_base_def] >> metis_tac[]
QED


Theorem current_exec_read0_opcodes_pair:
  MEM inst.inst_opcode
    [CALLER; ADDRESS; CALLVALUE; ORIGIN; GASPRICE; CHAINID; COINBASE;
     TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE; BLOBBASEFEE;
     SELFBALANCE; CALLDATASIZE; RETURNDATASIZE; MEMTOP; CODESIZE] /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  step_inst_base inst' st' = OK t' ==>
  ?t. step_inst_base inst st = OK t /\ state_rel sg1 t t'
Proof
  strip_tac >>
  `inst'.inst_opcode = inst.inst_opcode` by fs[inst_pair_def] >>
  fs[MEM] >>
  qpat_x_assum `inst'.inst_opcode = inst.inst_opcode` mp_tac >> simp[] >>
  strip_tac >> stepInstBaseLib.with_opcode_clause fs >>
  ho_match_mp_tac current_exec_read0_pair >> asm_rewrite_tac[] >>
  rpt strip_tac >> fs[execution_frame_def]
QED

Theorem current_exec_read1_opcodes_pair:
  MEM inst.inst_opcode
    [MLOAD; SLOAD; TLOAD; BLOCKHASH; BLOBHASH; BALANCE; CALLDATALOAD;
     EXTCODESIZE; EXTCODEHASH; ILOAD; DLOAD] /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  step_inst_base inst' st' = OK t' ==>
  ?t. step_inst_base inst st = OK t /\ state_rel sg1 t t'
Proof
  strip_tac >>
  `inst'.inst_opcode = inst.inst_opcode` by fs[inst_pair_def] >>
  fs[MEM] >>
  qpat_x_assum `inst'.inst_opcode = inst.inst_opcode` mp_tac >> simp[] >>
  strip_tac >> stepInstBaseLib.with_opcode_clause fs >>
  ho_match_mp_tac current_exec_read1_pair >> asm_rewrite_tac[] >>
  rpt strip_tac >>
  fs[execution_frame_def, mload_def, sload_def, tload_def,
     contract_storage_def, contract_transient_def]
QED

Theorem current_exec_store_state_rel:
  state_rel sg a b ==>
  state_rel sg (mstore off v a) (mstore off v b) /\
  state_rel sg (mstore8 off v a) (mstore8 off v b) /\
  state_rel sg (sstore key v a) (sstore key v b) /\
  state_rel sg (tstore key v a) (tstore key v b)
Proof
  simp[state_rel_def, execution_frame_def, vars_rel_def, lookup_var_def,
       mstore_def, mstore8_def, sstore_def, tstore_def,
       write_memory_with_expansion_def, contract_storage_def,
       contract_transient_def]
QED

Theorem current_exec_write2_opcodes_pair:
  MEM inst.inst_opcode [MSTORE; MSTORE8; SSTORE; TSTORE] /\
  inst.inst_outputs = [] /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  step_inst_base inst' st' = OK t' ==>
  ?t. step_inst_base inst st = OK t /\ state_rel sg1 t t'
Proof
  strip_tac >>
  `inst'.inst_opcode = inst.inst_opcode` by fs[inst_pair_def] >>
  `st'.vs_call_ctx = st.vs_call_ctx` by
    fs[state_rel_def, execution_frame_def] >>
  `eval_operands inst'.inst_operands st' = eval_operands inst.inst_operands st` by
    (drule_all inst_pair_ops >> simp[ops_pair_def] >>
     metis_tac[eval_operands_rel]) >>
  fs[MEM] >>
  qpat_x_assum `inst'.inst_opcode = inst.inst_opcode` mp_tac >> simp[] >>
  strip_tac >> stepInstBaseLib.with_opcode_clause fs >>
  gvs[AllCaseEqs()] >>
  ho_match_mp_tac current_exec_write2_pair >> asm_rewrite_tac[] >>
  rpt strip_tac >> metis_tac[current_exec_store_state_rel]
QED

Theorem current_exec_memory_state_rel:
  state_rel sg a b ==>
  state_rel sg (write_memory_with_expansion off bytes a)
               (write_memory_with_expansion off bytes b) /\
  state_rel sg (mcopy dst src sz a) (mcopy dst src sz b) /\
  state_rel sg (istore off v a) (istore off v b)
Proof
  simp[state_rel_def, execution_frame_def, vars_rel_def, lookup_var_def,
       write_memory_with_expansion_def, mcopy_def, istore_def, mstore_def,
       read_memory_def]
QED

Theorem current_exec_copy3_opcodes_pair:
  MEM inst.inst_opcode [MCOPY; CALLDATACOPY; RETURNDATACOPY; DLOADBYTES; CODECOPY] /\
  inst.inst_outputs = [] /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  step_inst_base inst' st' = OK t' ==>
  ?t. step_inst_base inst st = OK t /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >> simp[ops_pair_def] >> strip_tac >>
  `inst'.inst_opcode = inst.inst_opcode` by fs[inst_pair_def] >>
  `st'.vs_call_ctx = st.vs_call_ctx /\ st'.vs_returndata = st.vs_returndata /\
   st'.vs_data_section = st.vs_data_section /\ st'.vs_code = st.vs_code` by
    fs[state_rel_def, execution_frame_def] >>
  `inst'.inst_outputs = []` by gvs[current_last_output_slots_def] >>
  fs[MEM] >>
  qpat_x_assum `inst'.inst_opcode = inst.inst_opcode` mp_tac >> simp[] >>
  strip_tac >> stepInstBaseLib.with_opcode_clause fs >>
  gvs[AllCaseEqs()] >>
  metis_tac[current_exec_empty_last_slots, current_exec_memory_state_rel]
QED

Theorem current_exec_istore_extcodecopy_pair:
  MEM inst.inst_opcode [ISTORE; EXTCODECOPY] /\ inst.inst_outputs = [] /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  step_inst_base inst' st' = OK t' ==>
  ?t. step_inst_base inst st = OK t /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >> simp[ops_pair_def] >> strip_tac >>
  `inst'.inst_opcode = inst.inst_opcode` by fs[inst_pair_def] >>
  `st'.vs_accounts = st.vs_accounts` by fs[state_rel_def, execution_frame_def] >>
  `inst'.inst_outputs = []` by gvs[current_last_output_slots_def] >>
  fs[MEM] >>
  qpat_x_assum `inst'.inst_opcode = inst.inst_opcode` mp_tac >> simp[] >>
  strip_tac >> stepInstBaseLib.with_opcode_clause fs >>
  gvs[AllCaseEqs()] >>
  metis_tac[current_exec_empty_last_slots, current_exec_memory_state_rel]
QED

Theorem current_exec_assign_sha3_pair:
  MEM inst.inst_opcode [ASSIGN; SHA3] /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  step_inst_base inst' st' = OK t' ==>
  ?t. step_inst_base inst st = OK t /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >> simp[ops_pair_def] >> strip_tac >>
  `inst'.inst_opcode = inst.inst_opcode` by fs[inst_pair_def] >>
  `st'.vs_memory = st.vs_memory` by fs[state_rel_def, execution_frame_def] >>
  fs[MEM] >>
  qpat_x_assum `inst'.inst_opcode = inst.inst_opcode` mp_tac >> simp[] >>
  strip_tac >> stepInstBaseLib.with_opcode_clause fs >>
  gvs[AllCaseEqs()] >>
  `LENGTH inst.inst_outputs = 1` by fs[current_last_output_slots_def] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  metis_tac[current_exec_update_last_slots]
QED

Theorem current_exec_fmp_state_rel:
  state_rel sg a b ==> state_rel sg (a with vs_fmp := v) (b with vs_fmp := v)
Proof
  simp[state_rel_def, execution_frame_def, vars_rel_def, lookup_var_def]
QED

Theorem current_exec_fmp_read_pair:
  MEM inst.inst_opcode [GETFMP; INITIAL_FMP; PARAM; FMP_PARAM; RETPC_PARAM] /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  step_inst_base inst' st' = OK t' ==>
  ?t. step_inst_base inst st = OK t /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >> simp[ops_pair_def] >> strip_tac >>
  `inst'.inst_opcode = inst.inst_opcode` by fs[inst_pair_def] >>
  `st'.vs_fmp = st.vs_fmp /\ st'.vs_initial_fmp = st.vs_initial_fmp /\
   st'.vs_params = st.vs_params /\ st'.vs_return_pc_token = st.vs_return_pc_token` by
    fs[state_rel_def, execution_frame_def] >>
  fs[MEM] >>
  qpat_x_assum `inst'.inst_opcode = inst.inst_opcode` mp_tac >> simp[] >>
  strip_tac >> stepInstBaseLib.with_opcode_clause fs >>
  gvs[AllCaseEqs(), op_rename_lit] >>
  `LENGTH inst.inst_outputs = 1` by fs[current_last_output_slots_def] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  metis_tac[current_exec_update_last_slots]
QED

Theorem current_exec_setfmp_pair:
  inst.inst_opcode = SETFMP /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  step_inst_base inst' st' = OK t' ==>
  ?t. step_inst_base inst st = OK t /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >> simp[ops_pair_def] >> strip_tac >>
  `inst'.inst_opcode = SETFMP` by fs[inst_pair_def] >>
  stepInstBaseLib.with_opcode_clause fs >> gvs[AllCaseEqs()] >>
  `inst.inst_outputs = []` by gvs[current_last_output_slots_def] >>
  gvs[] >> metis_tac[current_exec_empty_last_slots, current_exec_fmp_state_rel]
QED

Theorem current_exec_dalloca_pair:
  inst.inst_opcode = DALLOCA /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  step_inst_base inst' st' = OK t' ==>
  ?t. step_inst_base inst st = OK t /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >> simp[ops_pair_def] >> strip_tac >>
  `inst'.inst_opcode = DALLOCA` by fs[inst_pair_def] >>
  `st'.vs_fmp = st.vs_fmp` by fs[state_rel_def, execution_frame_def] >>
  stepInstBaseLib.with_opcode_clause fs >> gvs[AllCaseEqs()] >>
  `LENGTH inst.inst_outputs = 1` by fs[current_last_output_slots_def] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  metis_tac[current_exec_update_last_slots, current_exec_fmp_state_rel]
QED

Theorem current_exec_nop_pair:
  inst.inst_opcode = NOP /\ inst.inst_outputs = [] /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  step_inst_base inst' st' = OK t' ==>
  ?t. step_inst_base inst st = OK t /\ state_rel sg1 t t'
Proof
  strip_tac >> `inst'.inst_opcode = NOP` by fs[inst_pair_def] >>
  stepInstBaseLib.with_opcode_clause fs >> gvs[] >>
  `inst'.inst_outputs = []` by gvs[current_last_output_slots_def] >>
  metis_tac[current_exec_empty_last_slots]
QED

Theorem current_exec_alloca_pair:
  inst.inst_opcode = ALLOCA /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  step_inst_base inst' st' = OK t' ==>
  ?t. step_inst_base inst st = OK t /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >> simp[ops_pair_def] >> strip_tac >>
  `inst'.inst_opcode = ALLOCA /\ inst'.inst_id = inst.inst_id` by fs[inst_pair_def] >>
  `st'.vs_allocas = st.vs_allocas /\ st'.vs_alloca_next = st.vs_alloca_next` by
    fs[state_rel_def, execution_frame_def] >>
  stepInstBaseLib.with_opcode_clause fs >>
  gvs[exec_alloca_def, AllCaseEqs(), op_rename_lit] >>
  `LENGTH inst.inst_outputs = 1` by fs[current_last_output_slots_def] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  irule current_exec_update_last_slots >> qexists_tac `sg` >> simp[] >>
  fs[state_rel_def, execution_frame_def, vars_rel_def, lookup_var_def]
QED

Theorem current_exec_log_pair:
  inst.inst_opcode = LOG /\ inst.inst_outputs = [] /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  step_inst_base inst' st' = OK t' ==>
  ?t. step_inst_base inst st = OK t /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >> simp[ops_pair_def] >> strip_tac >>
  `inst'.inst_opcode = LOG` by fs[inst_pair_def] >>
  `st'.vs_call_ctx = st.vs_call_ctx /\ st'.vs_memory = st.vs_memory /\
   st'.vs_logs = st.vs_logs` by fs[state_rel_def, execution_frame_def] >>
  `eval_operands inst'.inst_operands st' = eval_operands inst.inst_operands st` by
    metis_tac[eval_operands_rel] >>
  `inst'.inst_outputs = []` by gvs[current_last_output_slots_def] >>
  stepInstBaseLib.with_opcode_clause fs >> gvs[AllCaseEqs(), op_rename_lit] >>
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
     irule rich_listTheory.LIST_REL_DROP >>
     first_assum MATCH_ACCEPT_TAC) >>
  gvs[] >>
  qpat_x_assum `SOME off = _` (assume_tac o SYM) >> simp[] >>
  irule current_exec_empty_last_slots >> qexists_tac `sg` >> simp[] >>
  fs[state_rel_def, execution_frame_def, vars_rel_def, lookup_var_def]
QED

Theorem current_exec_oracle_requests_pair:
  state_rel sg a b ==>
  venom_call_request a addr value ao sz static =
    venom_call_request b addr value ao sz static /\
  venom_create_request a value ao sz salt = venom_create_request b value ao sz salt
Proof
  simp[state_rel_def, execution_frame_def, venom_call_request_def,
       venom_create_request_def, read_memory_def]
QED

Theorem current_exec_consume_call_pair:
  state_rel sg a b ==>
  FST (consume_call_outcome rq ro rs a) = FST (consume_call_outcome rq ro rs b) /\
  state_rel sg (SND (consume_call_outcome rq ro rs a))
               (SND (consume_call_outcome rq ro rs b))
Proof
  simp[state_rel_def, execution_frame_def, vars_rel_def, lookup_var_def,
       write_memory_with_expansion_def]
QED

Theorem current_exec_consume_create_pair:
  state_rel sg a b ==>
  FST (consume_create_outcome rq a) = FST (consume_create_outcome rq b) /\
  state_rel sg (SND (consume_create_outcome rq a))
               (SND (consume_create_outcome rq b))
Proof
  simp[state_rel_def, execution_frame_def, vars_rel_def, lookup_var_def]
QED

Theorem current_exec_ext_call_pair:
  state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  exec_ext_call inst' st' gas addr value ao sz ro rs static = OK t' ==>
  ?t. exec_ext_call inst st gas addr value ao sz ro rs static = OK t /\
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
  fs[exec_ext_call_def, AllCaseEqs()] >>
  `LENGTH inst.inst_outputs = 1` by fs[current_last_output_slots_def] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  metis_tac[current_exec_update_last_slots]
QED

Theorem current_exec_create_pair:
  state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  exec_create inst' st' value off sz salt = OK t' ==>
  ?t. exec_create inst st value off sz salt = OK t /\ state_rel sg1 t t'
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
  fs[exec_create_def, AllCaseEqs()] >>
  `LENGTH inst.inst_outputs = 1` by fs[current_last_output_slots_def] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  metis_tac[current_exec_update_last_slots]
QED

Theorem current_exec_call_opcodes_pair:
  MEM inst.inst_opcode [CALL; STATICCALL] /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  step_inst_base inst' st' = OK t' ==>
  ?t. step_inst_base inst st = OK t /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >> simp[ops_pair_def] >> strip_tac >>
  `inst'.inst_opcode = inst.inst_opcode` by fs[inst_pair_def] >>
  `st'.vs_call_ctx = st.vs_call_ctx` by fs[state_rel_def, execution_frame_def] >>
  fs[MEM] >>
  qpat_x_assum `inst'.inst_opcode = inst.inst_opcode` mp_tac >> simp[] >>
  strip_tac >> stepInstBaseLib.with_opcode_clause fs >> gvs[AllCaseEqs()] >>
  metis_tac[current_exec_ext_call_pair]
QED

Theorem current_exec_create_opcodes_pair:
  MEM inst.inst_opcode [CREATE; CREATE2] /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  step_inst_base inst' st' = OK t' ==>
  ?t. step_inst_base inst st = OK t /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >> simp[ops_pair_def] >> strip_tac >>
  `inst'.inst_opcode = inst.inst_opcode` by fs[inst_pair_def] >>
  `st'.vs_call_ctx = st.vs_call_ctx` by fs[state_rel_def, execution_frame_def] >>
  `eval_operands inst'.inst_operands st' = eval_operands inst.inst_operands st` by
    metis_tac[eval_operands_rel] >>
  fs[MEM] >>
  qpat_x_assum `inst'.inst_opcode = inst.inst_opcode` mp_tac >> simp[] >>
  strip_tac >> stepInstBaseLib.with_opcode_clause fs >> gvs[AllCaseEqs()] >>
  metis_tac[current_exec_create_pair]
QED

Theorem current_exec_delegatecall_state_pair:
  state_rel sg a b ==>
  make_venom_delegatecall_state a target gas data code static =
    make_venom_delegatecall_state b target gas data code static
Proof
  simp[state_rel_def, execution_frame_def, make_venom_delegatecall_state_def,
       venom_to_tx_params_def]
QED

Theorem current_exec_extract_result_pair:
  state_rel sg a b /\
  extract_venom_result b output ro rs result = SOME (v,t') ==>
  ?t. extract_venom_result a output ro rs result = SOME (v,t) /\ state_rel sg t t'
Proof
  strip_tac >> gvs[extract_venom_result_def, AllCaseEqs()] >>
  fs[state_rel_def, execution_frame_def] >>
  pairarg_tac >> gvs[] >>
  simp[state_rel_def, execution_frame_def, vars_rel_def, lookup_var_def,
       write_memory_with_expansion_def] >>
  fs[vars_rel_def, lookup_var_def]
QED

Theorem current_exec_delegatecall_pair:
  state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  exec_delegatecall inst' st' gas addr ao sz ro rs = OK t' ==>
  ?t. exec_delegatecall inst st gas addr ao sz ro rs = OK t /\ state_rel sg1 t t'
Proof
  strip_tac >>
  `st'.vs_memory = st.vs_memory /\ st'.vs_accounts = st.vs_accounts /\
   st'.vs_call_ctx = st.vs_call_ctx` by fs[state_rel_def, execution_frame_def] >>
  fs[exec_delegatecall_def, read_memory_def, AllCaseEqs()] >>
  `!target gas data code static.
    make_venom_delegatecall_state st target gas data code static =
    make_venom_delegatecall_state st' target gas data code static` by
    metis_tac[current_exec_delegatecall_state_pair] >>
  gvs[] >> drule_all current_exec_extract_result_pair >> strip_tac >> simp[] >>
  `LENGTH inst.inst_outputs = 1` by fs[current_last_output_slots_def] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  metis_tac[current_exec_update_last_slots]
QED

Theorem current_exec_delegatecall_opcode_pair:
  inst.inst_opcode = DELEGATECALL /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  step_inst_base inst' st' = OK t' ==>
  ?t. step_inst_base inst st = OK t /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >> simp[ops_pair_def] >> strip_tac >>
  `inst'.inst_opcode = DELEGATECALL` by fs[inst_pair_def] >>
  stepInstBaseLib.with_opcode_clause fs >> gvs[AllCaseEqs()] >>
  metis_tac[current_exec_delegatecall_pair]
QED

Theorem current_exec_jump_state_rel:
  state_rel sg a b ==> state_rel sg (jump_to l a) (jump_to l b)
Proof
  simp[state_rel_def, execution_frame_def, jump_to_def, vars_rel_def, lookup_var_def]
QED

Theorem current_exec_extract_labels_pair:
  !ops ops'. LIST_REL (op_rename sg) ops ops' ==>
  extract_labels ops' = extract_labels ops
Proof
  Induct >> simp[extract_labels_def] >> rpt strip_tac >>
  gvs[] >> Cases_on `h` >> Cases_on `y` >>
  gvs[op_rename_def, extract_labels_def]
QED

Theorem current_exec_jumps_pair:
  MEM inst.inst_opcode [JMP; JNZ; DJMP] /\ inst.inst_outputs = [] /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  step_inst_base inst' st' = OK t' ==>
  ?t. step_inst_base inst st = OK t /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >> simp[ops_pair_def] >> strip_tac >>
  `inst'.inst_opcode = inst.inst_opcode` by fs[inst_pair_def] >>
  `inst'.inst_outputs = []` by gvs[current_last_output_slots_def] >>
  fs[MEM] >>
  qpat_x_assum `inst'.inst_opcode = inst.inst_opcode` mp_tac >> simp[] >>
  strip_tac >> stepInstBaseLib.with_opcode_clause fs >>
  gvs[AllCaseEqs(), op_rename_label] >>
  metis_tac[current_exec_empty_last_slots, current_exec_jump_state_rel,
            current_exec_extract_labels_pair, ops_pair_rename, ops_pair_def]
QED

Theorem current_exec_assertions_pair:
  MEM inst.inst_opcode [ASSERT; ASSERT_UNREACHABLE] /\ inst.inst_outputs = [] /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  step_inst_base inst' st' = OK t' ==>
  ?t. step_inst_base inst st = OK t /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >> simp[ops_pair_def] >> strip_tac >>
  `inst'.inst_opcode = inst.inst_opcode` by fs[inst_pair_def] >>
  `inst'.inst_outputs = []` by gvs[current_last_output_slots_def] >>
  fs[MEM] >>
  qpat_x_assum `inst'.inst_opcode = inst.inst_opcode` mp_tac >> simp[] >>
  strip_tac >> stepInstBaseLib.with_opcode_clause fs >> gvs[AllCaseEqs()] >>
  metis_tac[current_exec_empty_last_slots]
QED

Theorem current_exec_pack_dret_pair:
  !pairs cursor a b ptrs final t'.
  state_rel sg a b /\ pack_dret_dynamic cursor pairs b = (ptrs,final,t') ==>
  ?t. pack_dret_dynamic cursor pairs a = (ptrs,final,t) /\ state_rel sg t t'
Proof
  Induct >> simp[pack_dret_dynamic_def] >> rpt strip_tac >> gvs[] >>
  PairCases_on `h` >> gvs[pack_dret_dynamic_def] >>
  qpat_x_assum `_ = (ptrs,final,t')` mp_tac >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  `state_rel sg (mcopy (w2n cursor) (w2n h0) (w2n h1) a)
                (mcopy (w2n cursor) (w2n h0) (w2n h1) b)` by
    metis_tac[current_exec_memory_state_rel] >>
  first_x_assum drule_all >> strip_tac >> simp[]
QED

Theorem current_exec_ret_pair:
  MEM inst.inst_opcode [RET; RETFMP] /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  step_inst_base inst' st' = IntRet v t' ==>
  ?t. step_inst_base inst st = IntRet v t /\ execution_frame t' = execution_frame t
Proof
  strip_tac >> drule_all inst_pair_ops >> simp[ops_pair_def] >> strip_tac >>
  `inst'.inst_opcode = inst.inst_opcode` by fs[inst_pair_def] >>
  `eval_operands inst'.inst_operands st' = eval_operands inst.inst_operands st` by
    metis_tac[eval_operands_rel] >>
  `st'.vs_fmp = st.vs_fmp` by fs[state_rel_def, execution_frame_def] >>
  fs[MEM] >>
  qpat_x_assum `inst'.inst_opcode = inst.inst_opcode` mp_tac >> simp[] >>
  strip_tac >> stepInstBaseLib.with_opcode_clause fs >> gvs[AllCaseEqs()] >>
  fs[state_rel_def]
QED

Theorem current_exec_dret_pair:
  inst.inst_opcode = DRET /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  step_inst_base inst' st' = IntRet v t' ==>
  ?t. step_inst_base inst st = IntRet v t /\ execution_frame t' = execution_frame t
Proof
  strip_tac >> drule_all inst_pair_ops >> simp[ops_pair_def] >> strip_tac >>
  `inst'.inst_opcode = DRET` by fs[inst_pair_def] >>
  `eval_operands inst'.inst_operands st' = eval_operands inst.inst_operands st` by
    metis_tac[eval_operands_rel] >>
  `st'.vs_call_entry_fmp = st.vs_call_entry_fmp` by
    fs[state_rel_def, execution_frame_def] >>
  `parse_dret_shape inst' = parse_dret_shape inst` by
    (irule parse_dret_shape_rename >> qexists_tac `sg` >> fs[inst_pair_def]) >>
  stepInstBaseLib.with_opcode_clause fs >> gvs[AllCaseEqs()] >>
  `inst.inst_outputs = []` by gvs[inst_pair_def] >>
  gvs[] >> qpat_x_assum `_ = IntRet v t'` mp_tac >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule_all current_exec_pack_dret_pair >> strip_tac >> simp[] >>
  fs[state_rel_def, execution_frame_def]
QED

Theorem current_exec_halt_frame_pair:
  execution_frame a = execution_frame b ==>
  execution_frame (halt_state (set_returndata rd a)) =
    execution_frame (halt_state (set_returndata rd b)) /\
  execution_frame (revert_state (set_returndata rd a)) =
    execution_frame (revert_state (set_returndata rd b)) /\
  execution_frame (halt_state a) = execution_frame (halt_state b)
Proof
  simp[execution_frame_def, halt_state_def, revert_state_def, set_returndata_def]
QED

Theorem current_exec_halt_opcodes_pair:
  MEM inst.inst_opcode [STOP; RETURN; SINK; SELFDESTRUCT] /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  step_inst_base inst' st' = Halt t' ==>
  ?t. step_inst_base inst st = Halt t /\ execution_frame t' = execution_frame t
Proof
  strip_tac >> drule_all inst_pair_ops >> simp[ops_pair_def] >> strip_tac >>
  `inst'.inst_opcode = inst.inst_opcode` by fs[inst_pair_def] >>
  `eval_operands inst'.inst_operands st' = eval_operands inst.inst_operands st` by
    metis_tac[eval_operands_rel] >>
  `st'.vs_call_ctx = st.vs_call_ctx /\ st'.vs_memory = st.vs_memory /\
   st'.vs_accounts = st.vs_accounts` by fs[state_rel_def, execution_frame_def] >>
  fs[MEM] >>
  qpat_x_assum `inst'.inst_opcode = inst.inst_opcode` mp_tac >> simp[] >>
  strip_tac >> stepInstBaseLib.with_opcode_clause fs >> gvs[AllCaseEqs()] >>
  rpt (qpat_x_assum `SOME _ = eval_operand _ _` (assume_tac o SYM)) >> simp[] >>
  fs[state_rel_def, execution_frame_def, halt_state_def, set_returndata_def]
QED

(* Existing no-Abort facts in passSharedFrame and ssaRenamedSim are local. *)
Theorem current_exec_ext_call_not_abort[local]:
  exec_ext_call inst st gas addr value ao as_ ro rs is_static <> Abort reason t
Proof
  rw[exec_ext_call_def] >> gvs[AllCaseEqs()]
QED

Theorem current_exec_simple_abort_pair:
  MEM inst.inst_opcode [REVERT; INVALID; ASSERT; ASSERT_UNREACHABLE;
                       SSTORE; TSTORE; LOG; SELFDESTRUCT; CALL; CREATE; CREATE2;
                       RETURNDATACOPY] /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  step_inst_base inst' st' = Abort reason t' ==>
  ?t. step_inst_base inst st = Abort reason t /\ execution_frame t' = execution_frame t
Proof
  strip_tac >> drule_all inst_pair_ops >> simp[ops_pair_def] >> strip_tac >>
  `inst'.inst_opcode = inst.inst_opcode` by fs[inst_pair_def] >>
  `eval_operands inst'.inst_operands st' = eval_operands inst.inst_operands st` by
    metis_tac[eval_operands_rel] >>
  `st'.vs_call_ctx = st.vs_call_ctx /\ st'.vs_memory = st.vs_memory /\
   st'.vs_returndata = st.vs_returndata` by fs[state_rel_def, execution_frame_def] >>
  fs[MEM] >>
  qpat_x_assum `inst'.inst_opcode = inst.inst_opcode` mp_tac >> simp[] >>
  strip_tac >> stepInstBaseLib.with_opcode_clause fs >>
  gvs[current_exec_ext_call_not_abort, exec_write2_def, exec_create_abort_iff,
      AllCaseEqs()] >>
  rpt (qpat_x_assum `SOME _ = eval_operand _ _` (assume_tac o SYM)) >> simp[] >>
  fs[state_rel_def, execution_frame_def, halt_state_def, revert_state_def,
     set_returndata_def] >>
  gvs[inst_pair_def, LENGTH_EQ_NUM_compute] >>
  qexists_tac `halt_state (set_returndata [] st)` >>
  simp[halt_state_def, set_returndata_def]
QED
