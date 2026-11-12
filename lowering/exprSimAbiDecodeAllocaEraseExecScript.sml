Theory exprSimAbiDecodeAllocaEraseExec
Ancestors
  exprSimAbiDecodeAllocaErase venomExecSemantics venomState finite_map pred_set
  venomCallOracleDefs

Theorem abi_decode_clean_exec_alloca:
  inst.inst_id IN abi_decode_alloca_ids func /\ exec_alloca inst s n = OK t ==>
  exec_alloca inst (abi_decode_clean_allocas func s) n =
    OK (abi_decode_clean_allocas func t)
Proof
  strip_tac >>
  qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
  simp[exec_alloca_def, abi_decode_clean_lookup] >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  Cases_on `t'` >> simp[] >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id` >> simp[]
  >- (strip_tac >> gvs[abi_decode_clean_allocas_def, update_var_def,
                       DRESTRICT_FUPDATE]) >>
  Cases_on `x` >> strip_tac >>
  gvs[abi_decode_clean_allocas_def, update_var_def]
QED

Theorem abi_decode_clean_eval_operand[simp]:
  eval_operand op (abi_decode_clean_allocas func s) = eval_operand op s
Proof
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def,
                       abi_decode_clean_allocas_def]
QED

Theorem abi_decode_clean_eval_operands[simp]:
  eval_operands ops (abi_decode_clean_allocas func s) = eval_operands ops s
Proof
  Induct_on `ops` >> simp[eval_operands_def]
QED

Theorem abi_decode_clean_update_var[simp]:
  update_var out v (abi_decode_clean_allocas func s) =
  abi_decode_clean_allocas func (update_var out v s)
Proof
  simp[update_var_def, abi_decode_clean_allocas_def]
QED

Theorem abi_decode_clean_step_ADD:
  inst.inst_opcode = ADD /\ step_inst_base inst s = OK t ==>
  step_inst_base inst (abi_decode_clean_allocas func s) =
    OK (abi_decode_clean_allocas func t)
Proof
  strip_tac >> fs[Once step_inst_base_def] >>
  gvs[exec_pure2_def, AllCaseEqs()] >> simp[]
QED

Theorem abi_decode_clean_exec_pure2:
  exec_pure2 f inst s = OK t ==>
  exec_pure2 f inst (abi_decode_clean_allocas func s) =
    OK (abi_decode_clean_allocas func t)
Proof
  simp[exec_pure2_def, AllCaseEqs()] >>
  strip_tac >> gvs[]
QED

Theorem abi_decode_clean_exec_pure1:
  exec_pure1 f inst s = OK t ==>
  exec_pure1 f inst (abi_decode_clean_allocas func s) =
    OK (abi_decode_clean_allocas func t)
Proof
  simp[exec_pure1_def, AllCaseEqs()] >> strip_tac >> gvs[]
QED

Theorem abi_decode_clean_exec_pure3:
  exec_pure3 f inst s = OK t ==>
  exec_pure3 f inst (abi_decode_clean_allocas func s) =
    OK (abi_decode_clean_allocas func t)
Proof
  simp[exec_pure3_def, AllCaseEqs()] >> strip_tac >> gvs[]
QED

Theorem abi_decode_clean_exec_pure1_reflect:
  exec_pure1 f inst (abi_decode_clean_allocas func s) = OK u ==>
  ?t. exec_pure1 f inst s = OK t /\ u = abi_decode_clean_allocas func t
Proof
  simp[exec_pure1_def, AllCaseEqs()] >> strip_tac >> gvs[]
QED

Theorem abi_decode_clean_exec_pure2_reflect:
  exec_pure2 f inst (abi_decode_clean_allocas func s) = OK u ==>
  ?t. exec_pure2 f inst s = OK t /\ u = abi_decode_clean_allocas func t
Proof
  simp[exec_pure2_def, AllCaseEqs()] >> strip_tac >> gvs[]
QED

Theorem abi_decode_clean_exec_pure3_reflect:
  exec_pure3 f inst (abi_decode_clean_allocas func s) = OK u ==>
  ?t. exec_pure3 f inst s = OK t /\ u = abi_decode_clean_allocas func t
Proof
  simp[exec_pure3_def, AllCaseEqs()] >> strip_tac >> gvs[]
QED

Theorem abi_decode_clean_exec_read0:
  (!s. f (abi_decode_clean_allocas func s) = f s) /\
  exec_read0 f inst s = OK t ==>
  exec_read0 f inst (abi_decode_clean_allocas func s) =
    OK (abi_decode_clean_allocas func t)
Proof
  simp[exec_read0_def, AllCaseEqs()] >> strip_tac >> gvs[]
QED

Theorem abi_decode_clean_exec_read0_reflect:
  (!s. f (abi_decode_clean_allocas func s) = f s) /\
  exec_read0 f inst (abi_decode_clean_allocas func s) = OK u ==>
  ?t. exec_read0 f inst s = OK t /\ u = abi_decode_clean_allocas func t
Proof
  simp[exec_read0_def, AllCaseEqs()] >> strip_tac >> gvs[]
QED

Theorem abi_decode_clean_exec_read1:
  (!v s. f v (abi_decode_clean_allocas func s) = f v s) /\
  exec_read1 f inst s = OK t ==>
  exec_read1 f inst (abi_decode_clean_allocas func s) =
    OK (abi_decode_clean_allocas func t)
Proof
  simp[exec_read1_def, AllCaseEqs()] >> strip_tac >> gvs[]
QED

Theorem abi_decode_clean_exec_read1_reflect:
  (!v s. f v (abi_decode_clean_allocas func s) = f v s) /\
  exec_read1 f inst (abi_decode_clean_allocas func s) = OK u ==>
  ?t. exec_read1 f inst s = OK t /\ u = abi_decode_clean_allocas func t
Proof
  simp[exec_read1_def, AllCaseEqs()] >> strip_tac >> gvs[]
QED

Theorem abi_decode_clean_exec_write2:
  (!a b s. f a b (abi_decode_clean_allocas func s) =
           abi_decode_clean_allocas func (f a b s)) /\
  exec_write2 f inst s = OK t ==>
  exec_write2 f inst (abi_decode_clean_allocas func s) =
    OK (abi_decode_clean_allocas func t)
Proof
  simp[exec_write2_def, AllCaseEqs()] >> strip_tac >> gvs[]
QED

Theorem abi_decode_clean_exec_write2_reflect:
  (!a b s. f a b (abi_decode_clean_allocas func s) =
           abi_decode_clean_allocas func (f a b s)) /\
  exec_write2 f inst (abi_decode_clean_allocas func s) = OK u ==>
  ?t. exec_write2 f inst s = OK t /\ u = abi_decode_clean_allocas func t
Proof
  simp[exec_write2_def, AllCaseEqs()] >> strip_tac >> gvs[]
QED

Theorem abi_decode_clean_exec_gas:
  exec_gas inst s = OK t ==>
  exec_gas inst (abi_decode_clean_allocas func s) =
    OK (abi_decode_clean_allocas func t)
Proof
  simp[exec_gas_def, abi_decode_clean_allocas_def, update_var_def,
       AllCaseEqs()] >> strip_tac >> gvs[]
QED

Theorem abi_decode_clean_exec_gas_reflect:
  exec_gas inst (abi_decode_clean_allocas func s) = OK u ==>
  ?t. exec_gas inst s = OK t /\ u = abi_decode_clean_allocas func t
Proof
  simp[exec_gas_def, abi_decode_clean_allocas_def, update_var_def,
       AllCaseEqs()] >> strip_tac >> gvs[]
QED

Theorem abi_decode_clean_exec_alloca_reflect:
  inst.inst_id IN abi_decode_alloca_ids func /\
  exec_alloca inst (abi_decode_clean_allocas func s) n = OK u ==>
  ?t. exec_alloca inst s n = OK t /\ u = abi_decode_clean_allocas func t
Proof
  strip_tac >>
  qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
  simp[exec_alloca_def, abi_decode_clean_lookup] >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id` >> simp[]
  >- (strip_tac >> gvs[abi_decode_clean_allocas_def, update_var_def,
                       DRESTRICT_FUPDATE]) >>
  Cases_on `x` >> strip_tac >>
  gvs[abi_decode_clean_allocas_def, update_var_def]
QED

Theorem abi_decode_clean_mstore[simp]:
  mstore off v (abi_decode_clean_allocas func s) =
  abi_decode_clean_allocas func (mstore off v s)
Proof
  simp[mstore_def, abi_decode_clean_allocas_def]
QED

Theorem abi_decode_clean_mstore8[simp]:
  mstore8 off v (abi_decode_clean_allocas func s) =
  abi_decode_clean_allocas func (mstore8 off v s)
Proof
  simp[mstore8_def, abi_decode_clean_allocas_def]
QED

Theorem abi_decode_clean_write_memory[simp]:
  write_memory_with_expansion off bytes (abi_decode_clean_allocas func s) =
  abi_decode_clean_allocas func (write_memory_with_expansion off bytes s)
Proof
  simp[write_memory_with_expansion_def, abi_decode_clean_allocas_def]
QED

Theorem abi_decode_clean_mcopy[simp]:
  mcopy dst src sz (abi_decode_clean_allocas func s) =
  abi_decode_clean_allocas func (mcopy dst src sz s)
Proof
  simp[mcopy_def, abi_decode_clean_allocas_def, write_memory_with_expansion_def]
QED

Theorem abi_decode_clean_istore[simp]:
  istore off v (abi_decode_clean_allocas func s) =
  abi_decode_clean_allocas func (istore off v s)
Proof
  simp[istore_def, mstore_def, abi_decode_clean_allocas_def]
QED

Theorem abi_decode_clean_sstore[simp]:
  sstore key v (abi_decode_clean_allocas func s) =
  abi_decode_clean_allocas func (sstore key v s)
Proof
  simp[sstore_def, abi_decode_clean_allocas_def]
QED

Theorem abi_decode_clean_tstore[simp]:
  tstore key v (abi_decode_clean_allocas func s) =
  abi_decode_clean_allocas func (tstore key v s)
Proof
  simp[tstore_def, abi_decode_clean_allocas_def]
QED

Theorem abi_decode_clean_call_request[simp]:
  venom_call_request (abi_decode_clean_allocas func s) addr v ao az st =
  venom_call_request s addr v ao az st
Proof
  simp[venom_call_request_def, read_memory_def, abi_decode_clean_allocas_def]
QED

Theorem abi_decode_clean_create_request[simp]:
  venom_create_request (abi_decode_clean_allocas func s) v off sz salt =
  venom_create_request s v off sz salt
Proof
  simp[venom_create_request_def, read_memory_def, abi_decode_clean_allocas_def]
QED

Theorem abi_decode_clean_consume_call:
  consume_call_outcome rq ro rs (abi_decode_clean_allocas func s) =
    (FST (consume_call_outcome rq ro rs s),
     abi_decode_clean_allocas func (SND (consume_call_outcome rq ro rs s)))
Proof
  simp[abi_decode_clean_allocas_def, write_memory_with_expansion_def]
QED

Theorem abi_decode_clean_consume_create:
  consume_create_outcome rq (abi_decode_clean_allocas func s) =
    (FST (consume_create_outcome rq s),
     abi_decode_clean_allocas func (SND (consume_create_outcome rq s)))
Proof
  simp[abi_decode_clean_allocas_def]
QED

Theorem abi_decode_clean_exec_ext_call_iff:
  exec_ext_call inst (abi_decode_clean_allocas func s) gas addr v ao az ro rz st = OK u <=>
  ?t. exec_ext_call inst s gas addr v ao az ro rz st = OK t /\
      u = abi_decode_clean_allocas func t
Proof
  Cases_on `consume_call_outcome (venom_call_request s addr v ao az st)
              (w2n ro) (w2n rz) s` >>
  simp[exec_ext_call_def, abi_decode_clean_consume_call,
       Excl "consume_call_outcome_eq", AllCaseEqs()] >>
  metis_tac[]
QED

Theorem abi_decode_clean_exec_create_iff:
  exec_create inst (abi_decode_clean_allocas func s) v off sz salt = OK u <=>
  ?t. exec_create inst s v off sz salt = OK t /\
      u = abi_decode_clean_allocas func t
Proof
  Cases_on `consume_create_outcome (venom_create_request s v off sz salt) s` >>
  simp[exec_create_def, abi_decode_clean_consume_create,
       Excl "consume_create_outcome_eq", AllCaseEqs()] >>
  metis_tac[]
QED

Theorem abi_decode_clean_delegate_state[simp]:
  make_venom_delegatecall_state (abi_decode_clean_allocas func s)
    target gas calldata code st =
  make_venom_delegatecall_state s target gas calldata code st
Proof
  simp[make_venom_delegatecall_state_def, venom_to_tx_params_def,
       abi_decode_clean_allocas_def]
QED

Theorem abi_decode_clean_extract_result:
  extract_venom_result (abi_decode_clean_allocas func s) output ro rz result =
  OPTION_MAP (\(v,t). (v, abi_decode_clean_allocas func t))
    (extract_venom_result s output ro rz result)
Proof
  Cases_on `result` >- simp[extract_venom_result_def] >>
  PairCases_on `x` >>
  Cases_on `x1.contexts` >- simp[extract_venom_result_def] >>
  Cases_on `t` >> simp[extract_venom_result_def] >>
  PairCases_on `h` >>
  Cases_on `x0`
  >- simp[abi_decode_clean_allocas_def, venom_state_component_equality] >>
  simp[] >> rename1 `case r of NONE => _ | SOME _ => _` >>
  Cases_on `r` >>
  simp[abi_decode_clean_allocas_def, venom_state_component_equality]
QED

Theorem abi_decode_clean_exec_delegatecall_iff:
  exec_delegatecall inst (abi_decode_clean_allocas func s) gas addr ao az ro rz = OK u <=>
  ?t. exec_delegatecall inst s gas addr ao az ro rz = OK t /\
      u = abi_decode_clean_allocas func t
Proof
  simp[exec_delegatecall_def, read_memory_def, abi_decode_clean_allocas_def,
       update_var_def, AllCaseEqs(), PULL_EXISTS] >>
  eq_tac >> strip_tac >> gvs[]
QED

Theorem abi_decode_clean_logs_update[simp]:
  (abi_decode_clean_allocas func s) with vs_logs := logs =
  abi_decode_clean_allocas func (s with vs_logs := logs)
Proof
  simp[abi_decode_clean_allocas_def]
QED

Theorem abi_decode_clean_jump[simp]:
  jump_to lbl (abi_decode_clean_allocas func s) =
  abi_decode_clean_allocas func (jump_to lbl s)
Proof
  simp[jump_to_def, abi_decode_clean_allocas_def]
QED

Theorem abi_decode_clean_fmp_update[simp]:
  (abi_decode_clean_allocas func s) with vs_fmp := v =
  abi_decode_clean_allocas func (s with vs_fmp := v)
Proof
  simp[abi_decode_clean_allocas_def]
QED

Theorem abi_decode_clean_dispatch_fields[simp]:
  (abi_decode_clean_allocas func s).vs_call_ctx = s.vs_call_ctx /\
  (abi_decode_clean_allocas func s).vs_tx_ctx = s.vs_tx_ctx /\
  (abi_decode_clean_allocas func s).vs_block_ctx = s.vs_block_ctx /\
  (abi_decode_clean_allocas func s).vs_accounts = s.vs_accounts /\
  (abi_decode_clean_allocas func s).vs_code = s.vs_code /\
  (abi_decode_clean_allocas func s).vs_data_section = s.vs_data_section /\
  (abi_decode_clean_allocas func s).vs_params = s.vs_params /\
  (abi_decode_clean_allocas func s).vs_fmp = s.vs_fmp /\
  (abi_decode_clean_allocas func s).vs_initial_fmp = s.vs_initial_fmp /\
  (abi_decode_clean_allocas func s).vs_return_pc_token = s.vs_return_pc_token /\
  (abi_decode_clean_allocas func s).vs_logs = s.vs_logs /\
  (abi_decode_clean_allocas func s).vs_returndata = s.vs_returndata
Proof
  simp[abi_decode_clean_allocas_def]
QED

Theorem abi_decode_clean_read0_iff:
  (!s. f (abi_decode_clean_allocas func s) = f s) ==>
  (exec_read0 f inst (abi_decode_clean_allocas func s) = OK u <=>
   ?t. exec_read0 f inst s = OK t /\ u = abi_decode_clean_allocas func t)
Proof
  metis_tac[abi_decode_clean_exec_read0, abi_decode_clean_exec_read0_reflect]
QED

Theorem abi_decode_clean_read1_iff:
  (!v s. f v (abi_decode_clean_allocas func s) = f v s) ==>
  (exec_read1 f inst (abi_decode_clean_allocas func s) = OK u <=>
   ?t. exec_read1 f inst s = OK t /\ u = abi_decode_clean_allocas func t)
Proof
  metis_tac[abi_decode_clean_exec_read1, abi_decode_clean_exec_read1_reflect]
QED

Theorem abi_decode_clean_write2_iff:
  (!a b s. f a b (abi_decode_clean_allocas func s) =
           abi_decode_clean_allocas func (f a b s)) ==>
  (exec_write2 f inst (abi_decode_clean_allocas func s) = OK u <=>
   ?t. exec_write2 f inst s = OK t /\ u = abi_decode_clean_allocas func t)
Proof
  metis_tac[abi_decode_clean_exec_write2, abi_decode_clean_exec_write2_reflect]
QED

(* Successful base-step transport is an image relation, not injectivity. *)
Theorem abi_decode_clean_step_base_OK:
  (inst.inst_opcode = ALLOCA ==> inst.inst_id IN abi_decode_alloca_ids func) ==>
  (step_inst_base inst (abi_decode_clean_allocas func s) = OK u <=>
   ?t. step_inst_base inst s = OK t /\ u = abi_decode_clean_allocas func t)
Proof
  strip_tac >> Cases_on `inst.inst_opcode`
  >- (simp[step_inst_base_opcode_eqs] >> metis_tac[abi_decode_clean_exec_pure2, abi_decode_clean_exec_pure2_reflect])
  >- (simp[step_inst_base_opcode_eqs] >> metis_tac[abi_decode_clean_exec_pure2, abi_decode_clean_exec_pure2_reflect])
  >- (simp[step_inst_base_opcode_eqs] >> metis_tac[abi_decode_clean_exec_pure2, abi_decode_clean_exec_pure2_reflect])
  >- (simp[step_inst_base_opcode_eqs] >> metis_tac[abi_decode_clean_exec_pure2, abi_decode_clean_exec_pure2_reflect])
  >- (simp[step_inst_base_opcode_eqs] >> metis_tac[abi_decode_clean_exec_pure2, abi_decode_clean_exec_pure2_reflect])
  >- (simp[step_inst_base_opcode_eqs] >> metis_tac[abi_decode_clean_exec_pure2, abi_decode_clean_exec_pure2_reflect])
  >- (simp[step_inst_base_opcode_eqs] >> metis_tac[abi_decode_clean_exec_pure2, abi_decode_clean_exec_pure2_reflect])
  >- (simp[step_inst_base_opcode_eqs] >> metis_tac[abi_decode_clean_exec_pure2, abi_decode_clean_exec_pure2_reflect])
  >- (simp[step_inst_base_opcode_eqs] >> metis_tac[abi_decode_clean_exec_pure3, abi_decode_clean_exec_pure3_reflect])
  >- (simp[step_inst_base_opcode_eqs] >> metis_tac[abi_decode_clean_exec_pure3, abi_decode_clean_exec_pure3_reflect])
  >- (simp[step_inst_base_opcode_eqs] >> metis_tac[abi_decode_clean_exec_pure2, abi_decode_clean_exec_pure2_reflect])
  >- (simp[step_inst_base_opcode_eqs] >> metis_tac[abi_decode_clean_exec_pure2, abi_decode_clean_exec_pure2_reflect])
  >- (simp[step_inst_base_opcode_eqs] >> metis_tac[abi_decode_clean_exec_pure2, abi_decode_clean_exec_pure2_reflect])
  >- (simp[step_inst_base_opcode_eqs] >> metis_tac[abi_decode_clean_exec_pure2, abi_decode_clean_exec_pure2_reflect])
  >- (simp[step_inst_base_opcode_eqs] >> metis_tac[abi_decode_clean_exec_pure2, abi_decode_clean_exec_pure2_reflect])
  >- (simp[step_inst_base_opcode_eqs] >> metis_tac[abi_decode_clean_exec_pure1, abi_decode_clean_exec_pure1_reflect])
  >- (simp[step_inst_base_opcode_eqs] >> metis_tac[abi_decode_clean_exec_pure2, abi_decode_clean_exec_pure2_reflect])
  >- (simp[step_inst_base_opcode_eqs] >> metis_tac[abi_decode_clean_exec_pure2, abi_decode_clean_exec_pure2_reflect])
  >- (simp[step_inst_base_opcode_eqs] >> metis_tac[abi_decode_clean_exec_pure2, abi_decode_clean_exec_pure2_reflect])
  >- (simp[step_inst_base_opcode_eqs] >> metis_tac[abi_decode_clean_exec_pure1, abi_decode_clean_exec_pure1_reflect])
  >- (simp[step_inst_base_opcode_eqs] >> metis_tac[abi_decode_clean_exec_pure2, abi_decode_clean_exec_pure2_reflect])
  >- (simp[step_inst_base_opcode_eqs] >> metis_tac[abi_decode_clean_exec_pure2, abi_decode_clean_exec_pure2_reflect])
  >- (simp[step_inst_base_opcode_eqs] >> metis_tac[abi_decode_clean_exec_pure2, abi_decode_clean_exec_pure2_reflect])
  >- (simp[step_inst_base_opcode_eqs] >> metis_tac[abi_decode_clean_exec_pure2, abi_decode_clean_exec_pure2_reflect])
  >- (simp[step_inst_base_opcode_eqs] >> metis_tac[abi_decode_clean_exec_pure2, abi_decode_clean_exec_pure2_reflect])
  >- (simp[step_inst_base_opcode_eqs] >> irule abi_decode_clean_read1_iff >> simp[mload_def, abi_decode_clean_allocas_def])
  >- simp[step_inst_base_opcode_eqs, abi_decode_clean_write2_iff]
  >- simp[step_inst_base_opcode_eqs, abi_decode_clean_write2_iff]
  >- (simp[step_inst_base_opcode_eqs, AllCaseEqs()] >> metis_tac[abi_decode_clean_mcopy])
  >- simp[step_inst_base_opcode_eqs, abi_decode_clean_read0_iff]
  >- (simp[step_inst_base_opcode_eqs] >> irule abi_decode_clean_read1_iff >> simp[sload_def, contract_storage_def, abi_decode_clean_allocas_def])
  >- (simp[step_inst_base_opcode_eqs, AllCaseEqs(), abi_decode_clean_write2_iff] >> metis_tac[])
  >- (simp[step_inst_base_opcode_eqs] >> irule abi_decode_clean_read1_iff >> simp[tload_def, contract_transient_def, abi_decode_clean_allocas_def])
  >- (simp[step_inst_base_opcode_eqs, AllCaseEqs(), abi_decode_clean_write2_iff] >> metis_tac[])
  >- (simp[step_inst_base_opcode_eqs] >> irule abi_decode_clean_read1_iff >> simp[mload_def, abi_decode_clean_allocas_def])
  >- (simp[step_inst_base_opcode_eqs, AllCaseEqs()] >> metis_tac[abi_decode_clean_istore])
  >- (simp[step_inst_base_opcode_eqs, AllCaseEqs()] >> metis_tac[])
  >- (simp[step_inst_base_opcode_eqs, AllCaseEqs()] >> metis_tac[])
  >- (simp[step_inst_base_opcode_eqs, AllCaseEqs()] >> metis_tac[])
  >- simp[step_inst_base_opcode_eqs, AllCaseEqs()]
  >- simp[step_inst_base_opcode_eqs, AllCaseEqs()]
  >- simp[step_inst_base_opcode_eqs, AllCaseEqs()]
  >- simp[step_inst_base_opcode_eqs]
  >- simp[step_inst_base_opcode_eqs]
  >- simp[step_inst_base_opcode_eqs]
  >- (simp[step_inst_base_opcode_eqs, AllCaseEqs()] >> metis_tac[])
  >- (simp[step_inst_base_opcode_eqs, AllCaseEqs()] >> metis_tac[])
  >- (simp[step_inst_base_opcode_eqs] >> metis_tac[])
  >- (fs[] >> simp[step_inst_base_opcode_eqs, AllCaseEqs()] >> metis_tac[abi_decode_clean_exec_alloca, abi_decode_clean_exec_alloca_reflect])
  >- (simp[step_inst_base_opcode_eqs, AllCaseEqs()] >> metis_tac[])
  >- (simp[step_inst_base_opcode_eqs, AllCaseEqs()] >>
      CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >> simp[] )
  >- (simp[step_inst_base_opcode_eqs, AllCaseEqs()] >> metis_tac[])
  >- (simp[step_inst_base_opcode_eqs, AllCaseEqs()] >> metis_tac[])
  >- simp[step_inst_base_opcode_eqs, AllCaseEqs()]
  >- (simp[step_inst_base_opcode_eqs, AllCaseEqs()] >> metis_tac[])
  >- (simp[step_inst_base_opcode_eqs, AllCaseEqs()] >> metis_tac[])
  >- simp[step_inst_base_opcode_eqs, AllCaseEqs()]
  >- (simp[step_inst_base_opcode_eqs, AllCaseEqs()] >> metis_tac[])
  >- (simp[step_inst_base_opcode_eqs, AllCaseEqs()] >> metis_tac[])
  >- simp[step_inst_base_opcode_eqs, abi_decode_clean_read0_iff]
  >- simp[step_inst_base_opcode_eqs, abi_decode_clean_read0_iff]
  >- simp[step_inst_base_opcode_eqs, abi_decode_clean_read1_iff]
  >- simp[step_inst_base_opcode_eqs, abi_decode_clean_read0_iff]
  >- (simp[step_inst_base_opcode_eqs, AllCaseEqs()] >> metis_tac[abi_decode_clean_write_memory])
  >- simp[step_inst_base_opcode_eqs, abi_decode_clean_read0_iff]
  >- simp[step_inst_base_opcode_eqs, abi_decode_clean_read0_iff]
  >- simp[step_inst_base_opcode_eqs, abi_decode_clean_read0_iff]
  >- (simp[step_inst_base_opcode_eqs] >> metis_tac[abi_decode_clean_exec_gas, abi_decode_clean_exec_gas_reflect])
  >- simp[step_inst_base_opcode_eqs, abi_decode_clean_read0_iff]
  >- simp[step_inst_base_opcode_eqs, abi_decode_clean_read0_iff]
  >- simp[step_inst_base_opcode_eqs, abi_decode_clean_read0_iff]
  >- simp[step_inst_base_opcode_eqs, abi_decode_clean_read0_iff]
  >- simp[step_inst_base_opcode_eqs, abi_decode_clean_read0_iff]
  >- simp[step_inst_base_opcode_eqs, abi_decode_clean_read0_iff]
  >- simp[step_inst_base_opcode_eqs, abi_decode_clean_read0_iff]
  >- simp[step_inst_base_opcode_eqs, abi_decode_clean_read1_iff]
  >- simp[step_inst_base_opcode_eqs, abi_decode_clean_read1_iff]
  >- simp[step_inst_base_opcode_eqs, abi_decode_clean_read0_iff]
  >- simp[step_inst_base_opcode_eqs, abi_decode_clean_read0_iff]
  >- (simp[step_inst_base_opcode_eqs, AllCaseEqs()] >> metis_tac[abi_decode_clean_write_memory])
  >- simp[step_inst_base_opcode_eqs, abi_decode_clean_read1_iff]
  >- simp[step_inst_base_opcode_eqs, abi_decode_clean_read1_iff]
  >- (simp[step_inst_base_opcode_eqs, AllCaseEqs()] >> metis_tac[abi_decode_clean_write_memory])
  >- simp[step_inst_base_opcode_eqs, abi_decode_clean_read0_iff]
  >- (simp[step_inst_base_opcode_eqs, AllCaseEqs()] >> metis_tac[abi_decode_clean_write_memory])
  >- simp[step_inst_base_opcode_eqs, abi_decode_clean_read1_iff]
  >- simp[step_inst_base_opcode_eqs, abi_decode_clean_read0_iff]
  >- (simp[step_inst_base_opcode_eqs, AllCaseEqs()] >> metis_tac[])
  >- (simp[step_inst_base_opcode_eqs, AllCaseEqs(), abi_decode_clean_exec_ext_call_iff] >> eq_tac >> strip_tac >> gvs[] >> metis_tac[])
  >- (simp[step_inst_base_opcode_eqs, AllCaseEqs(), abi_decode_clean_exec_ext_call_iff] >> eq_tac >> strip_tac >> gvs[] >> metis_tac[])
  >- (simp[step_inst_base_opcode_eqs, AllCaseEqs(), abi_decode_clean_exec_delegatecall_iff] >> metis_tac[])
  >- (simp[step_inst_base_opcode_eqs, AllCaseEqs(), abi_decode_clean_exec_create_iff] >> metis_tac[])
  >- (simp[step_inst_base_opcode_eqs, AllCaseEqs(), abi_decode_clean_exec_create_iff] >> metis_tac[])
  >- (simp[step_inst_base_opcode_eqs, AllCaseEqs()] >> eq_tac >> strip_tac >> gvs[] >> metis_tac[])
  >- simp[step_inst_base_opcode_eqs, AllCaseEqs()]
  >- simp[step_inst_base_opcode_eqs]
  >- (simp[step_inst_base_opcode_eqs, AllCaseEqs()] >> metis_tac[])
  >- (simp[step_inst_base_opcode_eqs, AllCaseEqs()] >> metis_tac[])
  >- simp[step_inst_base_opcode_eqs, abi_decode_clean_read1_iff]
  >- (simp[step_inst_base_opcode_eqs, AllCaseEqs()] >> metis_tac[abi_decode_clean_write_memory])
  >> simp[step_inst_base_opcode_eqs] >> metis_tac[abi_decode_clean_exec_pure2, abi_decode_clean_exec_pure2_reflect]
QED

Theorem abi_decode_clean_step_base:
  (inst.inst_opcode = ALLOCA ==> inst.inst_id IN abi_decode_alloca_ids func) /\
  step_inst_base inst s = OK t ==>
  step_inst_base inst (abi_decode_clean_allocas func s) =
    OK (abi_decode_clean_allocas func t)
Proof
  metis_tac[abi_decode_clean_step_base_OK]
QED

Theorem abi_decode_clean_step_base_reflect:
  (inst.inst_opcode = ALLOCA ==> inst.inst_id IN abi_decode_alloca_ids func) /\
  step_inst_base inst (abi_decode_clean_allocas func s) = OK u ==>
  ?t. step_inst_base inst s = OK t /\ u = abi_decode_clean_allocas func t
Proof
  metis_tac[abi_decode_clean_step_base_OK]
QED
