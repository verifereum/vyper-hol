Theory exprSimAbiDecodeAllocaEraseExec
Ancestors
  exprSimAbiDecodeAllocaErase venomExecSemantics venomState finite_map pred_set

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
