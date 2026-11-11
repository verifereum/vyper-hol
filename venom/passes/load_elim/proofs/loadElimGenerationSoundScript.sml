Theory loadElimGenerationSound
Ancestors
  loadElimAbsoluteKey loadElimKeyReadOperational loadElimKeyRead
  venomExecSemantics venomState venomMemProps venomMemDefs
  loadElimDefs finite_map words memLocDefs basePtrDefs vfmState

Theorem le_generating_load_state:
  MEM (inst.inst_opcode,space)
    [(MLOAD,AddrSp_Memory); (SLOAD,AddrSp_Storage);
     (TLOAD,AddrSp_Transient); (CALLDATALOAD,AddrSp_Calldata);
     (DLOAD,AddrSp_Data)] /\
  inst.inst_operands = [addr] /\ inst.inst_outputs = [out] /\
  eval_operand addr s = SOME w /\
  step_inst fuel ctx inst s = OK t ==>
  ?v. le_read_address space (w2n w) s = SOME v /\
      t = update_var out v s
Proof
  simp[] >> strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[Once step_inst_def] >>
  simp[step_inst_base_opcode_eqs, exec_read1_def] >>
  strip_tac >> gvs[]
QED

Theorem le_absolute_key_update_var:
  le_absolute_key space key /\
  (!v. key = LK_Op (Var v) ==> v <> out) ==>
  le_key_address space key (update_var out value s) =
  le_key_address space key s
Proof
  Cases_on `key`
  >- (rename1 `LK_Op op` >> Cases_on `op` >>
      simp[le_key_address_def, eval_operand_def, lookup_var_def,
           update_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  simp[le_absolute_key_def] >> strip_tac >>
  simp[le_key_address_def, memloc_runtime_region_def]
QED

Theorem le_read_address_update_var[simp]:
  le_read_address space a (update_var out value s) = le_read_address space a s
Proof
  Cases_on `space` >>
  simp[le_read_address_def, update_var_def, mload_def, sload_def, tload_def,
       read_memory_def, contract_storage_def, contract_transient_def]
QED

Theorem le_generating_load_key:
  MEM (inst.inst_opcode,space)
    [(MLOAD,AddrSp_Memory); (SLOAD,AddrSp_Storage);
     (TLOAD,AddrSp_Transient); (CALLDATALOAD,AddrSp_Calldata);
     (DLOAD,AddrSp_Data)] /\
  (!v. bp_get_ptrs bp v = []) /\
  inst.inst_operands = [addr] /\ inst.inst_outputs = [out] /\
  eval_operand addr s = SOME w /\ eval_operand (norm addr) s = SOME w /\
  (!v. load_get_read_key bp space norm inst = LK_Op (Var v) ==> v <> out) /\
  step_inst fuel ctx inst s = OK t ==>
  le_key_read space (load_get_read_key bp space norm inst) t = lookup_var out t
Proof
  strip_tac >>
  `le_key_address space (load_get_read_key bp space norm inst) s = SOME (w2n w)` by
    (Cases_on `inst.inst_opcode = DLOAD`
     >- (gvs[] >> drule_all le_dload_key_address >> simp[]) >>
     irule le_empty_read_key_address >> gvs[]) >>
  `le_absolute_key space (load_get_read_key bp space norm inst)` by
    (Cases_on `inst.inst_opcode = DLOAD`
     >- (gvs[] >> simp[le_dload_key_shape]) >>
     irule le_empty_read_key_shape >> gvs[] >> qexists `addr` >> simp[]) >>
  drule_all le_generating_load_state >> strip_tac >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  `le_key_address space (load_get_read_key bp space norm inst)
      (update_var out v s) = le_key_address space (load_get_read_key bp space norm inst) s` by
    (irule le_absolute_key_update_var >> metis_tac[]) >>
  simp[le_key_read_def] >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem le_generating_store_state:
  MEM (inst.inst_opcode,space)
    [(MSTORE,AddrSp_Memory); (SSTORE,AddrSp_Storage); (TSTORE,AddrSp_Transient)] /\
  inst.inst_operands = [addr;value] /\
  eval_operand addr s = SOME w /\
  step_inst fuel ctx inst s = OK t ==>
  t.vs_vars = s.vs_vars /\ t.vs_labels = s.vs_labels /\
  ?v. eval_operand value s = SOME v /\
      le_read_address space (w2n w) t = SOME v
Proof
  simp[] >> strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[Once step_inst_def] >>
  simp[step_inst_base_opcode_eqs, exec_write2_def] >>
  gvs[AllCaseEqs()] >> strip_tac >> gvs[] >>
  simp[mload_mstore_same, mstore_def, sstore_def, tstore_def,
       sload_def, tload_def, contract_storage_def, contract_transient_def,
       lookup_storage_def, update_storage_def, lookup_account_def,
       combinTheory.APPLY_UPDATE_THM]
QED

Theorem le_absolute_key_same_bindings:
  le_absolute_key space key /\ t.vs_vars = s.vs_vars /\
  t.vs_labels = s.vs_labels ==>
  le_key_address space key t = le_key_address space key s
Proof
  Cases_on `key`
  >- (rename1 `LK_Op op` >> Cases_on `op` >>
      simp[le_key_address_def, eval_operand_def, lookup_var_def]) >>
  metis_tac[le_absolute_location_address]
QED

Theorem le_generating_store_key:
  MEM (inst.inst_opcode,space)
    [(MSTORE,AddrSp_Memory); (SSTORE,AddrSp_Storage); (TSTORE,AddrSp_Transient)] /\
  (!v. bp_get_ptrs bp v = []) /\
  inst.inst_operands = [addr;value] /\
  eval_operand addr s = SOME w /\ eval_operand (norm addr) s = SOME w /\
  step_inst fuel ctx inst s = OK t ==>
  le_key_read space (load_get_write_key bp space norm inst) t = eval_operand value t
Proof
  strip_tac >>
  `le_key_address space (load_get_write_key bp space norm inst) s = SOME (w2n w)` by
    (irule le_empty_write_key_address >> simp[] >> metis_tac[]) >>
  `le_absolute_key space (load_get_write_key bp space norm inst)` by
    (irule le_empty_write_key_shape >> simp[] >> metis_tac[]) >>
  drule_all le_generating_store_state >> strip_tac >>
  `le_key_address space (load_get_write_key bp space norm inst) t =
   le_key_address space (load_get_write_key bp space norm inst) s` by
    (irule le_absolute_key_same_bindings >> simp[]) >>
  `eval_operand value t = eval_operand value s` by
    (Cases_on `value` >> gvs[eval_operand_def, lookup_var_def]) >>
  simp[le_key_read_def]
QED
