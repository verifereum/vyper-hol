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
