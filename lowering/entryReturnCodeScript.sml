Theory entryReturnCode
Ancestors
  entryCodePredicate entryContextCodePredicate entryTypedCopyCode entryEncoderCode
  stmtLowering context compileEnv

Theorem entry_code_load_tuple_elements:
  !tys offset. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_load_tuple_elements cenv base_op tys offset)
Proof
  Induct >> simp[compile_load_tuple_elements_def, entry_code_return] >>
  rpt gen_tac >>
  rpt (irule entry_code_bind >>
    simp[entry_code_emit_op, entry_code_return] >> rpt gen_tac)
QED

Theorem entry_code_mcopy_guard:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA) action ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_mcopy_guard cenv action)
Proof
  Cases_on `cenv.ce_target CapMcopy` >>
  simp[compile_mcopy_guard_def, entry_code_emit_inst]
QED

Theorem entry_code_nonreentrant_unlock:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_nonreentrant_unlock nkey ut iv)
Proof
  Cases_on `iv` >> Cases_on `ut` >>
  simp[compile_nonreentrant_unlock_def, entry_code_return, entry_code_emit_void]
QED

Theorem entry_code_internal_return:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_internal_return cenv rv rpc rcount rt src_ty elems rb)
Proof
  Cases_on `0 < rcount` >> Cases_on `rv` >> Cases_on `rb` >>
  simp[compile_internal_return_def, entry_code_emit_inst, comp_ignore_bind_def] >>
  Cases_on `elems = []` >> simp[entry_code_emit_inst] >>
  irule entry_code_bind >>
  simp[entry_code_emit_inst, entry_code_load_tuple_elements, entry_code_store_memory]
QED

Theorem entry_code_internal_return_from_env:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_internal_return_from_env cenv ty src_ty val_op rpc)
Proof
  simp[compile_internal_return_from_env_def] >> irule entry_code_bind >>
  conj_tac
  >- (rpt gen_tac >> BETA_TAC >> irule entry_code_bind >>
      simp[entry_code_return, entry_code_internal_return]) >>
  Cases_on `cenv.ce_return_buf` >> simp[entry_code_return] >>
  Cases_on `x` >> simp[entry_code_return] >>
  irule entry_code_bind >> simp[entry_code_emit_op, entry_code_return]
QED

Theorem entry_code_external_return:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_external_return rv prim raw info max_size nr nkey ut iv)
Proof
  simp[compile_external_return_def, comp_ignore_bind_def] >>
  irule entry_code_bind >> reverse conj_tac
  >- (Cases_on `nr` >> simp[entry_code_return, entry_code_nonreentrant_unlock]) >>
  rpt gen_tac >> Cases_on `rv` >> simp[entry_code_emit_inst] >>
  Cases_on `raw` >> Cases_on `prim` >> simp[] >>
  rpt (irule entry_code_bind >>
    simp[entry_code_emit_op, entry_code_emit_void, entry_code_emit_inst,
         entry_code_return, entry_code_alloc_buffer, entry_code_encode_to_buf] >>
    rpt gen_tac)
QED
