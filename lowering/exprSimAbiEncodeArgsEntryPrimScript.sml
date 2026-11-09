Theory exprSimAbiEncodeArgsEntryPrim
Ancestors
  exprSimAbiEncodeArgsEntry compileEnv context emitHelper

Definition abi_args_entry_safe_def:
  abi_args_entry_safe si sf <=>
    si.cs_current_insts = [] ==>
    (abi_args_entry_emitted si sf \/
     (sf.cs_current_bb = si.cs_current_bb /\ sf.cs_current_insts = [] /\
      sf.cs_blocks = si.cs_blocks))
End

Theorem abi_args_entry_safe_refl[simp]:
  abi_args_entry_safe si si
Proof
  simp[abi_args_entry_safe_def]
QED

Theorem abi_args_entry_emitted_code_eq:
  si.cs_current_bb = sm.cs_current_bb /\ si.cs_blocks = sm.cs_blocks ==>
  (abi_args_entry_emitted si sf <=> abi_args_entry_emitted sm sf)
Proof
  simp[abi_args_entry_emitted_def, fragExecTheory.emitted_blocks_def]
QED

Theorem abi_args_entry_safe_trans:
  abi_args_entry_safe si sm /\ abi_args_entry_safe sm sf /\
  cs_extends si sm /\ cs_extends sm sf ==>
  abi_args_entry_safe si sf
Proof
  rw[abi_args_entry_safe_def] >>
  metis_tac[abi_args_entry_emitted_mono, abi_args_entry_emitted_code_eq]
QED

Theorem abi_args_entry_emit_inst:
  si.cs_current_insts = [] /\ emit_inst op args outs si = (r,sf) /\ op <> PHI ==>
  abi_args_entry_emitted si sf
Proof
  simp[emit_inst_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rw[] >> simp[abi_args_entry_emitted_def, venomInstTheory.mk_inst_def]
QED

Theorem abi_args_entry_safe_emit_inst:
  emit_inst op args outs si = (r,sf) /\ op <> PHI ==>
  abi_args_entry_safe si sf
Proof
  metis_tac[abi_args_entry_safe_def, abi_args_entry_emit_inst]
QED

Theorem abi_args_entry_safe_fresh_var:
  fresh_var si = (r,sf) ==> abi_args_entry_safe si sf
Proof
  simp[fresh_var_def] >> rw[] >> simp[abi_args_entry_safe_def]
QED

Theorem abi_args_entry_safe_fresh_label:
  fresh_label suffix si = (r,sf) ==> abi_args_entry_safe si sf
Proof
  simp[fresh_label_def] >> rw[] >> simp[abi_args_entry_safe_def]
QED

Theorem abi_args_entry_safe_alloc_buffer:
  compile_alloc_buffer sz si = (r,sf) ==> abi_args_entry_safe si sf
Proof
  simp[compile_alloc_buffer_def, emit_op_def, emit_inst_def,
       fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rw[] >> simp[abi_args_entry_safe_def, abi_args_entry_emitted_def,
              venomInstTheory.mk_inst_def]
QED

Theorem abi_args_entry_emit_new_block:
  si.cs_current_insts = [] /\ emit_inst op args outs si = (r,sm) /\
  op <> PHI /\ new_block label sm = (old,sf) ==>
  abi_args_entry_emitted si sf
Proof
  simp[emit_inst_def, fresh_id_def, emit_def, new_block_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rw[] >> simp[abi_args_entry_emitted_def, fragExecTheory.emitted_blocks_def,
              venomInstTheory.mk_inst_def]
QED
