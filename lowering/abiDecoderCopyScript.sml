(* Snapshot-copy preservation used by bytestring and bulk-array decoding. *)
Theory abiDecoderCopy
Ancestors
  abiDecoderComposition abiDecoderContract emitHelperProps exprLoweringProps
  venomExecSemantics venomInst venomState compileEnv valueEncoding emitHelper

Theorem abi_decode_copy_vars:
  emit_void (abi_decode_copy_opcode opc) [dst;src;sz] st = ((),st') /\
  abi_decode_source_opcode opc /\
  run_inst_seq (emitted_insts st st') s = OK t ==>
  t.vs_vars = s.vs_vars
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  gvs[abi_decode_source_opcode_def, abi_decode_copy_opcode_def] >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  simp[run_inst_seq_def] >>
  simp[step_inst_base_opcode_eqs, mk_inst_def] >>
  simp[mcopy_def, write_memory_with_expansion_def, AllCaseEqs()] >>
  strip_tac >> gvs[]
QED

Theorem abi_decode_copy_fresh:
  emit_void (abi_decode_copy_opcode opc) [dst;src;sz] st = ((),st') /\
  abi_decode_source_opcode opc /\
  run_inst_seq (emitted_insts st st') s = OK t /\ fresh_vars_wrt st s ==>
  fresh_vars_wrt st' t
Proof
  strip_tac >> drule_all abi_decode_copy_vars >> strip_tac >>
  drule_all fresh_vars_wrt_emit_void >>
  simp[fresh_vars_wrt_def, lookup_var_def]
QED
