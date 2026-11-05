(* Opcode observations of the scalar encoder, independent of byte correctness. *)
Theory stmtSimLogEncodeFields
Ancestors
  stmtSimLogExecFields stmtSimLogEncodeLayout abiEncoderBytesCode
  abiEncoderMemberPhaseEffect abiEncoderComplexPrefix abiEncoderMemberCode
  abiEncoderChildCode abiEncoderChildSuffix abiDecoderArrayInit
  abiEncoderComplexCode abiEncoder emitHelperProps exprLoweringProps
  compileEnv emitHelper context venomInst words list rich_list arithmetic

Theorem log_encode_copy_safe:
  compile_abi_encode_to_buf dst src (AbiCopy n) st = (out,final) ==>
  inst_extends st final /\ same_blocks st final /\
  EVERY (\i. log_encode_safe_opcode i.inst_opcode) (emitted_insts st final)
Proof
  cheat
QED

Theorem log_encode_bytes_safe[local]:
  compile_abi_encode_to_buf dst src (AbiBytestring n) st = (out,final) ==>
  inst_extends st final /\ same_blocks st final /\
  EVERY (\i. log_encode_safe_opcode i.inst_opcode) (emitted_insts st final)
Proof
  cheat
QED

Theorem log_encode_scalar_safe[local]:
  compile_abi_encode_to_buf dst src ei st = (out,final) /\ log_scalar_enc_info ei ==>
  inst_extends st final /\ same_blocks st final /\
  EVERY (\i. log_encode_safe_opcode i.inst_opcode) (emitted_insts st final)
Proof
  cheat
QED

Theorem log_encode_safe_append:
  inst_extends st mid /\ inst_extends mid final /\
  same_blocks st mid /\ same_blocks mid final /\
  EVERY (\i. log_encode_safe_opcode i.inst_opcode) (emitted_insts st mid) /\
  EVERY (\i. log_encode_safe_opcode i.inst_opcode) (emitted_insts mid final) ==>
  inst_extends st final /\ same_blocks st final /\
  EVERY (\i. log_encode_safe_opcode i.inst_opcode) (emitted_insts st final)
Proof
  cheat
QED

Theorem log_encode_emit_safe:
  emit_op opc ops st = (out,final) /\ log_encode_safe_opcode opc ==>
  inst_extends st final /\ same_blocks st final /\
  EVERY (\i. log_encode_safe_opcode i.inst_opcode) (emitted_insts st final)
Proof
  cheat
QED

Theorem log_encode_child_prefix_safe[local]:
  abi_encode_child_prefix dst ho dp st = (ops,final) ==>
  inst_extends st final /\ same_blocks st final /\
  EVERY (\i. log_encode_safe_opcode i.inst_opcode) (emitted_insts st final)
Proof
  cheat
QED

Theorem log_encode_child_suffix_safe[local]:
  abi_encode_child_suffix head dp offset len st = (out,final) ==>
  inst_extends st final /\ same_blocks st final /\
  EVERY (\i. log_encode_safe_opcode i.inst_opcode) (emitted_insts st final)
Proof
  cheat
QED

Theorem log_encode_child_safe[local]:
  compile_abi_encode_child dst src ei dyn ho dp st = (out,final) /\
  log_scalar_enc_info ei ==>
  inst_extends st final /\ same_blocks st final /\
  EVERY (\i. log_encode_safe_opcode i.inst_opcode) (emitted_insts st final)
Proof
  cheat
QED

Theorem log_encode_members_safe[local]:
  !infos dst src so ho dp st out final.
  compile_abi_encode_complex_elems dst src infos so ho dp st = (out,final) /\
  EVERY (\(ei,asz,mz,dyn). log_scalar_enc_info ei) infos ==>
  inst_extends st final /\ same_blocks st final /\
  EVERY (\i. log_encode_safe_opcode i.inst_opcode) (emitted_insts st final)
Proof
  cheat
QED

Theorem log_encode_cursor_safe[local]:
  abi_encode_complex_prefix infos st = (dp,final) ==>
  inst_extends st final /\ same_blocks st final /\
  EVERY (\i. log_encode_safe_opcode i.inst_opcode) (emitted_insts st final)
Proof
  cheat
QED

Theorem log_encode_dynamic_safe:
  compile_abi_encode_to_buf dst src (AbiComplex infos) st = (out,final) /\
  EXISTS (\(_,_,_,dyn). dyn) infos /\
  EVERY (\(ei,asz,mz,dyn). log_scalar_enc_info ei) infos ==>
  inst_extends st final /\ same_blocks st final /\
  EVERY (\i. log_encode_safe_opcode i.inst_opcode) (emitted_insts st final)
Proof
  cheat
QED

Theorem log_scalar_encode_safe:
  compile_abi_encode_to_buf dst src ei st = (out,final) /\
  ((?n. ei = AbiCopy n) \/
   (?infos. ei = AbiComplex infos /\ EXISTS (\(_,_,_,dyn). dyn) infos /\
     EVERY (\(child,asz,mz,dyn). log_scalar_enc_info child) infos)) ==>
  EVERY (\i. log_encode_safe_opcode i.inst_opcode) (emitted_insts st final)
Proof
  cheat
QED

Theorem log_scalar_encode_external:
  compile_abi_encode_to_buf dst src ei st = (out,final) /\
  ((?n. ei = AbiCopy n) \/
   (?infos. ei = AbiComplex infos /\ EXISTS (\(_,_,_,dyn). dyn) infos /\
     EVERY (\(child,asz,mz,dyn). log_scalar_enc_info child) infos)) /\
  run_inst_seq (emitted_insts st final) initial = OK actual ==>
  log_encode_external actual = log_encode_external initial
Proof
  cheat
QED
