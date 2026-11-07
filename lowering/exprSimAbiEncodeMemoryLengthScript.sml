Theory exprSimAbiEncodeMemoryLength
Ancestors
  venomState venomExecSemantics list arithmetic

Theorem abi_encode_write_memory_length:
  !off bytes s.
    LENGTH s.vs_memory <= LENGTH (write_memory_with_expansion off bytes s).vs_memory
Proof
  simp[write_memory_with_expansion_def, LET_THM] >>
  rpt gen_tac >> IF_CASES_TAC >> simp[LENGTH_TAKE, LENGTH_DROP] >>
  decide_tac
QED

Theorem abi_encode_memory_length_chain:
  LENGTH s.vs_memory <= LENGTH t.vs_memory /\
  LENGTH t.vs_memory <= LENGTH u.vs_memory ==>
  LENGTH s.vs_memory <= LENGTH u.vs_memory
Proof
  decide_tac
QED

Theorem abi_encode_mcopy_memory_length:
  LENGTH s.vs_memory <= LENGTH (mcopy d src n s).vs_memory
Proof
  simp_tac bool_ss [mcopy_def, LET_THM] >> irule abi_encode_write_memory_length
QED

Theorem abi_encode_memory_length_inst_idx[simp]:
  LENGTH (s with vs_inst_idx := ix).vs_memory = LENGTH s.vs_memory
Proof
  simp[]
QED
