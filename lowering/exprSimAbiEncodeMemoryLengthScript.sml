Theory exprSimAbiEncodeMemoryLength
Ancestors
  venomState venomExecSemantics venomMemProps venomInst exprLoweringProps list arithmetic words

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

Theorem abi_encode_mstore_memory_length:
  LENGTH s.vs_memory <= LENGTH (mstore off w s).vs_memory
Proof
  simp[mstore_def, LENGTH_TAKE, LENGTH_DROP, dimindex_256] >>
  IF_CASES_TAC >> simp[] >> decide_tac
QED

Theorem abi_encode_leaf_step_memory_length:
  MEM i.inst_opcode [ALLOCA;ADD;AND;MLOAD;MSTORE;MCOPY] /\
  step_inst_base i s = OK t ==>
  LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  simp_tac (srw_ss()) [MEM] >> strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  PURE_ONCE_REWRITE_TAC [step_inst_base_def] >>
  asm_rewrite_tac [opcode_case_def] >> strip_tac >>
  gvs[exec_pure2_def, exec_read1_def, exec_write2_def, exec_alloca_def, AllCaseEqs()] >>
  gvs[update_var_def] >>
  metis_tac[abi_encode_mstore_memory_length, abi_encode_mcopy_memory_length]
QED

Theorem abi_encode_leaf_sequence_memory_length:
  !code s t. EVERY (\i. MEM i.inst_opcode [ALLOCA;ADD;AND;MLOAD;MSTORE;MCOPY]) code /\
    run_inst_seq code s = OK t ==>
    LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  Induct >- simp[run_inst_seq_def] >>
  simp_tac bool_ss [run_inst_seq_def, EVERY_DEF] >> rpt gen_tac >>
  Cases_on `step_inst_base h s` >>
  simp_tac bool_ss [exec_result_case_def, exec_result_distinct, exec_result_11] >>
  strip_tac >>
  `LENGTH s.vs_memory <= LENGTH v.vs_memory` by
    (irule abi_encode_leaf_step_memory_length >> qexists_tac `h` >> simp_tac bool_ss [] >>
     conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC) >>
  `LENGTH v.vs_memory <= LENGTH t.vs_memory` by
    (first_x_assum irule >> simp_tac bool_ss [] >>
     conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC) >> decide_tac
QED
