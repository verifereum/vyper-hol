(* Successful primitive execution cannot shrink byte memory. *)
Theory execMemoryLengthBase
Ancestors
  venomExecSemantics venomExecProofs venomMemProps venomInstProofs3
  opcodeClass venomState venomCallOracleDefs list arithmetic

Theorem step_base_memory_length:
  step_inst_base inst s = OK t ==>
  LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  Cases_on `inst.inst_opcode` >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs] >>
  strip_tac >>
  imp_res_tac exec_pure1_memory_preserves >>
  imp_res_tac exec_pure2_memory_preserves >>
  imp_res_tac exec_pure3_memory_preserves >>
  imp_res_tac exec_read0_memory_preserves >>
  imp_res_tac exec_read1_memory_preserves >>
  imp_res_tac exec_gas_memory_preserves >>
  gvs[exec_write2_def, exec_alloca_def, AllCaseEqs(), update_var_def] >>
  simp[mstore_memory_nondecreasing, mstore8_memory_nondecreasing,
       write_memory_with_expansion_nondecreasing] >>
  gvs[eval_operands_def] >>
  gvs[exec_create_def, exec_ext_call_def, exec_delegatecall_def,
      consume_create_outcome_eq, consume_call_outcome_eq, AllCaseEqs(),
      update_var_def] >>
  imp_res_tac extract_venom_result_memory >>
  gvs[] >> simp[write_memory_with_expansion_nondecreasing] >>
  simp[mcopy_def, sstore_def, tstore_def, istore_shared_fields, jump_to_def,
       write_memory_with_expansion_nondecreasing] >>
  pairarg_tac >> gvs[]
QED

Theorem pack_dret_dynamic_memory_length[local]:
  !pairs cursor s ptrs final_cursor t.
    pack_dret_dynamic cursor pairs s = (ptrs,final_cursor,t) ==>
    LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  Induct >> simp[pack_dret_dynamic_def] >>
  qx_gen_tac `h` >> PairCases_on `h` >> rpt gen_tac >>
  simp[pack_dret_dynamic_def] >> pairarg_tac >> simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  gvs[mcopy_def, LENGTH_write_memory_with_expansion]
QED

Theorem step_base_intret_memory_length:
  step_inst_base inst s = IntRet ret t ==>
  LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  strip_tac >> drule step_inst_base_intret_opcodes >> strip_tac >>
  gvs[step_inst_base_def, AllCaseEqs()] >>
  pairarg_tac >> gvs[] >>
  drule pack_dret_dynamic_memory_length >> simp[]
QED
