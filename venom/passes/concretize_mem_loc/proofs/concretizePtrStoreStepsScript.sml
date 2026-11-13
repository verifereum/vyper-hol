Theory concretizePtrStoreSteps
Ancestors
  concretizePtrBytes concretizePtrOperationalBytes venomExecSemantics venomState
  codegenRel mem2varBlockSimHelpers mem2varDefs spillSim list arithmetic
  concretizePtrWritePurity concretizePtrValueTransport ptrDiscipline finite_map

Theorem ptr_mstore_written_bytes:
  k < 32 /\ EL k (word_to_bytes v T) = EL k (word_to_bytes vt T) ==>
  read_byte (off + k) (mstore off v s).vs_memory =
  read_byte (offt + k) (mstore offt vt t).vs_memory
Proof
  strip_tac >>
  `mem_byte (off + k) (mstore off v s) = EL k (word_to_bytes v T)` by
    (simp[mem_byte_mstore_inside]) >>
  `mem_byte (offt + k) (mstore offt vt t) = EL k (word_to_bytes vt T)` by
    (simp[mem_byte_mstore_inside]) >>
  gvs[mem_byte_def, read_byte_def]
QED

Theorem ptr_mstore_backward:
  si.inst_opcode = MSTORE /\ ti.inst_opcode = MSTORE /\
  si.inst_operands = [sa;sv] /\ ti.inst_operands = [ta;tv] /\
  eval_operand sa s = SOME addr /\ eval_operand ta t = SOME addrt /\
  eval_operand sv s = SOME value /\ eval_operand tv t = SOME valuet /\
  step_inst fuel Ct ti t = OK t' ==>
  ?s'. step_inst fuel Cs si s = OK s' /\
    (!k. k < 32 /\ EL k (word_to_bytes value T) = EL k (word_to_bytes valuet T) ==>
      read_byte (w2n addr + k) s'.vs_memory =
      read_byte (w2n addrt + k) t'.vs_memory)
Proof
  rpt strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_def, exec_write2_def] >>
  metis_tac[ptr_mstore_written_bytes, ADD_COMM]
QED

Theorem ptr_mstore_protected_bytes[local]:
  ptr_bytes_agree live reloc s.vs_memory t.vs_memory /\
  DISJOINT live {i | off <= i /\ i < off + 32} /\
  DISJOINT (IMAGE reloc live) {i | offt <= i /\ i < offt + 32} ==>
  ptr_bytes_agree live reloc (mstore off v s).vs_memory (mstore offt v t).vs_memory
Proof
  strip_tac >> irule ptr_bytes_agree_unwritten >>
  qexistsl_tac [`s.vs_memory`, `t.vs_memory`,
    `{i | off <= i /\ i < off + 32}`, `{i | offt <= i /\ i < offt + 32}`] >>
  simp[] >> metis_tac[read_byte_mstore_outside]
QED

Theorem ptr_mstore_backward_protected:
  si.inst_opcode = MSTORE /\ ti.inst_opcode = MSTORE /\
  si.inst_operands = [sa;sv] /\ ti.inst_operands = [ta;tv] /\
  eval_operand sa s = SOME addr /\ eval_operand ta t = SOME addrt /\
  eval_operand sv s = SOME value /\ eval_operand tv t = SOME value /\
  step_inst fuel Ct ti t = OK t' /\
  ptr_bytes_agree live reloc s.vs_memory t.vs_memory /\
  DISJOINT live {i | w2n addr <= i /\ i < w2n addr + 32} /\
  DISJOINT (IMAGE reloc live) {i | w2n addrt <= i /\ i < w2n addrt + 32} ==>
  ?s'. step_inst fuel Cs si s = OK s' /\
    ptr_bytes_agree live reloc s'.vs_memory t'.vs_memory /\
    (!k. k < 32 ==> read_byte (w2n addr + k) s'.vs_memory =
      read_byte (w2n addrt + k) t'.vs_memory)
Proof
  rpt strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_def, exec_write2_def] >>
  conj_tac >- (irule ptr_mstore_protected_bytes >> simp[]) >>
  metis_tac[ptr_mstore_written_bytes, ADD_COMM]
QED

Theorem ptr_mstore_backward_masked:
  si.inst_opcode = MSTORE /\ ti.inst_opcode = MSTORE /\
  si.inst_operands = [sa;sv] /\ ti.inst_operands = [ta;tv] /\
  eval_operand sa s = SOME addr /\ eval_operand ta t = SOME addrt /\
  eval_operand sv s = SOME value /\ eval_operand tv t = SOME valuet /\
  step_inst fuel Ct ti t = OK t' /\
  fn_ptr_ok P fn /\ MEM si (fn_insts fn) /\
  (!x. x IN FDOM TG ==> x IN fn_pv P fn) /\
  ptr_value_transport births positions (op_prov TG sv) (op_taint tn sv) value valuet ==>
  ?s'. step_inst fuel Cs si s = OK s' /\
    (!k. k < 32 /\ w2n addr + k NOTIN mem_taint tn si s s' ==>
      read_byte (w2n addr + k) s'.vs_memory =
      read_byte (w2n addrt + k) t'.vs_memory)
Proof
  strip_tac >>
  `op_prov TG sv = NONE` by
    (irule ptr_mstore_value_no_provenance >> metis_tac[]) >>
  gvs[ptr_value_transport_def] >>
  `?s'. step_inst fuel Cs si s = OK s' /\
    (!k. k < 32 /\ EL k (word_to_bytes value T) = EL k (word_to_bytes valuet T) ==>
      read_byte (w2n addr + k) s'.vs_memory =
      read_byte (w2n addrt + k) t'.vs_memory)` by
    (irule ptr_mstore_backward >> metis_tac[]) >>
  qexists_tac `s'` >> simp[] >> rpt strip_tac >>
  first_x_assum (mp_tac o Q.SPEC `k`) >> simp[ADD_COMM] >>
  disch_then irule >>
  `k NOTIN op_taint tn sv` by
    (qpat_x_assum `_ NOTIN mem_taint _ _ _ _` mp_tac >>
     simp[mem_taint_def, written_taint_def] >> metis_tac[]) >>
  gvs[word_agree_except_def]
QED
