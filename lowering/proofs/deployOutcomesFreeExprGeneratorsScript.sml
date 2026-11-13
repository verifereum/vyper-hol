Theory deployOutcomesFreeExprGenerators
Ancestors
  deployOutcomesFreeGenerators deployOutcomesFreeLowering exprLowering list

Theorem outcomes_free_mapping_subscript:
  P ALLOCA /\ P MSTORE /\ P ADD /\ P SHA3 /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_mapping_subscript b k s)))
Proof
  strip_tac >> simp[compile_mapping_subscript_def] >>
  rpt (FIRST [gen_tac, strip_tac,
    CHANGED_TAC (simp[outcomes_free_emit_ops, outcomes_free_alloc_buffer]),
    irule outcomes_free_bind, irule outcomes_free_ignore_bind, conj_tac])
QED

Theorem outcomes_free_keccak256_key:
  P ALLOCA /\ P MSTORE /\ P ADD /\ P MLOAD /\ P SHA3 /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_keccak256_key k flag s)))
Proof
  strip_tac >> Cases_on `flag` >> simp[compile_keccak256_key_def] >>
  rpt (FIRST [gen_tac, strip_tac,
    CHANGED_TAC (simp[outcomes_free_emit_ops, outcomes_free_alloc_buffer]),
    irule outcomes_free_bind, irule outcomes_free_ignore_bind, conj_tac])
QED

Theorem outcomes_free_tuple_subscript:
  P ADD /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_tuple_subscript b n s)))
Proof
  simp[compile_tuple_subscript_def, outcomes_free_emit_ops]
QED

Theorem outcomes_free_array_subscript:
  (!b st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (loader b st)))) /\
  P SLT /\ P LT /\ P ISZERO /\ P OR /\ P ASSERT /\ P ADD /\ P MUL /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_array_subscript b i d n ws sz sg loader s)))
Proof
  strip_tac >> Cases_on `d` >> Cases_on `sg` >>
  simp[compile_array_subscript_def] >>
  rpt (FIRST [gen_tac, strip_tac,
    CHANGED_TAC (simp[outcomes_free_emit_ops, outcomes_free_return]),
    irule outcomes_free_bind, irule outcomes_free_ignore_bind, conj_tac])
QED

Theorem outcomes_free_dynarray_pop:
  EVERY P [ADD; ILOAD; DLOAD; MLOAD; SLOAD; TLOAD; CALLDATALOAD;
    ISTORE; INVALID; MSTORE; SSTORE; TSTORE; ISZERO; ASSERT; SUB; MUL] /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_dynarray_pop b ws sz ctor imm loc s)))
Proof
  simp[] >> strip_tac >> simp[compile_dynarray_pop_def] >>
  rpt (FIRST [gen_tac, strip_tac,
    CHANGED_TAC (simp[outcomes_free_emit_ops, outcomes_free_ptr_load,
      outcomes_free_ptr_store]),
    irule outcomes_free_bind, irule outcomes_free_ignore_bind, conj_tac])
QED

Theorem outcomes_free_store_byte_chunks:
  !ptr bs off s. P ADD /\ P MSTORE /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_store_byte_chunks ptr bs off s)))
Proof
  ho_match_mp_tac compile_store_byte_chunks_ind >> rpt strip_tac >>
  gvs[] >> simp[Once compile_store_byte_chunks_def] >>
  rpt (FIRST [gen_tac, strip_tac,
    CHANGED_TAC (simp[outcomes_free_emit_ops, outcomes_free_return]),
    irule outcomes_free_bind, irule outcomes_free_ignore_bind, conj_tac]) >>
  first_x_assum irule >> simp[]
QED

Theorem outcomes_free_bytelike_literal:
  P ALLOCA /\ P ADD /\ P MSTORE /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_bytelike_literal bs n s)))
Proof
  strip_tac >> simp[compile_bytelike_literal_def] >>
  rpt (FIRST [gen_tac, strip_tac,
    CHANGED_TAC (simp[outcomes_free_emit_ops, outcomes_free_return,
      outcomes_free_alloc_buffer, outcomes_free_store_byte_chunks]),
    irule outcomes_free_bind, irule outcomes_free_ignore_bind, conj_tac])
QED

Theorem outcomes_free_literal_vv:
  P ALLOCA /\ P ADD /\ P MSTORE /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_literal_vv ty lit s)))
Proof
  strip_tac >> Cases_on `lit` >>
  simp[compile_literal_vv_def, outcomes_free_return]
  >~ [`BoolL b`] >-
    (Cases_on `b` >> simp[compile_literal_vv_def, outcomes_free_return]) >>
  rpt (FIRST [gen_tac, strip_tac,
    CHANGED_TAC (simp[outcomes_free_return, outcomes_free_bytelike_literal]),
    irule outcomes_free_bind, conj_tac,
    (CASE_TAC >> simp[compile_literal_vv_def, outcomes_free_return])])
QED

Theorem outcomes_free_name_vv:
  P INVALID /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_name_vv ce ty id s)))
Proof
  strip_tac >> simp[compile_name_vv_def] >>
  Cases_on `FLOOKUP ce.ce_vars id` >> simp[outcomes_free_return] >>
  rpt (FIRST [gen_tac, strip_tac,
    CHANGED_TAC (simp[outcomes_free_return, outcomes_free_emit_ops]),
    irule outcomes_free_ignore_bind, conj_tac, CASE_TAC])
QED

Theorem outcomes_free_ifexp_arm:
  EVERY P [ALLOCA; ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD;
    MLOAD; SLOAD; TLOAD; CALLDATALOAD; ISTORE; INVALID; MSTORE; SSTORE;
    TSTORE; CALLDATACOPY; NOT; AND; MCOPY; LT; ISZERO; GT; ASSERT] /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_ifexp_arm ce rt at vv s)))
Proof
  simp[] >> strip_tac >> simp[compile_ifexp_arm_def] >>
  IF_CASES_TAC >>
  rpt (FIRST [gen_tac, strip_tac,
    CHANGED_TAC (simp[outcomes_free_return, outcomes_free_alloc_buffer,
      SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_unwrap_value,
      SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_store_memory]),
    irule outcomes_free_bind, irule outcomes_free_ignore_bind, conj_tac])
QED
