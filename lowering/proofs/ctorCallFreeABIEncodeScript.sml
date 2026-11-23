(* Opcode preservation for ABI encoding. *)
Theory ctorCallFreeABIEncode
Ancestors
  list compileEnv venomInst loweringShapeDefs emitHelper context abiEncoder
  ctorCallFreeRules ctorCallFreeValues exprLowering

val abi_preserve_tac =
  rpt (FIRST [CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void,
      opcode_every_emit_inst, every_state_insts_return,
    every_state_insts_fresh_id, every_state_insts_fresh_var, every_state_insts_fresh_label,
        every_state_insts_new_block, outcomes_free_alloc_buffer,
    outcomes_free_copy_memory]),
    gen_tac, strip_tac, irule ctorCallFreeRulesTheory.every_state_insts_bind,
    irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind, conj_tac, IF_CASES_TAC]);

Theorem outcomes_free_abi_encode_static:
  P MLOAD /\ P MSTORE /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_abi_encode_static dst src s)))
Proof
  strip_tac >> simp[compile_abi_encode_static_def] >> abi_preserve_tac
QED

Theorem outcomes_free_abi_encode_static_info:
  P MLOAD /\ P MSTORE /\ P MCOPY /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_abi_encode_static_info dst src info s)))
Proof
  strip_tac >> Cases_on `info` >>
  simp[compile_abi_encode_static_info_def, outcomes_free_abi_encode_static] >>
  abi_preserve_tac
QED

Theorem outcomes_free_abi_encode_dyn_static_loop:
  (!opc. MEM opc [ALLOCA; MLOAD; MSTORE; MCOPY; JMP; LT; ISZERO; JNZ;
    ADD; MUL] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_abi_encode_dyn_static_loop dst src info asz msz len s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_abi_encode_dyn_static_loop_def] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_abi_encode_static_info]),
    CHANGED_TAC abi_preserve_tac])
QED

val abi_encode_case_tac =
  simp[Once compile_abi_encode_child_def] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_abi_encode_static,
    outcomes_free_abi_encode_dyn_static_loop, DISJ_IMP_THM, FORALL_AND_THM]),
    CHANGED_TAC abi_preserve_tac, CHANGED_TAC (gvs[]),
    first_x_assum irule]) >> gvs[];

Theorem outcomes_free_abi_encode:
  (!dst src info dyn off dp s.
    (!opc. MEM opc [ALLOCA; MLOAD; MSTORE; MCOPY; JMP; LT; ISZERO; JNZ;
      ADD; MUL; AND; NOT] ==> P opc) /\
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_abi_encode_child dst src info dyn off dp s)))) /\
  (!dst src info s.
    (!opc. MEM opc [ALLOCA; MLOAD; MSTORE; MCOPY; JMP; LT; ISZERO; JNZ;
      ADD; MUL; AND; NOT] ==> P opc) /\
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_abi_encode_to_buf dst src info s)))) /\
  (!dst src elems so ho dp s.
    (!opc. MEM opc [ALLOCA; MLOAD; MSTORE; MCOPY; JMP; LT; ISZERO; JNZ;
      ADD; MUL; AND; NOT] ==> P opc) /\
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_abi_encode_complex_elems dst src elems so ho dp s)))) /\
  (!dst src info asz msz len s.
    (!opc. MEM opc [ALLOCA; MLOAD; MSTORE; MCOPY; JMP; LT; ISZERO; JNZ;
      ADD; MUL; AND; NOT] ==> P opc) /\
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_abi_encode_dyn_loop dst src info asz msz len s))))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >> rpt strip_tac >>
  fs[DISJ_IMP_THM, FORALL_AND_THM] >> abi_encode_case_tac
QED

Theorem opcode_every_abi_encode:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!dst cp ci dyn off dp st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_abi_encode_child dst cp ci dyn off dp st)))) /\
  (!dst src info st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_abi_encode_to_buf dst src info st)))) /\
  (!dst src elems so ho dp st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_abi_encode_complex_elems dst src elems so ho dp st)))) /\
  (!dst src info asz msz len_op st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_abi_encode_dyn_loop dst src info asz msz len_op st))))
  )
Proof
  strip_tac >> rpt conj_tac >> rpt gen_tac >> strip_tac >>
  FIRST (map irule (CONJUNCTS outcomes_free_abi_encode)) >>
  simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem outcomes_free_abi_encode_values_to_buf:
  (!opc. opc <> CALL /\ opc <> STATICCALL /\ opc <> DELEGATECALL /\
         opc <> CREATE /\ opc <> CREATE2 /\ opc <> INVOKE /\
         opc <> RETURNDATACOPY ==> P opc) ==>
  !s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_abi_encode_values_to_buf cenv dst rows s)))
Proof
  strip_tac >>
  `!rs d c off s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
     EVERY (\i. P i.inst_opcode)
       (state_insts (SND (compile_abi_encode_value_rows cenv d c off rs s)))` by
    (Induct >> simp[compile_abi_encode_value_rows_def, every_state_insts_return] >>
     gen_tac >> PairCases_on `h` >>
     simp[compile_abi_encode_value_rows_def] >> rpt gen_tac >>
     simp_tac bool_ss [GSYM AND_IMP_INTRO] >>
     fs[DISJ_IMP_THM, FORALL_AND_THM] >>
     rpt (FIRST [CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void,
       every_state_insts_return, outcomes_free_unwrap_value,
       outcomes_free_store_memory, cj 2 outcomes_free_abi_encode,
       DISJ_IMP_THM, FORALL_AND_THM]),
       gen_tac, strip_tac, irule ctorCallFreeRulesTheory.every_state_insts_bind,
       irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind,
       conj_tac, IF_CASES_TAC])) >>
  simp[compile_abi_encode_values_to_buf_def] >> abi_preserve_tac
QED
