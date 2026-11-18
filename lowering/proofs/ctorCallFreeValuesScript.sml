(* Opcode preservation at the memory/value boundary. *)
Theory ctorCallFreeValues
Ancestors
  list compileEnv venomInst loweringShapeDefs emitHelper context exprLowering
  ctorCallFreeRules

Theorem outcomes_free_alloc_buffer:
  P ALLOCA /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_alloc_buffer sz s)))
Proof
  rpt strip_tac >> simp[compile_alloc_buffer_def] >>
  irule ctorCallFreeRulesTheory.every_state_insts_bind >> simp[every_state_insts_return,
      opcode_every_emit_op, opcode_every_emit_void, opcode_every_emit_inst]
QED

Theorem outcomes_free_imm_load:
  P ADD /\ P ILOAD /\ P DLOAD /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_imm_load_word ctor imm off s)))
Proof
  rpt strip_tac >> Cases_on `ctor` >> Cases_on `imm` >>
  simp[compile_imm_load_word_def, opcode_every_emit_op, opcode_every_emit_void,
      opcode_every_emit_inst] >>
  irule ctorCallFreeRulesTheory.every_state_insts_bind >> simp[opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst]
QED

Theorem outcomes_free_ptr_load:
  P ADD /\ P ILOAD /\ P DLOAD /\ P MLOAD /\ P SLOAD /\
  P TLOAD /\ P CALLDATALOAD /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_ptr_load ctor imm loc off s)))
Proof
  rpt strip_tac >> Cases_on `loc` >>
  simp[compile_ptr_load_def, opcode_every_emit_op, opcode_every_emit_void,
      opcode_every_emit_inst, outcomes_free_imm_load]
QED

Theorem outcomes_free_imm_store:
  P ADD /\ P ISTORE /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_imm_store_word imm off v s)))
Proof
  rpt strip_tac >> Cases_on `imm` >>
  simp[compile_imm_store_word_def, opcode_every_emit_op, opcode_every_emit_void,
      opcode_every_emit_inst] >>
  irule ctorCallFreeRulesTheory.every_state_insts_bind >> simp[opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst]
QED

Theorem outcomes_free_ptr_store:
  P ADD /\ P ISTORE /\ P INVALID /\ P MSTORE /\ P SSTORE /\ P TSTORE /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_ptr_store ctor imm loc off v s)))
Proof
  rpt strip_tac >> Cases_on `loc` >> Cases_on `ctor` >>
  simp[compile_ptr_store_def, opcode_every_emit_op, opcode_every_emit_void,
      opcode_every_emit_inst, outcomes_free_imm_store]
QED

Theorem outcomes_free_copy_memory:
  P MCOPY /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_copy_memory dst src sz s)))
Proof
  Cases_on `sz` >> simp[compile_copy_memory_def, every_state_insts_return,
    opcode_every_emit_op, opcode_every_emit_void, opcode_every_emit_inst]
QED

Theorem outcomes_free_word_copy_base:
  (!opc. MEM opc [ADD; MUL; ASSIGN; JMP; EQ; JNZ] ==> P opc) /\
  (!off st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
     EVERY (\i. P i.inst_opcode)
       (state_insts (SND (compile_ptr_load ctor imm load off st)))) /\
  (!off v st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
     EVERY (\i. P i.inst_opcode)
       (state_insts (SND (compile_ptr_store ctor imm store off v st)))) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND
      (compile_word_copy_loop_base src dst nwords load store ctor imm s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_word_copy_loop_base_def] >>
  rpt (FIRST [CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void,
      opcode_every_emit_inst, every_state_insts_return,
               every_state_insts_fresh_id, every_state_insts_fresh_var,
                   every_state_insts_fresh_label, every_state_insts_new_block]),
       gen_tac, strip_tac, irule ctorCallFreeRulesTheory.every_state_insts_bind,
       irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind, conj_tac, IF_CASES_TAC]) >>
  gvs[]
QED

Theorem outcomes_free_word_copy:
  (!opc. MEM opc [ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD; MLOAD;
                  SLOAD; TLOAD; CALLDATALOAD; ISTORE; INVALID; MSTORE;
                  SSTORE; TSTORE] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND
      (compile_word_copy_loop src dst nwords load store ctor s))) /\
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND
      (compile_word_copy_loop_op src dst nwop load store ctor s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_word_copy_loop_def, compile_word_copy_loop_op_def] >>
  conj_tac >> irule outcomes_free_word_copy_base >>
  simp[DISJ_IMP_THM, outcomes_free_ptr_load, outcomes_free_ptr_store]
QED

Theorem outcomes_free_lit_offset:
  P ADD /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_lit_byte_offset op off s)))
Proof
  rpt strip_tac >> Cases_on `off = 0` >> Cases_on `op` >>
  simp[compile_lit_byte_offset_def, every_state_insts_return, opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst]
QED

Theorem outcomes_free_imm_copy:
  !n off s. P ADD /\ P ILOAD /\ P DLOAD /\ P MSTORE /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_imm_copy_to_memory ctor imm src dst n off s)))
Proof
  Induct_on `n` >> rpt strip_tac >>
  simp[compile_imm_copy_to_memory_def, every_state_insts_return] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_lit_offset,
          outcomes_free_imm_load, opcode_every_emit_op, opcode_every_emit_void,
              opcode_every_emit_inst]),
       gen_tac, strip_tac, irule ctorCallFreeRulesTheory.every_state_insts_bind,
       irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind, conj_tac, first_assum irule])
QED

Theorem outcomes_free_slot_copies:
  (!opc. MEM opc [ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD; MLOAD;
                  SLOAD; TLOAD; CALLDATALOAD; ISTORE; INVALID; MSTORE;
                  SSTORE; TSTORE] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_storage_to_memory src dst n s))) /\
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_memory_to_storage src dst n s))) /\
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_transient_to_memory src dst n s))) /\
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_memory_to_transient src dst n s)))
Proof
  strip_tac >> simp[compile_storage_to_memory_def, compile_memory_to_storage_def,
    compile_transient_to_memory_def, compile_memory_to_transient_def,
    outcomes_free_word_copy]
QED

Theorem outcomes_free_ensure_memory:
  (!opc. MEM opc [ALLOCA; ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD;
    MLOAD; SLOAD; TLOAD; CALLDATALOAD; ISTORE; INVALID; MSTORE; SSTORE;
    TSTORE; CALLDATACOPY] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_ensure_in_memory ptr_op loc bytes words ctor imm s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `loc` >> simp[compile_ensure_in_memory_def] >>
  rpt (FIRST [CHANGED_TAC (simp[every_state_insts_return, opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst,
    outcomes_free_alloc_buffer, outcomes_free_imm_copy,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_slot_copies]),
    gen_tac, strip_tac, irule ctorCallFreeRulesTheory.every_state_insts_bind,
        irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind,
    conj_tac, IF_CASES_TAC]) >> gvs[]
QED

Theorem outcomes_free_unwrap_value:
  (!opc. MEM opc [ALLOCA; ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD;
    MLOAD; SLOAD; TLOAD; CALLDATALOAD; ISTORE; INVALID; MSTORE; SSTORE;
    TSTORE; CALLDATACOPY] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND (unwrap_value cenv vv s)))
Proof
  strip_tac >> Cases_on `vv` >> simp[unwrap_value_def, every_state_insts_return] >>
  IF_CASES_TAC >- simp[outcomes_free_ptr_load] >>
  BasicProvers.TOP_CASE_TAC >>
  simp[every_state_insts_return, outcomes_free_ensure_memory]
QED

Theorem outcomes_free_bytestring_copy:
  P MLOAD /\ P NOT /\ P ADD /\ P AND /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_bytestring_copy_len src s))) /\
  (P MCOPY ==>
   EVERY (\i. P i.inst_opcode)
     (state_insts (SND (compile_store_bytestring src dst s))))
Proof
  strip_tac >> simp[compile_bytestring_copy_len_def, compile_store_bytestring_def] >>
  rpt (FIRST [CHANGED_TAC (simp[every_state_insts_return, opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst,
    compile_bytestring_copy_len_def]),
    gen_tac, strip_tac, irule ctorCallFreeRulesTheory.every_state_insts_bind,
        irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind,
    conj_tac])
QED

Theorem outcomes_free_byte_offset:
  P ADD /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_with_byte_offset src off s)))
Proof
  strip_tac >> simp[compile_with_byte_offset_def] >>
  IF_CASES_TAC >> simp[every_state_insts_return, opcode_every_emit_op, opcode_every_emit_void,
      opcode_every_emit_inst]
QED

Theorem outcomes_free_typed_copy:
  (!opc. MEM opc [MLOAD; MSTORE; NOT; ADD; AND; MCOPY; INVALID; ASSIGN;
    JMP; LT; ISZERO; JNZ; MUL; GT; ASSERT] ==> P opc) ==>
  (!ce dst dt src st s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_store_memory_typed ce dst dt src st s)))) /\
  (!ce dst src dts sts doff soff s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_typed_copy_fields ce dst src dts sts doff soff s)))) /\
  (!ce dst dt src st n s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_copy_sarray_typed ce dst dt src st n s)))) /\
  (!ce dst dt cap src st s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_copy_dynarray_typed ce dst dt cap src st s)))) /\
  (!ce dst src dfs sfs doff soff s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_struct_typed_copy ce dst src dfs sfs doff soff s))))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  ho_match_mp_tac compile_store_memory_typed_ind >> rpt strip_tac
  >- (simp[Once compile_store_memory_typed_def] >>
      Cases_on `is_word_type dt`
      >- (simp[] >> irule ctorCallFreeRulesTheory.every_state_insts_bind >> simp[opcode_every_emit_op, opcode_every_emit_void, opcode_every_emit_inst]) >>
      Cases_on `is_bytestring_type dt /\ is_bytestring_type st`
      >- simp[outcomes_free_bytestring_copy] >>
      Cases_on `acyclic_struct_metadata ce.ce_struct_fields`
      >- (Cases_on `dt` >> Cases_on `st` >> gvs[] >>
          rpt (BasicProvers.TOP_CASE_TAC >> gvs[]) >> simp[outcomes_free_copy_memory]) >>
      simp[opcode_every_emit_op, opcode_every_emit_void, opcode_every_emit_inst]) >>
  simp[Once compile_store_memory_typed_def] >> gnvs[] >>
  rpt (FIRST [CHANGED_TAC (simp[every_state_insts_return, opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst,
    every_state_insts_fresh_id, every_state_insts_fresh_var, every_state_insts_fresh_label,
        every_state_insts_new_block, outcomes_free_byte_offset,
    outcomes_free_copy_memory, outcomes_free_bytestring_copy,
    compile_copy_memory_dynamic_def]),
    gen_tac, strip_tac, irule ctorCallFreeRulesTheory.every_state_insts_bind,
        irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind,
    conj_tac, IF_CASES_TAC,
    first_assum (fn th => irule th >> simp[] >> NO_TAC), pairarg_tac]) >>
  first_x_assum irule >> gvs[] >> metis_tac[]
QED

Theorem outcomes_free_store_memory:
  (!opc. MEM opc [MLOAD; MSTORE; NOT; ADD; AND; MCOPY; INVALID; ASSIGN;
    JMP; LT; ISZERO; JNZ; MUL; GT; ASSERT] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_store_memory ce src dst dt st s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_store_memory_def] >> rpt IF_CASES_TAC >>
  simp[opcode_every_emit_op, opcode_every_emit_void, opcode_every_emit_inst,
      outcomes_free_copy_memory, outcomes_free_bytestring_copy,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] (cj 1 outcomes_free_typed_copy)]
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
    CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void, opcode_every_emit_inst,
        outcomes_free_ptr_load,
      outcomes_free_ptr_store]),
    irule ctorCallFreeRulesTheory.every_state_insts_bind,
        irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind, conj_tac])
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
    CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void, opcode_every_emit_inst,
        every_state_insts_return]),
    irule ctorCallFreeRulesTheory.every_state_insts_bind,
        irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind, conj_tac]) >>
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
    CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void, opcode_every_emit_inst,
        every_state_insts_return,
      outcomes_free_alloc_buffer, outcomes_free_store_byte_chunks]),
    irule ctorCallFreeRulesTheory.every_state_insts_bind,
        irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind, conj_tac])
QED

Theorem outcomes_free_literal_vv:
  P ALLOCA /\ P ADD /\ P MSTORE /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_literal_vv ty lit s)))
Proof
  strip_tac >> Cases_on `lit` >>
  simp[compile_literal_vv_def, every_state_insts_return]
  >~ [`BoolL b`] >-
    (Cases_on `b` >> simp[compile_literal_vv_def, every_state_insts_return]) >>
  rpt (FIRST [gen_tac, strip_tac,
    CHANGED_TAC (simp[every_state_insts_return, outcomes_free_bytelike_literal]),
    irule ctorCallFreeRulesTheory.every_state_insts_bind, conj_tac,
    (CASE_TAC >> simp[compile_literal_vv_def, every_state_insts_return])])
QED

Theorem outcomes_free_name_vv:
  P INVALID /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_name_vv ce ty id s)))
Proof
  strip_tac >> simp[compile_name_vv_def] >>
  Cases_on `FLOOKUP ce.ce_vars id` >> simp[every_state_insts_return] >>
  rpt (FIRST [gen_tac, strip_tac,
    CHANGED_TAC (simp[every_state_insts_return, opcode_every_emit_op, opcode_every_emit_void,
        opcode_every_emit_inst]),
    irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind, conj_tac, CASE_TAC])
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
    CHANGED_TAC (simp[every_state_insts_return, outcomes_free_alloc_buffer,
      SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_unwrap_value,
      SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_store_memory]),
    irule ctorCallFreeRulesTheory.every_state_insts_bind,
        irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind, conj_tac])
QED

Theorem outcomes_free_materialize_vv:
  (!n st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_alloc_buffer n st)))) /\
  (!v st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (unwrap_value ce v st)))) /\
  (!a b ty sty st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_store_memory ce a b ty sty st)))) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_materialize_vv ce ty vv s)))
Proof
  strip_tac >> simp[compile_materialize_vv_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> metis_tac[pairTheory.SND]
QED

Theorem outcomes_free_snapshot:
  (!ce v st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (unwrap_value ce v st)))) /\
  (!n st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_alloc_buffer n st)))) /\
  (!ce a b ty sty st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_store_memory ce a b ty sty st)))) ==>
  !ce copy v s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_snapshot_vv ce copy v s)))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> simp[compile_snapshot_vv_def] >>
  IF_CASES_TAC
  >- (irule ctorCallFreeRulesTheory.every_state_insts_bind >> simp[every_state_insts_return]) >>
  IF_CASES_TAC >> simp[every_state_insts_return] >>
  irule ctorCallFreeRulesTheory.every_state_insts_bind >> simp[every_state_insts_return] >>
  rpt strip_tac >> irule outcomes_free_materialize_vv >> simp[]
QED

Theorem opcode_every_alloc_buffer:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode)
    (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_alloc_buffer sz st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_alloc_buffer >> simp[]
QED

Theorem call_free_alloc_buffer:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_alloc_buffer sz st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_alloc_buffer) >> simp[]
QED

Theorem opcode_every_imm_load_word:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode)
    (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_imm_load_word ctor imm off st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_imm_load >> simp[]
QED

Theorem opcode_every_imm_store_word:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode)
    (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_imm_store_word imm off v st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_imm_store >> simp[]
QED

Theorem opcode_every_ptr_load:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode)
    (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_ptr_load ctor imm loc op st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_ptr_load >> simp[]
QED

Theorem opcode_every_ptr_store:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode)
    (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_ptr_store ctor imm loc dst v st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_ptr_store >> simp[]
QED

Theorem opcode_every_copy_memory:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode)
    (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_copy_memory dst src sz st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_copy_memory >> simp[]
QED

Theorem opcode_every_word_copy_loop_base:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode)
    (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND
      (compile_word_copy_loop_base src dst nwords ll sl ctor imm st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_word_copy_base >>
  simp[DISJ_IMP_THM, outcomes_free_ptr_load, outcomes_free_ptr_store]
QED

Theorem opcode_every_word_copy_loop:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode)
    (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND
      (compile_word_copy_loop src dst nwords ll sl ctor st)))
  )
Proof
  rpt strip_tac >> irule (cj 1 outcomes_free_word_copy) >>
  simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem opcode_every_store_byte_chunks:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  !dst bs off st.
  EVERY (\i. P i.inst_opcode)
    (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_store_byte_chunks dst bs off st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_store_byte_chunks >> simp[]
QED

Theorem opcode_every_bytelike_literal:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode)
    (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_bytelike_literal bs max_len st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_bytelike_literal >> simp[]
QED

Theorem opcode_every_literal_vv:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode)
    (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_literal_vv ty lit st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_literal_vv >> simp[]
QED

Theorem opcode_every_name_vv:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode)
    (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_name_vv ce ty nm st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_name_vv >> simp[]
QED

Theorem opcode_every_lit_byte_offset:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode)
    (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_lit_byte_offset op off st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_lit_offset >> simp[]
QED

Theorem opcode_every_imm_copy_to_memory:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  !n ctor imm src dst off st.
  EVERY (\i. P i.inst_opcode)
    (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_imm_copy_to_memory ctor imm src dst n off st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_imm_copy >> simp[]
QED

Theorem opcode_every_ensure_in_memory:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode)
    (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_ensure_in_memory ptr_op loc sz nw ctor imm st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_ensure_memory >> simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem opcode_every_unwrap_value:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode)
    (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (unwrap_value ce vv st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_unwrap_value >> simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem opcode_every_with_byte_offset:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode)
    (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_with_byte_offset base_op off st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_byte_offset >> simp[]
QED

Theorem opcode_every_bytestring_copy_len:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode)
    (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_bytestring_copy_len src st)))
  )
Proof
  rpt strip_tac >> irule (cj 1 outcomes_free_bytestring_copy) >> simp[]
QED

Theorem opcode_every_store_bytestring:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode)
    (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_store_bytestring src dst st)))
  )
Proof
  rpt strip_tac >> irule (cj 2 outcomes_free_bytestring_copy) >> simp[]
QED

Theorem outcomes_free_copy_memory_dynamic:
  P MCOPY /\ EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_copy_memory_dynamic dst src len st)))
Proof
  simp[compile_copy_memory_dynamic_def, opcode_every_emit_void]
QED

Theorem opcode_every_copy_memory_dynamic:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode)
    (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_copy_memory_dynamic dst src len st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_copy_memory_dynamic >> simp[]
QED

Theorem opcode_every_typed_copy:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!ce dst dty src sty st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_store_memory_typed ce dst dty src sty st)))) /\
  (!ce dst src dtys stys doff soff st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_typed_copy_fields ce dst src dtys stys doff soff st)))) /\
  (!ce dst dty src sty ncopy st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_copy_sarray_typed ce dst dty src sty ncopy st)))) /\
  (!ce dst dty cap src sty st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_copy_dynarray_typed ce dst dty cap src sty st)))) /\
  (!ce dst src dfs sfs doff soff st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_struct_typed_copy ce dst src dfs sfs doff soff st))))
  )
Proof
  strip_tac >> irule outcomes_free_typed_copy >> simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem opcode_every_store_memory:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_store_memory ce src dst dty sty st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_store_memory >> simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem opcode_every_ifexp_arm:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_ifexp_arm ce rty aty vv st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_ifexp_arm >> simp[]
QED


Theorem opcode_every_materialize_vv:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_materialize_vv ce ty vv st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_materialize_vv >>
  simp[UNDISCH opcode_every_unwrap_value, UNDISCH opcode_every_alloc_buffer,
       UNDISCH opcode_every_store_memory]
QED

Theorem opcode_every_snapshot_vv:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_snapshot_vv ce copy vv st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_snapshot >>
  simp[UNDISCH opcode_every_unwrap_value, UNDISCH opcode_every_alloc_buffer,
       UNDISCH opcode_every_store_memory]
QED


Theorem opcode_every_dynarray_pop:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_dynarray_pop ptr_op scale esz ctor imm loc st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_dynarray_pop >> simp[]
QED
