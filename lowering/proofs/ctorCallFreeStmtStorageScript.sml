(* Assignment, local declaration, and loop scaffolding opcode boundaries. *)
Theory ctorCallFreeStmtStorage
Ancestors
  list pair stmtLowering context venomInst loweringShapeDefs emitHelper compileEnv
  ctorCallFreeRules ctorCallFreeValues

Theorem outcomes_free_imm_store_words:
  !n off s. P ADD /\ P MLOAD /\ P ISTORE /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_imm_store_words imm src dst n off s)))
Proof
  Induct_on `n` >> rpt strip_tac >>
  simp[compile_imm_store_words_def, every_state_insts_return] >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_lit_offset,
    outcomes_free_imm_store, opcode_every_emit_op, opcode_every_emit_void, opcode_every_emit_inst]),
    gen_tac, strip_tac, irule ctorCallFreeRulesTheory.every_state_insts_bind,
    irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind, conj_tac, first_assum irule])
QED

Theorem outcomes_free_bytestring_word_count:
  P MLOAD /\ P ADD /\ P SHR /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_bytestring_word_count src s)))
Proof
  strip_tac >> simp[compile_bytestring_word_count_def] >>
  irule ctorCallFreeRulesTheory.every_state_insts_bind >> simp[opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst] >> rpt strip_tac >>
  irule ctorCallFreeRulesTheory.every_state_insts_bind >> simp[opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst]
QED

Theorem outcomes_free_store_immutable_bytestring:
  (!opc. MEM opc [ADD; MUL; ASSIGN; JMP; EQ; JNZ; MLOAD; ISTORE; SHR]
    ==> P opc) /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_store_immutable_bytestring imm src dst s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_store_immutable_bytestring_def] >>
  irule ctorCallFreeRulesTheory.every_state_insts_bind >> simp[outcomes_free_bytestring_word_count] >>
  rpt strip_tac >> irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind >>
  simp[every_state_insts_return] >> rpt strip_tac >>
  irule outcomes_free_word_copy_base >>
  simp[DISJ_IMP_THM, compile_ptr_load_def, compile_ptr_store_def,
    opcode_every_emit_op, outcomes_free_imm_store]
QED

Theorem outcomes_free_slot_to_memory:
  (!opc. MEM opc [ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD; MLOAD;
    SLOAD; TLOAD; CALLDATALOAD; MSTORE] ==> P opc) /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_slot_to_memory src dst n loc s)))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[compile_slot_to_memory_def, compile_word_copy_loop_def,
    compile_word_copy_loop_op_def] >>
  irule outcomes_free_word_copy_base >>
  simp[DISJ_IMP_THM, outcomes_free_ptr_load, compile_ptr_store_def,
    opcode_every_emit_void]
QED

Theorem outcomes_free_range_bound_checks:
  P SGT /\ P GT /\ P ISZERO /\ P ASSERT ==>
  !a b c n signed s.
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_range_bound_checks a b c n signed s)))
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  Cases_on `signed` >>
  simp[compile_range_bound_checks_def, comp_ignore_bind_def, comp_bind_def,
       emit_op_def, emit_void_def, emit_inst_def, fresh_var_def, fresh_id_def,
       comp_return_def, emit_def, outcomes_free_state_insts, mk_inst_def]
QED

Theorem outcomes_free_declare_local:
  !cenv id ty s.
    EVERY P (state_insts s) ==>
    EVERY P (state_insts (SND (declare_local cenv id ty s)))
Proof
  rpt gen_tac >> simp[declare_local_def] >>
  Cases_on `cenv.ce_alloca_locals` >>
  simp[comp_bind_def, comp_return_def, fresh_var_def, fresh_id_def,
       outcomes_free_state_insts]
QED

Theorem outcomes_free_emit_local_alloca:
  P ALLOCA ==>
  !cenv id s.
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (emit_local_alloca cenv id s)))
Proof
  strip_tac >> rpt gen_tac >>
  Cases_on `FLOOKUP cenv.ce_vars id` >>
  simp[emit_local_alloca_def, every_state_insts_return] >>
  rename1 `SOME loc` >> Cases_on `loc` >>
  simp[every_state_insts_return] >> rename1 `PtrVar op n` >> Cases_on `op` >>
  simp[every_state_insts_return, opcode_every_emit_op, opcode_every_emit_void,
      opcode_every_emit_inst]
QED

Theorem outcomes_free_declare_stmt_local:
  !cenv stmt s.
    EVERY P (state_insts s) ==>
    EVERY P (state_insts (SND (declare_stmt_local cenv stmt s)))
Proof
  rpt gen_tac >> Cases_on `stmt` >>
  simp[declare_stmt_local_def, every_state_insts_return, outcomes_free_declare_local]
QED

Theorem outcomes_free_iter_elem_copy:
  P MSTORE /\ P MLOAD /\ P CALLDATACOPY /\
  (!a b n loc s.
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_slot_to_memory a b n loc s)))) /\
  (!ctor alloc loc ptr s.
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_ptr_load ctor alloc loc ptr s)))) /\
  (!ctor alloc src dst n k s.
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_imm_copy_to_memory ctor alloc src dst n k s)))) /\
  (!dst src n s.
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_copy_memory dst src n s)))) /\
  (!env src dst ty sty s.
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_store_memory env src dst ty sty s)))) ==>
  !env src dst n loc slots ty sty s.
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_iter_elem_copy env src dst n loc slots ty sty s)))
Proof
  strip_tac >> rpt gen_tac >>
  Cases_on `slots` >> simp[compile_iter_elem_copy_def] >>
  Cases_on `loc` >> simp[] >>
  rpt IF_CASES_TAC >> simp[] >>
  rpt (FIRST [irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind >> conj_tac,
              irule ctorCallFreeRulesTheory.every_state_insts_bind >> conj_tac,
              gen_tac, disch_tac]) >>
  simp[every_state_insts_return, opcode_every_emit_op, opcode_every_emit_void,
      opcode_every_emit_inst]
QED

Theorem outcomes_free_load_memory:
  P MLOAD /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_load_memory src prim s)))
Proof
  strip_tac >> Cases_on `prim` >>
  simp[compile_load_memory_def, every_state_insts_return, opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst]
QED

Theorem outcomes_free_compile_tuple_load_all:
  P ADD /\
  (!op word s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_load_memory op word s)))) ==>
  !tys cenv base offset s.
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_tuple_load_all cenv base tys offset s)))
Proof
  strip_tac >> Induct_on `tys` >>
  simp[compile_tuple_load_all_def, every_state_insts_return] >>
  rpt gen_tac >> strip_tac >> BETA_TAC >> irule ctorCallFreeRulesTheory.every_state_insts_bind >> reverse conj_tac
  >- simp[opcode_every_emit_op, opcode_every_emit_void, opcode_every_emit_inst] >>
  rpt gen_tac >> strip_tac >> BETA_TAC >> irule ctorCallFreeRulesTheory.every_state_insts_bind >> reverse conj_tac
  >- simp[] >>
  rpt gen_tac >> strip_tac >> BETA_TAC >> irule ctorCallFreeRulesTheory.every_state_insts_bind >>
  simp[every_state_insts_return]
QED

Theorem outcomes_free_compile_store_at_loc:
  P MSTORE /\ P SSTORE /\ P TSTORE /\ P INVALID /\
  (!imm dst value s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_imm_store_word imm dst value s)))) ==>
  !imm dst value loc s.
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_store_at_loc imm dst value loc s)))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> namedCases_on `loc` ["", "loc_kind"]
  >- simp[compile_store_at_loc_def, opcode_every_emit_op, opcode_every_emit_void,
      opcode_every_emit_inst] >>
  Cases_on `loc_kind` >> simp[compile_store_at_loc_def, opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst]
QED

Theorem outcomes_free_compile_assign_value:
  EVERY P [MSTORE; SSTORE; TSTORE; MLOAD; INVALID] /\
  (!n s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_alloc_buffer n s)))) /\
  (!ce a b ty sty s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_store_memory ce a b ty sty s)))) /\
  (!ce a ty b sty s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_store_memory_typed ce a ty b sty s)))) /\
  (!a b n s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_copy_memory a b n s)))) /\
  (!ce a b ty tr s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_store_slots ce a b ty tr s)))) /\
  (!imm a b s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_imm_store_word imm a b s)))) /\
  (!imm a b s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_store_immutable_bytestring imm a b s)))) /\
  (!imm a b n k s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_imm_store_words imm a b n k s)))) ==>
  !ce dst loc value prim src_loc dst_ty src_ty size s.
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts
      (SND (compile_assign_value ce dst loc value prim src_loc dst_ty src_ty size s)))
Proof
  simp[EVERY_DEF] >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `loc` >> simp[compile_assign_value_def] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  rpt (FIRST [CHANGED_TAC (simp[every_state_insts_return]),
              irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind >> conj_tac,
              irule ctorCallFreeRulesTheory.every_state_insts_bind >> conj_tac,
              gen_tac, disch_tac]) >>
  simp[every_state_insts_return, opcode_every_emit_op, opcode_every_emit_void,
      opcode_every_emit_inst] >>
  rpt IF_CASES_TAC >> simp[] >>
  rpt (FIRST [CHANGED_TAC (simp[every_state_insts_return, opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst]),
              irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind >> conj_tac,
              irule ctorCallFreeRulesTheory.every_state_insts_bind >> conj_tac,
              gen_tac, disch_tac]) >>
  rpt IF_CASES_TAC >> simp[every_state_insts_return, opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst]
QED

Theorem outcomes_free_store_slots_mutual:
  (!opc. MEM opc [ADD; MUL; ASSIGN; JMP; EQ; JNZ; ILOAD; DLOAD; MLOAD;
    SLOAD; TLOAD; CALLDATALOAD; ISTORE; INVALID; MSTORE; SSTORE; TSTORE;
    SHR; LT; ISZERO] ==> P opc) ==>
  (!ce src slot ty tr s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_store_slots ce src slot ty tr s)))) /\
  (!ce src slot members mo so tr s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_store_slots_members ce src slot members mo so tr s)))) /\
  (!ce src slot elem cnt tr s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_copy_elements_to_slots ce src slot elem cnt tr s))))
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  ho_match_mp_tac compile_store_slots_ind >> rpt strip_tac >>
  simp[Once compile_store_slots_def] >>
  rpt (FIRST [CHANGED_TAC (simp[every_state_insts_return, opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst,
    every_state_insts_fresh_id, every_state_insts_fresh_var, every_state_insts_fresh_label,
        every_state_insts_new_block, outcomes_free_lit_offset,
    outcomes_free_bytestring_word_count,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_slot_copies,
    SRULE [DISJ_IMP_THM, FORALL_AND_THM] outcomes_free_word_copy]),
    gen_tac, strip_tac, irule ctorCallFreeRulesTheory.every_state_insts_bind,
        irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind,
    conj_tac, IF_CASES_TAC,
    first_assum (fn th => irule th >> simp[] >> NO_TAC)]) >>
  Cases_on `ty` >> gvs[] >>
  TRY (rename1 `ArrayT elem kind` >> Cases_on `kind` >> gvs[]) >>
  rpt (FIRST [CHANGED_TAC (simp[every_state_insts_return, opcode_every_emit_op,
      opcode_every_emit_void, opcode_every_emit_inst]),
    gen_tac, strip_tac, irule ctorCallFreeRulesTheory.every_state_insts_bind,
        irule ctorCallFreeRulesTheory.every_state_insts_ignore_bind,
    conj_tac, first_assum (fn th => irule th >> simp[] >> NO_TAC)]) >>
  first_x_assum irule >> simp[]
QED

Theorem opcode_every_store_at_loc:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_store_at_loc imm dst value loc st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_compile_store_at_loc >>
  simp[UNDISCH opcode_every_imm_store_word]
QED

Theorem opcode_every_tuple_load_all:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  !tys ce src off st.
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_tuple_load_all ce src tys off st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_compile_tuple_load_all >> simp[] >>
  rpt strip_tac >> irule outcomes_free_load_memory >> simp[]
QED

Theorem opcode_every_declare_local:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (declare_local ce id ty st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_declare_local >> simp[]
QED

Theorem opcode_every_declare_stmt_local:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (declare_stmt_local ce s st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_declare_stmt_local >> simp[]
QED

Theorem opcode_every_emit_local_alloca:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (emit_local_alloca ce id st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_emit_local_alloca >> simp[]
QED

Theorem opcode_every_range_bound_checks:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_range_bound_checks start_op end_op rounds_op bound signed st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_range_bound_checks >> simp[]
QED

Theorem opcode_every_iter_elem_copy:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_iter_elem_copy ce src dst sz loc slots ty ety st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_iter_elem_copy >>
  simp[UNDISCH opcode_every_ptr_load, UNDISCH opcode_every_imm_copy_to_memory,
       UNDISCH opcode_every_copy_memory, UNDISCH opcode_every_store_memory] >>
  rpt strip_tac >> irule outcomes_free_slot_to_memory >>
  simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem opcode_every_imm_store_words:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  !n imm src dst off st.
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_imm_store_words imm src dst n off st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_imm_store_words >> simp[]
QED

Theorem opcode_every_store_immutable_bytestring[local]:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_store_immutable_bytestring imm src dst st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_store_immutable_bytestring >>
  simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem opcode_every_store_slots:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!cenv src slot ty transient st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_store_slots cenv src slot ty transient st)))) /\
  (!cenv src slot members mem_off slot_off transient st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_store_slots_members cenv src slot members
                           mem_off slot_off transient st)))) /\
  (!cenv src slot elem count_op transient st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_copy_elements_to_slots cenv src slot elem
                           count_op transient st))))
  )
Proof
  strip_tac >> irule outcomes_free_store_slots_mutual >> simp[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem opcode_every_assign_value:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_assign_value ce dst loc value prim src_loc dty sty sz st)))
  )
Proof
  rpt strip_tac >> irule outcomes_free_compile_assign_value >>
  simp[UNDISCH opcode_every_alloc_buffer, UNDISCH opcode_every_store_memory,
       cj 1 (UNDISCH opcode_every_typed_copy), UNDISCH opcode_every_copy_memory,
       cj 1 (UNDISCH opcode_every_store_slots), UNDISCH opcode_every_imm_store_word,
       UNDISCH opcode_every_store_immutable_bytestring,
       UNDISCH opcode_every_imm_store_words]
QED
