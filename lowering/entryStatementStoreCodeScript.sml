Theory entryStatementStoreCode
Ancestors
  entryCodePredicate entryContextCodePredicate entryTypedCopyCode
  entryAggregateCode entryValueCode entryLocationValueCode stmtLowering context compileEnv

Theorem entry_code_imm_store_words[local]:
  !n off. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_imm_store_words imm src dst n off)
Proof
  Induct >> simp[compile_imm_store_words_def, comp_ignore_bind_def,
                 entry_code_return] >> rpt gen_tac >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_lit_byte_offset, entry_code_emit_op, entry_code_imm_store] >>
    rpt gen_tac >> BETA_TAC) >> simp[]
QED

Theorem entry_code_dynarray_to_storage[local]:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_dynarray_to_storage src dst ew ems transient)
Proof
  Cases_on `transient` >> Cases_on `ew = 1` >>
  simp[compile_dynarray_to_storage_def, comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_emit_void, entry_code_emit_inst,
            entry_code_fresh_var, entry_code_fresh_label, entry_code_new_block,
            entry_code_word_copy_loop] >> rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_emit_void]
QED

Theorem entry_code_store_at_loc:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_store_at_loc imm dst value loc)
Proof
  Cases_on `loc` >- simp[compile_store_at_loc_def, entry_code_emit_void] >>
  Cases_on `x` >> simp[compile_store_at_loc_def, entry_code_emit_void,
                       entry_code_imm_store]
QED

Theorem entry_code_declare_local:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (declare_local ce id ty)
Proof
  simp[declare_local_def] >> IF_CASES_TAC >> simp[entry_code_return] >>
  irule entry_code_bind >> simp[entry_code_fresh_var, entry_code_return]
QED

Theorem entry_code_declare_stmt_local:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (declare_stmt_local ce s)
Proof
  Cases_on `s` >> simp[declare_stmt_local_def, entry_code_declare_local,
                       entry_code_return]
QED

Theorem entry_code_emit_local_alloca:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (emit_local_alloca ce id)
Proof
  simp[emit_local_alloca_def] >>
  Cases_on `FLOOKUP ce.ce_vars id` >> simp[entry_code_return] >>
  Cases_on `x` >> simp[entry_code_return] >>
  Cases_on `o'` >>
  simp[entry_code_return, entry_code_emit_inst]
QED

Theorem entry_code_assignment_normalize[local]:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (do buf <- compile_alloc_buffer memsz;
        compile_store_memory_typed ce buf.buf_operand dt value st;
        return buf.buf_operand od)
Proof
  simp[comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_alloc_buffer, entry_code_store_memory_typed] >>
    rpt gen_tac >> BETA_TAC) >> simp[entry_code_return]
QED

Theorem entry_code_assign_value:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_assign_value ce dst loc value prim sl dt st da memsz)
Proof
  Cases_on `da` >> Cases_on `loc` >>
  simp[compile_assign_value_def] >> rpt IF_CASES_TAC >>
  simp[entry_code_emit_void, entry_code_store_memory, comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[SRULE [comp_ignore_bind_def] entry_code_assignment_normalize, entry_code_alloc_buffer,
            entry_code_copy_memory, entry_code_return, entry_code_emit_op,
            entry_code_memory_to_storage, entry_code_memory_to_transient,
            entry_code_emit_inst] >> rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_emit_void, entry_code_store_memory, entry_code_imm_store,
       entry_code_return, entry_code_imm_store_words] >>
  rpt IF_CASES_TAC >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_memory_to_storage,
            entry_code_memory_to_transient] >> rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_emit_void, entry_code_return, entry_code_imm_store,
       entry_code_imm_store_words] >>
  PairCases_on `x` >> simp[entry_code_dynarray_to_storage]
QED

Theorem entry_code_tuple_load_all:
  !tys offset. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_tuple_load_all ce src tys offset)
Proof
  Induct >> simp[compile_tuple_load_all_def, entry_code_return] >>
  rpt gen_tac >> Cases_on `is_word_type h` >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, compile_load_memory_def, entry_code_return] >>
    rpt gen_tac >> BETA_TAC) >> simp[entry_code_return]
QED

Theorem entry_code_tuple_store_all:
  !tys targets vals ce.
    (!bt e ce' et. MEM (BaseTarget bt) targets /\ MEM e (target_indices bt) ==>
      entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
        (compile_expr ce' et e)) ==>
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
      (compile_tuple_store_all ce tys targets vals)
Proof
  Induct >> namedCases_on `targets` ["", "target rest"] >> Cases_on `vals` >>
  simp[compile_tuple_store_all_def, entry_code_return] >>
  Cases_on `target` >> rpt strip_tac >>
  simp[compile_tuple_store_all_def, comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- (simp[entry_code_emit_void, entry_code_return] >>
        irule entry_code_get_target_ptr >> metis_tac[listTheory.MEM]) >>
    rpt gen_tac >> BETA_TAC) >>
  rpt IF_CASES_TAC >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_store_at_loc, entry_code_assign_value, entry_code_emit_void] >>
    rpt gen_tac >> BETA_TAC) >>
  first_x_assum irule >> metis_tac[listTheory.MEM]
QED

Theorem entry_code_tuple_unpack:
  (!bt e ce' et. MEM (BaseTarget bt) targets /\ MEM e (target_indices bt) ==>
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
      (compile_expr ce' et e)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_tuple_unpack ce ty stage targets src)
Proof
  strip_tac >> simp[compile_tuple_unpack_def] >>
  rpt IF_CASES_TAC >> simp[entry_code_emit_inst, comp_ignore_bind_def] >>
  (irule entry_code_bind >> reverse conj_tac
  >- (simp[entry_code_return] >>
      rpt (irule entry_code_bind >> reverse conj_tac
        >- simp[entry_code_alloc_buffer, entry_code_return, entry_code_emit_void] >>
        rpt gen_tac >> BETA_TAC) >> simp[entry_code_return]) >>
  rpt gen_tac >> BETA_TAC >>
  irule entry_code_bind >> reverse conj_tac >- simp[entry_code_tuple_load_all] >>
  rpt gen_tac >> BETA_TAC >> irule entry_code_tuple_store_all >> metis_tac[])
QED
