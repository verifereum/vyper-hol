(* Instruction witnesses for memory operations, independent of expression recursion. *)
Theory bodyIntCallFamCallIntEntryWitnessMemory
Ancestors
  bodyIntCallFamCallIntEntryCodeWitness context compileEnv exprLowering

Theorem entry_witness_imm_load_word:
  entry_code_witness st (SND (compile_imm_load_word ctor imm off st))
Proof
  Cases_on `ctor` >> Cases_on `imm` >>
  simp[compile_imm_load_word_def, entry_code_witness_emit_op] >>
  irule entry_code_witness_bind >> simp[entry_code_witness_emit_op]
QED

Theorem entry_witness_imm_store_word:
  entry_code_witness st (SND (compile_imm_store_word imm off v st))
Proof
  Cases_on `imm` >>
  simp[compile_imm_store_word_def, entry_code_witness_emit_void] >>
  irule entry_code_witness_bind >>
  simp[entry_code_witness_emit_op, entry_code_witness_emit_void]
QED

Theorem entry_witness_ptr_load:
  entry_code_witness st (SND (compile_ptr_load ctor imm loc op st))
Proof
  Cases_on `loc` >>
  simp[compile_ptr_load_def, entry_code_witness_emit_op,
    entry_witness_imm_load_word]
QED

Theorem entry_witness_ptr_store:
  entry_code_witness st (SND (compile_ptr_store ctor imm loc op v st))
Proof
  Cases_on `loc` >> Cases_on `ctor` >>
  simp[compile_ptr_store_def, entry_code_witness_emit_void,
    entry_witness_imm_store_word]
QED

Theorem entry_witness_copy_memory:
  entry_code_witness st (SND (compile_copy_memory dst src sz st))
Proof
  Cases_on `sz` >> simp[compile_copy_memory_def,
    entry_code_witness_return, entry_code_witness_emit_void]
QED

Theorem entry_witness_copy_memory_dynamic:
  entry_code_witness st (SND (compile_copy_memory_dynamic dst src sz st))
Proof
  simp[compile_copy_memory_dynamic_def, entry_code_witness_emit_void]
QED

Theorem entry_witness_lit_byte_offset:
  entry_code_witness st (SND (compile_lit_byte_offset op off st))
Proof
  simp[compile_lit_byte_offset_def] >>
  Cases_on `off = 0` >> simp[entry_code_witness_return] >>
  Cases_on `op` >> simp[entry_code_witness_return, entry_code_witness_emit_op]
QED

Theorem entry_witness_imm_copy_to_memory:
  !n ctor imm src dst off st.
    entry_code_witness st
      (SND (compile_imm_copy_to_memory ctor imm src dst n off st))
Proof
  Induct >> rpt gen_tac >>
  simp[compile_imm_copy_to_memory_def, entry_code_witness_return] >>
  irule entry_code_witness_bind >> simp[entry_witness_lit_byte_offset] >>
  rpt gen_tac >> irule entry_code_witness_bind >>
  simp[entry_witness_imm_load_word] >>
  rpt gen_tac >> irule entry_code_witness_bind >>
  simp[entry_witness_lit_byte_offset] >>
  rpt gen_tac >> irule entry_code_witness_ignore_bind >>
  simp[entry_code_witness_emit_void]
QED

Theorem entry_witness_imm_store_words:
  !n imm src dst off st.
    entry_code_witness st (SND (compile_imm_store_words imm src dst n off st))
Proof
  Induct >> rpt gen_tac >>
  simp[compile_imm_store_words_def, entry_code_witness_return] >>
  irule entry_code_witness_bind >> simp[entry_witness_lit_byte_offset] >>
  rpt gen_tac >> irule entry_code_witness_bind >>
  simp[entry_code_witness_emit_op] >>
  rpt gen_tac >> irule entry_code_witness_bind >>
  simp[entry_witness_lit_byte_offset] >>
  rpt gen_tac >> irule entry_code_witness_ignore_bind >>
  simp[entry_witness_imm_store_word]
QED

Theorem entry_witness_word_copy_loop:
  entry_code_witness st (SND (compile_word_copy_loop src dst wc ll sl ctor st))
Proof
  Cases_on `word_scale ll = 1` >> Cases_on `word_scale sl = 1` >>
  simp[compile_word_copy_loop_def, LET_THM] >>
  rpt ((irule entry_code_witness_bind ORELSE
        irule entry_code_witness_ignore_bind) >>
    simp[entry_code_witness_fresh_label, entry_code_witness_fresh_var,
      entry_code_witness_emit_inst, entry_code_witness_emit_op,
      entry_code_witness_new_block, entry_witness_ptr_load,
      entry_witness_ptr_store] >> rpt strip_tac)
QED

Theorem entry_witness_storage_to_memory:
  entry_code_witness st (SND (compile_storage_to_memory src dst wc st))
Proof
  simp[compile_storage_to_memory_def, entry_witness_word_copy_loop]
QED

Theorem entry_witness_transient_to_memory:
  entry_code_witness st (SND (compile_transient_to_memory src dst wc st))
Proof
  simp[compile_transient_to_memory_def, entry_witness_word_copy_loop]
QED

Theorem entry_witness_code_to_memory:
  entry_code_witness st (SND (compile_code_to_memory src dst wc st))
Proof
  simp[compile_code_to_memory_def] >> IF_CASES_TAC >>
  simp[entry_code_witness_return] >>
  irule entry_code_witness_ignore_bind >>
  simp[entry_witness_word_copy_loop, entry_code_witness_return]
QED

Theorem entry_witness_ensure_in_memory:
  entry_code_witness st
    (SND (compile_ensure_in_memory src loc sz wc ctor imm st))
Proof
  Cases_on `loc` >> Cases_on `wc = 1` >>
  simp[compile_ensure_in_memory_def, entry_code_witness_return] >>
  rpt ((irule entry_code_witness_bind ORELSE
        irule entry_code_witness_ignore_bind) >>
    simp[entry_code_witness_alloc_buffer, entry_code_witness_emit_op,
      entry_code_witness_emit_void, entry_code_witness_return,
      entry_witness_storage_to_memory, entry_witness_transient_to_memory,
      entry_witness_imm_copy_to_memory] >> rpt strip_tac)
QED

Theorem entry_witness_unwrap_value:
  entry_code_witness st (SND (unwrap_value ce vv st))
Proof
  Cases_on `vv` >> simp[unwrap_value_def, entry_code_witness_return] >>
  IF_CASES_TAC >> simp[entry_witness_ptr_load] >>
  Cases_on `p.ptr_location` >>
  simp[entry_code_witness_return, entry_witness_ensure_in_memory]
QED

Theorem entry_witness_as_stack_val:
  entry_code_witness st (SND result) ==>
  entry_code_witness st (SND (as_stack_val ty result))
Proof
  Cases_on `result` >> simp[as_stack_val_def]
QED

Theorem entry_witness_as_ptr_val:
  entry_code_witness st (SND result) ==>
  entry_code_witness st (SND (as_ptr_val ty loc result))
Proof
  Cases_on `result` >> simp[as_ptr_val_def]
QED

Theorem entry_witness_lower_value:
  (!s. entry_code_witness s (SND (f ce ty e s))) ==>
  entry_code_witness st (SND (lower_value f ce ty e st))
Proof
  strip_tac >> simp[lower_value_def] >>
  irule entry_code_witness_bind >> simp[entry_witness_unwrap_value]
QED

Theorem entry_witness_lower_value_with_loc:
  (!s. entry_code_witness s (SND (f ce ty e s))) ==>
  entry_code_witness st (SND (lower_value_with_loc f ce ty e st))
Proof
  strip_tac >> simp[lower_value_with_loc_def] >>
  irule entry_code_witness_bind >> simp[] >> rpt gen_tac >>
  irule entry_code_witness_bind >>
  simp[entry_witness_unwrap_value, entry_code_witness_return]
QED

Theorem entry_witness_bytestring_copy_len:
  entry_code_witness st (SND (compile_bytestring_copy_len src st))
Proof
  simp[compile_bytestring_copy_len_def] >>
  rpt (irule entry_code_witness_bind >>
    simp[entry_code_witness_emit_op] >> rpt gen_tac)
QED

Theorem entry_witness_store_bytestring:
  entry_code_witness st (SND (compile_store_bytestring src dst st))
Proof
  simp[compile_store_bytestring_def] >>
  irule entry_code_witness_bind >>
  simp[entry_witness_bytestring_copy_len, entry_code_witness_emit_void]
QED

Theorem entry_witness_with_byte_offset:
  entry_code_witness st (SND (compile_with_byte_offset src off st))
Proof
  simp[compile_with_byte_offset_def] >> IF_CASES_TAC >>
  simp[entry_code_witness_return, entry_code_witness_emit_op]
QED

Theorem entry_witness_typed_memory_family:
  (!ce dst dt src st. !s.
    entry_code_witness s (SND (compile_store_memory_typed ce dst dt src st s))) /\
  (!ce dst src dts sts doff soff s.
    entry_code_witness s
      (SND (compile_typed_copy_fields ce dst src dts sts doff soff s))) /\
  (!ce dst dt src st n s.
    entry_code_witness s (SND (compile_copy_sarray_typed ce dst dt src st n s))) /\
  (!ce dst dt cap src st s.
    entry_code_witness s (SND (compile_copy_dynarray_typed ce dst dt cap src st s))) /\
  (!ce dst src dfs sfs doff soff s.
    entry_code_witness s
      (SND (compile_struct_typed_copy ce dst src dfs sfs doff soff s)))
Proof
  ho_match_mp_tac compile_store_memory_typed_ind >>
  rpt conj_tac >> rpt strip_tac
  >~ [`compile_store_memory_typed ce dst dt src sty s`]
  >- (simp[Once compile_store_memory_typed_def] >>
      rpt IF_CASES_TAC >>
      simp[entry_witness_store_bytestring, entry_code_witness_emit_void]
      >~ [`emit_op MLOAD [src]`]
      >- (irule entry_code_witness_bind >>
          simp[entry_code_witness_emit_op, entry_code_witness_emit_void]) >>
      Cases_on `dt` >> Cases_on `sty` >>
      gvs[entry_witness_copy_memory] >>
      rename1 `case src_bound of Fixed _ => _ | Dynamic _ => _` >>
      Cases_on `src_bound` >>
      simp[entry_witness_copy_memory] >>
      qmatch_goalsub_rename_tac `type_memory_bytes ce (ArrayT elem dst_bound)` >>
      Cases_on `dst_bound` >> gvs[entry_witness_copy_memory]) >>
  simp[Once compile_store_memory_typed_def, entry_code_witness_return] >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt IF_CASES_TAC >> simp[entry_witness_copy_memory] >>
  rpt ((irule entry_code_witness_bind ORELSE
        irule entry_code_witness_ignore_bind) >>
    simp[entry_code_witness_emit_op, entry_code_witness_emit_void,
      entry_code_witness_emit_inst, entry_code_witness_fresh_label,
      entry_code_witness_fresh_var, entry_code_witness_new_block,
      entry_code_witness_return, entry_witness_with_byte_offset,
      entry_witness_copy_memory_dynamic] >> rpt strip_tac >>
    rpt IF_CASES_TAC) >>
  gvs[]
QED

Theorem entry_witness_store_memory:
  entry_code_witness s (SND (compile_store_memory ce src dst dt st s))
Proof
  simp[compile_store_memory_def] >> rpt IF_CASES_TAC >>
  simp[entry_code_witness_emit_void, entry_witness_store_bytestring,
    entry_witness_typed_memory_family, entry_witness_copy_memory]
QED
