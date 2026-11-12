Theory runtimeSymSrcDataContext
Ancestors
  runtimeSymSrcDataFrame context compileEnv emitHelper

Theorem runtime_data_frame_cond[simp]:
  runtime_data_frame (if b then m else n) <=>
  (if b then runtime_data_frame m else runtime_data_frame n)
Proof
  Cases_on `b` >> simp[]
QED

Theorem runtime_data_frame_imm_load[simp]:
  runtime_data_frame (compile_imm_load_word ctor imm off)
Proof
  Cases_on `imm` >> simp[compile_imm_load_word_def]
QED

Theorem runtime_data_frame_ptr_load[simp]:
  runtime_data_frame (compile_ptr_load ctor imm loc off)
Proof
  Cases_on `loc` >> simp[compile_ptr_load_def]
QED

Theorem runtime_data_frame_imm_store[simp]:
  runtime_data_frame (compile_imm_store_word imm off v)
Proof
  Cases_on `imm` >> simp[compile_imm_store_word_def]
QED

Theorem runtime_data_frame_ptr_store[simp]:
  runtime_data_frame (compile_ptr_store ctor imm loc off v)
Proof
  Cases_on `loc` >> simp[compile_ptr_store_def]
QED

Theorem runtime_data_frame_word_copy_base[simp]:
  runtime_data_frame (compile_word_copy_loop_base src dst n l s ctor imm)
Proof
  simp[compile_word_copy_loop_base_def, comp_ignore_bind_def] >>
  rpt (irule runtime_data_frame_bind >>
       reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem runtime_data_frame_alloc_buffer[simp]:
  runtime_data_frame (compile_alloc_buffer n)
Proof
  simp[compile_alloc_buffer_def]
QED

Theorem runtime_data_frame_alloc_dynamic[simp]:
  runtime_data_frame (compile_alloc_dynamic n)
Proof
  simp[compile_alloc_dynamic_def]
QED

Theorem runtime_data_frame_word_copy[simp]:
  runtime_data_frame (compile_word_copy_loop src dst n l s ctor)
Proof
  simp[compile_word_copy_loop_def, compile_word_copy_loop_op_def]
QED

Theorem runtime_data_frame_copy_memory[simp]:
  runtime_data_frame (compile_copy_memory dst src n)
Proof
  Cases_on `n` >> simp[compile_copy_memory_def]
QED

Theorem runtime_data_frame_zero_loop[simp]:
  !p i n. runtime_data_frame (compile_zero_memory_loop p i n)
Proof
  recInduct compile_zero_memory_loop_ind >> rpt strip_tac >>
  pure_once_rewrite_tac[compile_zero_memory_loop_def] >>
  IF_CASES_TAC >> simp[] >>
  rpt (irule runtime_data_frame_bind >>
       reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem runtime_data_frame_zero[simp]:
  runtime_data_frame (compile_zero_memory p n)
Proof
  Cases_on `n` >> simp[compile_zero_memory_def]
QED

Theorem runtime_data_frame_lit_offset[simp]:
  runtime_data_frame (compile_lit_byte_offset p n)
Proof
  Cases_on `p` >> simp[compile_lit_byte_offset_def]
QED

Theorem runtime_data_frame_imm_copy[simp]:
  !n off. runtime_data_frame (compile_imm_copy_to_memory ctor imm src dst n off)
Proof
  Induct >> simp[compile_imm_copy_to_memory_def]
QED

Theorem runtime_data_frame_imm_words[simp]:
  !n off. runtime_data_frame (compile_imm_store_words imm src dst n off)
Proof
  Induct >> simp[compile_imm_store_words_def]
QED

Theorem runtime_data_frame_byte_offset[simp]:
  runtime_data_frame (compile_with_byte_offset p n)
Proof
  simp[compile_with_byte_offset_def]
QED

Theorem runtime_data_frame_copy_dynamic[simp]:
  runtime_data_frame (compile_copy_memory_dynamic dst src n)
Proof
  simp[compile_copy_memory_dynamic_def]
QED

Theorem runtime_data_frame_bytestring_len[simp]:
  runtime_data_frame (compile_bytestring_copy_len p)
Proof
  simp[compile_bytestring_copy_len_def, comp_ignore_bind_def] >>
  rpt (irule runtime_data_frame_bind >>
       reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem runtime_data_frame_store_bytestring[simp]:
  runtime_data_frame (compile_store_bytestring src dst)
Proof
  simp[compile_store_bytestring_def]
QED

Theorem runtime_data_frame_typed_copy_mutual:
  (!cenv dst dt src st. runtime_data_frame (compile_store_memory_typed cenv dst dt src st)) /\
  (!cenv dst src dts sts doff soff. runtime_data_frame (compile_typed_copy_fields cenv dst src dts sts doff soff)) /\
  (!cenv dst dt src st n. runtime_data_frame (compile_copy_sarray_typed cenv dst dt src st n)) /\
  (!cenv dst dt cap src st. runtime_data_frame (compile_copy_dynarray_typed cenv dst dt cap src st)) /\
  (!cenv dst src dfs sfs doff soff. runtime_data_frame (compile_struct_typed_copy cenv dst src dfs sfs doff soff))
Proof
  ho_match_mp_tac compile_store_memory_typed_ind >> rpt strip_tac >>
  pure_once_rewrite_tac[compile_store_memory_typed_def] >>
  rpt (CHANGED_TAC (simp[comp_ignore_bind_def])) >>
  rpt (irule runtime_data_frame_bind >>
       reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC)
  >- (Cases_on `is_word_type dt` >> gvs[] >>
      Cases_on `is_bytestring_type dt /\ is_bytestring_type st` >> gvs[] >>
      Cases_on `acyclic_struct_metadata cenv.ce_struct_fields` >> gvs[] >>
      Cases_on `dt` >> Cases_on `st` >> gvs[] >>
      rpt (CASE_TAC >> gvs[]) >> metis_tac[])
  >- (Cases_on `type_memory_bytes cenv dt = type_memory_bytes cenv st /\ ~is_abi_dynamic cenv.ce_struct_fields dt` >> gvs[] >> disj2_tac >>
      rpt (irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >>
      simp[] >> metis_tac[])
  >- (IF_CASES_TAC >> gvs[] >>
      rpt (irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]) >>
  pairarg_tac >> gvs[] >>
  rpt (irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem runtime_data_frame_store_typed[simp]:
  runtime_data_frame (compile_store_memory_typed cenv dst dt src st)
Proof metis_tac[runtime_data_frame_typed_copy_mutual]
QED

Theorem runtime_data_frame_copy_fields[simp]:
  runtime_data_frame (compile_typed_copy_fields cenv dst src dts sts doff soff)
Proof metis_tac[runtime_data_frame_typed_copy_mutual]
QED

Theorem runtime_data_frame_copy_sarray[simp]:
  runtime_data_frame (compile_copy_sarray_typed cenv dst dt src st n)
Proof metis_tac[runtime_data_frame_typed_copy_mutual]
QED

Theorem runtime_data_frame_copy_dynarray[simp]:
  runtime_data_frame (compile_copy_dynarray_typed cenv dst dt cap src st)
Proof metis_tac[runtime_data_frame_typed_copy_mutual]
QED

Theorem runtime_data_frame_copy_struct[simp]:
  runtime_data_frame (compile_struct_typed_copy cenv dst src dfs sfs doff soff)
Proof metis_tac[runtime_data_frame_typed_copy_mutual]
QED

Theorem runtime_data_frame_store_memory[simp]:
  runtime_data_frame (compile_store_memory cenv src dst dt st)
Proof simp[compile_store_memory_def]
QED

Theorem runtime_data_frame_storage_copy[simp]:
  runtime_data_frame (compile_storage_to_memory src dst n) /\
  runtime_data_frame (compile_memory_to_storage src dst n) /\
  runtime_data_frame (compile_transient_to_memory src dst n) /\
  runtime_data_frame (compile_memory_to_transient src dst n)
Proof
  simp[compile_storage_to_memory_def, compile_memory_to_storage_def,
       compile_transient_to_memory_def, compile_memory_to_transient_def]
QED

Theorem runtime_data_frame_ensure_memory[simp]:
  runtime_data_frame (compile_ensure_in_memory p loc n wc ctor imm)
Proof
  Cases_on `loc` >> simp[compile_ensure_in_memory_def, comp_ignore_bind_def] >>
  rpt (irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem runtime_data_frame_load_memory[simp]:
  runtime_data_frame (compile_load_memory p b)
Proof simp[compile_load_memory_def]
QED

Theorem runtime_data_frame_load_calldata[simp]:
  runtime_data_frame (compile_load_calldata p b wc n)
Proof
  simp[compile_load_calldata_def, comp_ignore_bind_def] >>
  rpt (irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem runtime_data_frame_store_storage[simp]:
  runtime_data_frame (compile_store_storage v slot b n)
Proof
  simp[compile_store_storage_def, comp_ignore_bind_def] >>
  rpt (irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem runtime_data_frame_store_transient[simp]:
  runtime_data_frame (compile_store_transient v slot b n)
Proof
  simp[compile_store_transient_def, comp_ignore_bind_def] >>
  rpt (irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem runtime_data_frame_load_storage[simp]:
  runtime_data_frame (compile_load_storage slot b wc n)
Proof
  simp[compile_load_storage_def, comp_ignore_bind_def] >>
  rpt (irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem runtime_data_frame_load_transient[simp]:
  runtime_data_frame (compile_load_transient slot b wc n)
Proof
  simp[compile_load_transient_def, comp_ignore_bind_def] >>
  rpt (irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem runtime_data_frame_code_to_memory[simp]:
  runtime_data_frame (compile_code_to_memory off dst wc)
Proof
  simp[compile_code_to_memory_def]
QED

Theorem runtime_data_frame_load_immutable[simp]:
  runtime_data_frame (compile_load_immutable off b wc n ctor)
Proof
  simp[compile_load_immutable_def, comp_ignore_bind_def] >>
  rpt (irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem runtime_data_frame_fixed_region[simp]:
  runtime_data_frame (compile_fixed_region_with_id n)
Proof
  simp[compile_fixed_region_with_id_def]
QED

Theorem runtime_data_frame_bytes_word_count[simp]:
  runtime_data_frame (compile_bytestring_word_count src)
Proof
  simp[compile_bytestring_word_count_def]
QED

Theorem runtime_data_frame_store_immutable_bytes[simp]:
  runtime_data_frame (compile_store_immutable_bytestring imm src dst)
Proof
  simp[compile_store_immutable_bytestring_def]
QED

Theorem runtime_data_frame_nonreentrant_lock[simp]:
  runtime_data_frame (compile_nonreentrant_lock key trans view)
Proof
  simp[compile_nonreentrant_lock_def, comp_ignore_bind_def] >>
  rpt (irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem runtime_data_frame_nonreentrant_unlock[simp]:
  runtime_data_frame (compile_nonreentrant_unlock key trans view)
Proof
  simp[compile_nonreentrant_unlock_def]
QED

Theorem runtime_data_frame_bytes_data_ptr[simp]:
  runtime_data_frame (compile_bytes_data_ptr p loc)
Proof
  simp[compile_bytes_data_ptr_def]
QED

Theorem runtime_data_frame_bytestring_length[simp]:
  runtime_data_frame (compile_bytestring_length ctor imm p loc)
Proof
  simp[compile_bytestring_length_def]
QED

Theorem runtime_data_frame_slot_to_memory[simp]:
  runtime_data_frame (compile_slot_to_memory src dst n loc)
Proof
  simp[compile_slot_to_memory_def]
QED

Theorem runtime_data_frame_store_immutable[simp]:
  runtime_data_frame (compile_store_immutable imm src dst n)
Proof
  simp[compile_store_immutable_def]
QED

Theorem runtime_data_frame_dynarray_storage[simp]:
  runtime_data_frame (compile_dynarray_to_storage src dst ew es trans)
Proof
  simp[compile_dynarray_to_storage_def, comp_ignore_bind_def] >>
  rpt (irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >>
  Cases_on `ew = 1` >> simp[] >>
  rpt (irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem runtime_data_frame_iload_memory[simp]:
  !n. runtime_data_frame (compile_iload_to_memory src dst n)
Proof
  Induct >> simp[compile_iload_to_memory_def]
QED

Theorem runtime_data_frame_gep_memory[simp]:
  !n. runtime_data_frame (compile_gep_to_memory bp src dst n)
Proof
  Induct >> simp[compile_gep_to_memory_def, comp_ignore_bind_def] >>
  rpt (irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem runtime_data_frame_load_immutable_ctor[simp]:
  runtime_data_frame (compile_load_immutable_ctor off b wc n imm)
Proof
  Cases_on `imm` >> simp[compile_load_immutable_ctor_def, comp_ignore_bind_def] >>
  rpt (irule runtime_data_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem runtime_data_frame_encode_log_topic[simp]:
  runtime_data_frame (compile_encode_log_topic v b)
Proof
  simp[compile_encode_log_topic_def]
QED
