Theory runtimeSymSrcDataContext
Ancestors
  symbolicSourceCompilerCopyFrame
  runtimeSymSrcDataFrame context compileEnv emitHelper

fun specialize_frame theorem =
  REWRITE_RULE [symbolic_frame_runtime]
    (Q.ISPEC `\data (s:compile_state) t. s = t /\ s.cs_data_sections = data` (Q.GEN `R` theorem))

fun apply_symbolic_frame theorem = match_mp_tac (specialize_frame theorem)

Theorem runtime_data_frame_cond[simp]:
  runtime_data_frame (if b then m else n) <=>
  (if b then runtime_data_frame m else runtime_data_frame n)
Proof
  REWRITE_TAC [specialize_frame symbolic_frame_cond]
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
  apply_symbolic_frame symbolic_frame_zero_loop >> simp[]
QED

Theorem runtime_data_frame_zero[simp]:
  runtime_data_frame (compile_zero_memory p n)
Proof
  apply_symbolic_frame symbolic_frame_zero >> simp[]
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
  match_mp_tac (REWRITE_RULE [symbolic_frame_runtime]
    (Q.ISPEC `\data (s:compile_state) t. s = t /\ s.cs_data_sections = data`
      (Q.GEN `R` symbolic_frame_typed_copy_mutual))) >>
  simp[]
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
  apply_symbolic_frame symbolic_frame_ensure_memory >> simp[]
QED

Theorem runtime_data_frame_load_memory[simp]:
  runtime_data_frame (compile_load_memory p b)
Proof
  apply_symbolic_frame symbolic_frame_load_memory >> simp[]
QED

Theorem runtime_data_frame_load_calldata[simp]:
  runtime_data_frame (compile_load_calldata p b wc n)
Proof
  apply_symbolic_frame symbolic_frame_load_calldata >> simp[]
QED


Theorem runtime_data_frame_load_storage[simp]:
  runtime_data_frame (compile_load_storage slot b wc n)
Proof
  apply_symbolic_frame symbolic_frame_load_storage >> simp[]
QED

Theorem runtime_data_frame_load_transient[simp]:
  runtime_data_frame (compile_load_transient slot b wc n)
Proof
  apply_symbolic_frame symbolic_frame_load_transient >> simp[]
QED

Theorem runtime_data_frame_code_to_memory[simp]:
  runtime_data_frame (compile_code_to_memory off dst wc)
Proof
  simp[compile_code_to_memory_def]
QED

Theorem runtime_data_frame_load_immutable[simp]:
  runtime_data_frame (compile_load_immutable off b wc n ctor)
Proof
  apply_symbolic_frame symbolic_frame_load_immutable >> simp[]
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

Theorem runtime_data_frame_store_slots[simp]:
  (!cenv src slot ty trans.
    runtime_data_frame (compile_store_slots cenv src slot ty trans)) /\
  (!cenv src slot members mo so trans.
    runtime_data_frame (compile_store_slots_members cenv src slot members mo so trans)) /\
  (!cenv src slot elem count trans.
    runtime_data_frame (compile_copy_elements_to_slots cenv src slot elem count trans))
Proof
  apply_symbolic_frame symbolic_frame_store_slots >> simp[]
QED

Theorem runtime_data_frame_iload_memory[simp]:
  !n. runtime_data_frame (compile_iload_to_memory src dst n)
Proof
  apply_symbolic_frame symbolic_frame_iload_memory >> simp[]
QED

Theorem runtime_data_frame_gep_memory[simp]:
  !n. runtime_data_frame (compile_gep_to_memory bp src dst n)
Proof
  apply_symbolic_frame symbolic_frame_gep_memory >> simp[]
QED

Theorem runtime_data_frame_load_immutable_ctor[simp]:
  runtime_data_frame (compile_load_immutable_ctor off b wc n imm)
Proof
  apply_symbolic_frame symbolic_frame_load_immutable_ctor >> simp[]
QED

Theorem runtime_data_frame_encode_log_topic[simp]:
  runtime_data_frame (compile_encode_log_topic v b)
Proof
  simp[compile_encode_log_topic_def]
QED
