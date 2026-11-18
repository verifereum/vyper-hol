Theory deploySymSrcFrameContext
Ancestors
  symbolicSourceCompilerCopyFrame symbolicSourceCompilerFrame
  deploySymSrcBlockFrame context compileEnv emitHelper

fun specialize_frame theorem =
  REWRITE_RULE [symbolic_frame_deploy]
    (Q.ISPEC `\blocks (s:compile_state) t. t = s with cs_blocks := s.cs_blocks ++ blocks` (Q.GEN `R` theorem))

fun apply_symbolic_frame theorem = match_mp_tac (specialize_frame theorem)

Theorem deploy_blocks_frame_cond[simp]:
  deploy_blocks_frame (if b then m else n) <=>
  (if b then deploy_blocks_frame m else deploy_blocks_frame n)
Proof
  REWRITE_TAC [specialize_frame symbolic_frame_cond]
QED

(* These compositional rules are local simplifier rules, not new axioms. *)
val _ = augment_srw_ss [rewrites [deploy_blocks_frame_bind,
                                deploy_blocks_frame_ignore_bind]];

Theorem deploy_blocks_frame_fresh_vars[simp]:
  !n. deploy_blocks_frame (fresh_vars n)
Proof
  apply_symbolic_frame symbolic_frame_fresh_vars >> simp[]
QED

Theorem deploy_blocks_frame_emit_multi_op[simp]:
  deploy_blocks_frame (emit_multi_op opc ops n)
Proof
  apply_symbolic_frame symbolic_frame_emit_multi_op >> simp[]
QED

Theorem deploy_blocks_frame_imm_load[simp]:
  deploy_blocks_frame (compile_imm_load_word ctor imm off)
Proof
  apply_symbolic_frame symbolic_frame_imm_load >> simp[]
QED

Theorem deploy_blocks_frame_ptr_load[simp]:
  deploy_blocks_frame (compile_ptr_load ctor imm loc off)
Proof
  apply_symbolic_frame symbolic_frame_ptr_load >> simp[]
QED

Theorem deploy_blocks_frame_imm_store[simp]:
  deploy_blocks_frame (compile_imm_store_word imm off v)
Proof
  apply_symbolic_frame symbolic_frame_imm_store >> simp[]
QED

Theorem deploy_blocks_frame_ptr_store[simp]:
  deploy_blocks_frame (compile_ptr_store ctor imm loc off v)
Proof
  apply_symbolic_frame symbolic_frame_ptr_store >> simp[]
QED

Theorem deploy_blocks_frame_word_copy_base[simp]:
  deploy_blocks_frame (compile_word_copy_loop_base src dst n l s ctor imm)
Proof
  apply_symbolic_frame symbolic_frame_word_copy_base >> simp[]
QED

Theorem deploy_blocks_frame_alloc_dynamic[simp]:
  deploy_blocks_frame (compile_alloc_dynamic n)
Proof
  apply_symbolic_frame symbolic_frame_alloc_dynamic >> simp[]
QED

Theorem deploy_blocks_frame_word_copy[simp]:
  deploy_blocks_frame (compile_word_copy_loop src dst n l s ctor)
Proof
  apply_symbolic_frame symbolic_frame_word_copy >> simp[]
QED

Theorem deploy_blocks_frame_copy_memory[simp]:
  deploy_blocks_frame (compile_copy_memory dst src n)
Proof
  apply_symbolic_frame symbolic_frame_copy_memory >> simp[]
QED

Theorem deploy_blocks_frame_zero_loop[simp]:
  !p i n. deploy_blocks_frame (compile_zero_memory_loop p i n)
Proof
  apply_symbolic_frame symbolic_frame_zero_loop >> simp[]
QED

Theorem deploy_blocks_frame_zero[simp]:
  deploy_blocks_frame (compile_zero_memory p n)
Proof
  apply_symbolic_frame symbolic_frame_zero >> simp[]
QED

Theorem deploy_blocks_frame_lit_offset[simp]:
  deploy_blocks_frame (compile_lit_byte_offset p n)
Proof
  apply_symbolic_frame symbolic_frame_lit_offset >> simp[]
QED

Theorem deploy_blocks_frame_imm_copy[simp]:
  !n off. deploy_blocks_frame (compile_imm_copy_to_memory ctor imm src dst n off)
Proof
  apply_symbolic_frame symbolic_frame_imm_copy >> simp[]
QED

Theorem deploy_blocks_frame_imm_words[simp]:
  !n off. deploy_blocks_frame (compile_imm_store_words imm src dst n off)
Proof
  apply_symbolic_frame symbolic_frame_imm_words >> simp[]
QED

Theorem deploy_blocks_frame_byte_offset[simp]:
  deploy_blocks_frame (compile_with_byte_offset p n)
Proof
  apply_symbolic_frame symbolic_frame_byte_offset >> simp[]
QED

Theorem deploy_blocks_frame_copy_dynamic[simp]:
  deploy_blocks_frame (compile_copy_memory_dynamic dst src n)
Proof
  apply_symbolic_frame symbolic_frame_copy_dynamic >> simp[]
QED

Theorem deploy_blocks_frame_bytestring_len[simp]:
  deploy_blocks_frame (compile_bytestring_copy_len p)
Proof
  apply_symbolic_frame symbolic_frame_bytestring_len >> simp[]
QED

Theorem deploy_blocks_frame_store_bytestring[simp]:
  deploy_blocks_frame (compile_store_bytestring src dst)
Proof
  apply_symbolic_frame symbolic_frame_store_bytestring >> simp[]
QED

Theorem deploy_blocks_frame_typed_copy_mutual:
  (!cenv dst dt src st. deploy_blocks_frame (compile_store_memory_typed cenv dst dt src st)) /\
  (!cenv dst src dts sts doff soff. deploy_blocks_frame (compile_typed_copy_fields cenv dst src dts sts doff soff)) /\
  (!cenv dst dt src st n. deploy_blocks_frame (compile_copy_sarray_typed cenv dst dt src st n)) /\
  (!cenv dst dt cap src st. deploy_blocks_frame (compile_copy_dynarray_typed cenv dst dt cap src st)) /\
  (!cenv dst src dfs sfs doff soff. deploy_blocks_frame (compile_struct_typed_copy cenv dst src dfs sfs doff soff))
Proof
  match_mp_tac (REWRITE_RULE [symbolic_frame_deploy]
    (Q.ISPEC `\blocks (s:compile_state) t. t = s with cs_blocks := s.cs_blocks ++ blocks`
      (Q.GEN `R` symbolic_frame_typed_copy_mutual))) >>
  simp[]
QED

Theorem deploy_blocks_frame_store_typed[simp]:
  deploy_blocks_frame (compile_store_memory_typed cenv dst dt src st)
Proof metis_tac[deploy_blocks_frame_typed_copy_mutual]
QED

Theorem deploy_blocks_frame_copy_fields[simp]:
  deploy_blocks_frame (compile_typed_copy_fields cenv dst src dts sts doff soff)
Proof metis_tac[deploy_blocks_frame_typed_copy_mutual]
QED

Theorem deploy_blocks_frame_copy_sarray[simp]:
  deploy_blocks_frame (compile_copy_sarray_typed cenv dst dt src st n)
Proof metis_tac[deploy_blocks_frame_typed_copy_mutual]
QED

Theorem deploy_blocks_frame_copy_dynarray[simp]:
  deploy_blocks_frame (compile_copy_dynarray_typed cenv dst dt cap src st)
Proof metis_tac[deploy_blocks_frame_typed_copy_mutual]
QED

Theorem deploy_blocks_frame_copy_struct[simp]:
  deploy_blocks_frame (compile_struct_typed_copy cenv dst src dfs sfs doff soff)
Proof metis_tac[deploy_blocks_frame_typed_copy_mutual]
QED

Theorem deploy_blocks_frame_store_memory[simp]:
  deploy_blocks_frame (compile_store_memory cenv src dst dt st)
Proof
  apply_symbolic_frame symbolic_frame_store_memory >> simp[]
QED

Theorem deploy_blocks_frame_storage_copy[simp]:
  deploy_blocks_frame (compile_storage_to_memory src dst n) /\
  deploy_blocks_frame (compile_memory_to_storage src dst n) /\
  deploy_blocks_frame (compile_transient_to_memory src dst n) /\
  deploy_blocks_frame (compile_memory_to_transient src dst n)
Proof
  apply_symbolic_frame symbolic_frame_storage_copy >> simp[]
QED

Theorem deploy_blocks_frame_ensure_memory[simp]:
  deploy_blocks_frame (compile_ensure_in_memory p loc n wc ctor imm)
Proof
  apply_symbolic_frame symbolic_frame_ensure_memory >> simp[]
QED

Theorem deploy_blocks_frame_load_memory[simp]:
  deploy_blocks_frame (compile_load_memory p b)
Proof
  apply_symbolic_frame symbolic_frame_load_memory >> simp[]
QED

Theorem deploy_blocks_frame_load_calldata[simp]:
  deploy_blocks_frame (compile_load_calldata p b wc n)
Proof
  apply_symbolic_frame symbolic_frame_load_calldata >> simp[]
QED

Theorem deploy_blocks_frame_load_storage[simp]:
  deploy_blocks_frame (compile_load_storage slot b wc n)
Proof
  apply_symbolic_frame symbolic_frame_load_storage >> simp[]
QED

Theorem deploy_blocks_frame_load_transient[simp]:
  deploy_blocks_frame (compile_load_transient slot b wc n)
Proof
  apply_symbolic_frame symbolic_frame_load_transient >> simp[]
QED

Theorem deploy_blocks_frame_code_to_memory[simp]:
  deploy_blocks_frame (compile_code_to_memory off dst wc)
Proof
  apply_symbolic_frame symbolic_frame_code_to_memory >> simp[]
QED

Theorem deploy_blocks_frame_load_immutable[simp]:
  deploy_blocks_frame (compile_load_immutable off b wc n ctor)
Proof
  apply_symbolic_frame symbolic_frame_load_immutable >> simp[]
QED

Theorem deploy_blocks_frame_fixed_region[simp]:
  deploy_blocks_frame (compile_fixed_region_with_id n)
Proof
  apply_symbolic_frame symbolic_frame_fixed_region >> simp[]
QED

Theorem deploy_blocks_frame_bytes_word_count[simp]:
  deploy_blocks_frame (compile_bytestring_word_count src)
Proof
  apply_symbolic_frame symbolic_frame_bytes_word_count >> simp[]
QED

Theorem deploy_blocks_frame_store_immutable_bytes[simp]:
  deploy_blocks_frame (compile_store_immutable_bytestring imm src dst)
Proof
  apply_symbolic_frame symbolic_frame_store_immutable_bytes >> simp[]
QED

Theorem deploy_blocks_frame_nonreentrant_lock[simp]:
  deploy_blocks_frame (compile_nonreentrant_lock key trans view)
Proof
  apply_symbolic_frame symbolic_frame_nonreentrant_lock >> simp[]
QED

Theorem deploy_blocks_frame_nonreentrant_unlock[simp]:
  deploy_blocks_frame (compile_nonreentrant_unlock key trans view)
Proof
  apply_symbolic_frame symbolic_frame_nonreentrant_unlock >> simp[]
QED

Theorem deploy_blocks_frame_bytes_data_ptr[simp]:
  deploy_blocks_frame (compile_bytes_data_ptr p loc)
Proof
  apply_symbolic_frame symbolic_frame_bytes_data_ptr >> simp[]
QED

Theorem deploy_blocks_frame_bytestring_length[simp]:
  deploy_blocks_frame (compile_bytestring_length ctor imm p loc)
Proof
  apply_symbolic_frame symbolic_frame_bytestring_length >> simp[]
QED

Theorem deploy_blocks_frame_slot_to_memory[simp]:
  deploy_blocks_frame (compile_slot_to_memory src dst n loc)
Proof
  apply_symbolic_frame symbolic_frame_slot_to_memory >> simp[]
QED

Theorem deploy_blocks_frame_store_immutable[simp]:
  deploy_blocks_frame (compile_store_immutable imm src dst n)
Proof
  apply_symbolic_frame symbolic_frame_store_immutable >> simp[]
QED

Theorem deploy_blocks_frame_store_slots[simp]:
  (!cenv src slot ty trans.
    deploy_blocks_frame (compile_store_slots cenv src slot ty trans)) /\
  (!cenv src slot members mo so trans.
    deploy_blocks_frame (compile_store_slots_members cenv src slot members mo so trans)) /\
  (!cenv src slot elem count trans.
    deploy_blocks_frame (compile_copy_elements_to_slots cenv src slot elem count trans))
Proof
  apply_symbolic_frame symbolic_frame_store_slots >> simp[]
QED

Theorem deploy_blocks_frame_iload_memory[simp]:
  !n. deploy_blocks_frame (compile_iload_to_memory src dst n)
Proof
  apply_symbolic_frame symbolic_frame_iload_memory >> simp[]
QED

Theorem deploy_blocks_frame_gep_memory[simp]:
  !n. deploy_blocks_frame (compile_gep_to_memory bp src dst n)
Proof
  apply_symbolic_frame symbolic_frame_gep_memory >> simp[]
QED

Theorem deploy_blocks_frame_load_immutable_ctor[simp]:
  deploy_blocks_frame (compile_load_immutable_ctor off b wc n imm)
Proof
  apply_symbolic_frame symbolic_frame_load_immutable_ctor >> simp[]
QED

Theorem deploy_blocks_frame_encode_log_topic[simp]:
  deploy_blocks_frame (compile_encode_log_topic v b)
Proof
  apply_symbolic_frame symbolic_frame_encode_log_topic >> simp[]
QED
