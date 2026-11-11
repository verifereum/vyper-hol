(* Callback-free memory-operation correspondence, built bottom-up. *)
Theory gasShadowCompileContext
Ancestors
  gasShadowCompileBase gasShadowState context compileEnv emitHelper venomInst list

Theorem gas_shadow_compiles_emit_op_same[simp]:
  gas_shadow_compiles (emit_op opc ops) (emit_op opc ops)
Proof
  irule gas_shadow_compiles_emit_op >> simp[]
QED

Theorem gas_shadow_compiles_imm_load_word:
  gas_shadow_compiles (compile_imm_load_word is_ctor imm off)
    (compile_imm_load_word is_ctor imm off)
Proof
  Cases_on `is_ctor` >> Cases_on `imm` >>
  simp[compile_imm_load_word_def, gas_shadow_compiles_bind]
QED

Theorem gas_shadow_compiles_imm_store_word:
  gas_shadow_compiles (compile_imm_store_word imm off v)
    (compile_imm_store_word imm off v)
Proof
  Cases_on `imm` >>
  simp[compile_imm_store_word_def, gas_shadow_compiles_bind,
       gas_shadow_compiles_emit_void]
QED

Theorem gas_shadow_compiles_ptr_load:
  gas_shadow_compiles (compile_ptr_load is_ctor imm loc op)
    (compile_ptr_load is_ctor imm loc op)
Proof
  Cases_on `loc` >>
  simp[compile_ptr_load_def, gas_shadow_compiles_imm_load_word]
QED

Theorem gas_shadow_compiles_ptr_store:
  gas_shadow_compiles (compile_ptr_store is_ctor imm loc dst v)
    (compile_ptr_store is_ctor imm loc dst v)
Proof
  Cases_on `loc` >> Cases_on `is_ctor` >>
  simp[compile_ptr_store_def, gas_shadow_compiles_imm_store_word,
       gas_shadow_compiles_emit_void]
QED

Theorem gas_shadow_compiles_copy_memory:
  gas_shadow_compiles (compile_copy_memory dst src nbytes)
    (compile_copy_memory dst src nbytes)
Proof
  Cases_on `nbytes` >> simp[compile_copy_memory_def,
    gas_shadow_compiles_return, gas_shadow_compiles_emit_void]
QED

Theorem gas_shadow_compiles_alloc_buffer:
  gas_shadow_compiles (compile_alloc_buffer nbytes) (compile_alloc_buffer nbytes)
Proof
  simp[compile_alloc_buffer_def, gas_shadow_compiles_bind,
       gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_alloc_dynamic:
  gas_shadow_compiles (compile_alloc_dynamic nbytes_op) (compile_alloc_dynamic nbytes_op)
Proof
  simp[compile_alloc_dynamic_def]
QED


Theorem gas_shadow_compiles_word_copy_loop:
  gas_shadow_compiles
    (compile_word_copy_loop src dst word_count load_loc store_loc is_ctor)
    (compile_word_copy_loop src dst word_count load_loc store_loc is_ctor)
Proof
  Cases_on `word_scale load_loc = 1` >>
  Cases_on `word_scale store_loc = 1` >>
  pure_rewrite_tac[compile_word_copy_loop_def, LET_THM] >> BETA_TAC >>
  asm_rewrite_tac[] >>
  rewrite_tac[comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_bind,
               gas_shadow_compiles_fresh_label,
               gas_shadow_compiles_fresh_var,
               gas_shadow_compiles_emit_inst,
               gas_shadow_compiles_new_block,
               gas_shadow_compiles_ptr_load,
               gas_shadow_compiles_ptr_store]
       >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_new_block]
QED

Theorem gas_shadow_compiles_storage_to_memory:
  gas_shadow_compiles (compile_storage_to_memory slot buf n)
    (compile_storage_to_memory slot buf n)
Proof
  simp[compile_storage_to_memory_def, gas_shadow_compiles_word_copy_loop]
QED

Theorem gas_shadow_compiles_memory_to_storage:
  gas_shadow_compiles (compile_memory_to_storage buf slot n)
    (compile_memory_to_storage buf slot n)
Proof
  simp[compile_memory_to_storage_def, gas_shadow_compiles_word_copy_loop]
QED

Theorem gas_shadow_compiles_transient_to_memory:
  gas_shadow_compiles (compile_transient_to_memory slot buf n)
    (compile_transient_to_memory slot buf n)
Proof
  simp[compile_transient_to_memory_def, gas_shadow_compiles_word_copy_loop]
QED

Theorem gas_shadow_compiles_memory_to_transient:
  gas_shadow_compiles (compile_memory_to_transient buf slot n)
    (compile_memory_to_transient buf slot n)
Proof
  simp[compile_memory_to_transient_def, gas_shadow_compiles_word_copy_loop]
QED

Theorem gas_shadow_compiles_load_storage:
  gas_shadow_compiles (compile_load_storage slot prim n sz)
    (compile_load_storage slot prim n sz)
Proof
  Cases_on `prim` >> Cases_on `n = 1` >>
  simp[compile_load_storage_def, LET_THM, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_alloc_buffer,
               gas_shadow_compiles_emit_void,
               gas_shadow_compiles_storage_to_memory]
       >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_load_transient:
  gas_shadow_compiles (compile_load_transient slot prim n sz)
    (compile_load_transient slot prim n sz)
Proof
  Cases_on `prim` >> Cases_on `n = 1` >>
  simp[compile_load_transient_def, LET_THM, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_alloc_buffer,
               gas_shadow_compiles_emit_void,
               gas_shadow_compiles_transient_to_memory]
       >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_code_to_memory:
  gas_shadow_compiles (compile_code_to_memory off dst n)
    (compile_code_to_memory off dst n)
Proof
  Cases_on `n = 0` >>
  simp[compile_code_to_memory_def, comp_ignore_bind_def,
       gas_shadow_compiles_bind, gas_shadow_compiles_word_copy_loop,
       gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_load_immutable:
  gas_shadow_compiles (compile_load_immutable off prim n sz ctor)
    (compile_load_immutable off prim n sz ctor)
Proof
  Cases_on `prim` >> Cases_on `ctor` >>
  simp[compile_load_immutable_def, LET_THM, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_alloc_buffer,
               gas_shadow_compiles_code_to_memory]
       >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_zero_memory_loop:
  !ptr_op i n. gas_shadow_compiles (compile_zero_memory_loop ptr_op i n)
    (compile_zero_memory_loop ptr_op i n)
Proof
  recInduct compile_zero_memory_loop_ind >> rpt strip_tac >>
  once_rewrite_tac[compile_zero_memory_loop_def] >>
  Cases_on `i >= words` >- simp[gas_shadow_compiles_return] >>
  Cases_on `i = 0` >>
  simp[comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_return, gas_shadow_compiles_emit_void]
       >> gen_tac >> BETA_TAC) >>
  gvs[gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_zero_memory:
  gas_shadow_compiles (compile_zero_memory ptr_op sz) (compile_zero_memory ptr_op sz)
Proof
  Cases_on `sz` >> simp[compile_zero_memory_def,
    gas_shadow_compiles_return, gas_shadow_compiles_zero_memory_loop]
QED

Theorem gas_shadow_compiles_bytes_data_ptr:
  gas_shadow_compiles (compile_bytes_data_ptr ptr_op loc) (compile_bytes_data_ptr ptr_op loc)
Proof
  simp[compile_bytes_data_ptr_def]
QED

Theorem gas_shadow_compiles_bytestring_length:
  gas_shadow_compiles (compile_bytestring_length ctor imm ptr_op loc)
    (compile_bytestring_length ctor imm ptr_op loc)
Proof
  simp[compile_bytestring_length_def, gas_shadow_compiles_ptr_load]
QED

Theorem gas_shadow_compiles_lit_byte_offset:
  gas_shadow_compiles (compile_lit_byte_offset op off)
    (compile_lit_byte_offset op off)
Proof
  Cases_on `off = 0` >> Cases_on `op` >>
  simp[compile_lit_byte_offset_def, gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_imm_copy_to_memory:
  !n off. gas_shadow_compiles (compile_imm_copy_to_memory ctor imm src dst n off)
    (compile_imm_copy_to_memory ctor imm src dst n off)
Proof
  Induct >> once_rewrite_tac[compile_imm_copy_to_memory_def] >>
  simp[gas_shadow_compiles_return] >> gen_tac >>
  rewrite_tac[comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_lit_byte_offset,
               gas_shadow_compiles_imm_load_word, gas_shadow_compiles_emit_void]
       >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem gas_shadow_compiles_imm_store_words:
  !n off. gas_shadow_compiles (compile_imm_store_words imm src dst n off)
    (compile_imm_store_words imm src dst n off)
Proof
  Induct >> once_rewrite_tac[compile_imm_store_words_def] >>
  simp[gas_shadow_compiles_return] >> gen_tac >>
  rewrite_tac[comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_lit_byte_offset,
               gas_shadow_compiles_imm_store_word]
       >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem gas_shadow_compiles_ensure_in_memory:
  gas_shadow_compiles (compile_ensure_in_memory op loc sz n ctor imm)
    (compile_ensure_in_memory op loc sz n ctor imm)
Proof
  Cases_on `loc` >> Cases_on `n = 1` >>
  simp[compile_ensure_in_memory_def, LET_THM, comp_ignore_bind_def,
       gas_shadow_compiles_return] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_bind, gas_shadow_compiles_alloc_buffer,
               gas_shadow_compiles_emit_void, gas_shadow_compiles_return,
               gas_shadow_compiles_storage_to_memory,
               gas_shadow_compiles_transient_to_memory,
               gas_shadow_compiles_imm_copy_to_memory]
       >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_slot_to_memory:
  gas_shadow_compiles (compile_slot_to_memory src dst n loc)
    (compile_slot_to_memory src dst n loc)
Proof
  simp[compile_slot_to_memory_def, gas_shadow_compiles_word_copy_loop]
QED

Theorem gas_shadow_compiles_store_immutable:
  gas_shadow_compiles (compile_store_immutable imm src off n)
    (compile_store_immutable imm src off n)
Proof
  simp[compile_store_immutable_def, gas_shadow_compiles_imm_store_words]
QED

Theorem gas_shadow_compiles_load_calldata:
  gas_shadow_compiles (compile_load_calldata off prim n sz)
    (compile_load_calldata off prim n sz)
Proof
  Cases_on `prim` >> Cases_on `n = 1` >>
  simp[compile_load_calldata_def, LET_THM, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_alloc_buffer, gas_shadow_compiles_emit_void]
       >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_copy_memory_dynamic:
  gas_shadow_compiles (compile_copy_memory_dynamic dst src len)
    (compile_copy_memory_dynamic dst src len)
Proof
  simp[compile_copy_memory_dynamic_def, gas_shadow_compiles_emit_void]
QED

Theorem gas_shadow_compiles_with_byte_offset:
  gas_shadow_compiles (compile_with_byte_offset base_op off)
    (compile_with_byte_offset base_op off)
Proof
  Cases_on `off = 0` >>
  simp[compile_with_byte_offset_def, gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_bytestring_copy_len:
  gas_shadow_compiles (compile_bytestring_copy_len op)
    (compile_bytestring_copy_len op)
Proof
  simp[compile_bytestring_copy_len_def, LET_THM] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem gas_shadow_compiles_store_bytestring:
  gas_shadow_compiles (compile_store_bytestring op dst)
    (compile_store_bytestring op dst)
Proof
  simp[compile_store_bytestring_def, gas_shadow_compiles_bind,
    gas_shadow_compiles_bytestring_copy_len, gas_shadow_compiles_emit_void]
QED

Theorem gas_shadow_compiles_fixed_region_with_id:
  gas_shadow_compiles (compile_fixed_region_with_id sz)
    (compile_fixed_region_with_id sz)
Proof
  simp[compile_fixed_region_with_id_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_fresh_id, gas_shadow_compiles_fresh_var,
               gas_shadow_compiles_emit, gas_shadow_inst_def, mk_inst_def]
       >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_typed_copy_mutual:
  (!cenv dst dst_ty src src_ty.
    gas_shadow_compiles (compile_store_memory_typed cenv dst dst_ty src src_ty)
      (compile_store_memory_typed cenv dst dst_ty src src_ty)) /\
  (!cenv dst src dst_tys src_tys dst_off src_off.
    gas_shadow_compiles (compile_typed_copy_fields cenv dst src dst_tys src_tys dst_off src_off)
      (compile_typed_copy_fields cenv dst src dst_tys src_tys dst_off src_off)) /\
  (!cenv dst dst_ty src src_ty ncopy.
    gas_shadow_compiles (compile_copy_sarray_typed cenv dst dst_ty src src_ty ncopy)
      (compile_copy_sarray_typed cenv dst dst_ty src src_ty ncopy)) /\
  (!cenv dst dst_ty capacity src src_ty.
    gas_shadow_compiles (compile_copy_dynarray_typed cenv dst dst_ty capacity src src_ty)
      (compile_copy_dynarray_typed cenv dst dst_ty capacity src src_ty)) /\
  (!cenv dst src dst_fields src_fields dst_off src_off.
    gas_shadow_compiles (compile_struct_typed_copy cenv dst src dst_fields src_fields dst_off src_off)
      (compile_struct_typed_copy cenv dst src dst_fields src_fields dst_off src_off))
Proof
  ho_match_mp_tac compile_store_memory_typed_ind >>
  rpt conj_tac >> rpt gen_tac
  >- suspend "store"
  >- (once_rewrite_tac[compile_store_memory_typed_def] >> simp[gas_shadow_compiles_return])
  >- (once_rewrite_tac[compile_store_memory_typed_def] >> simp[gas_shadow_compiles_return])
  >- suspend "fields"
  >- suspend "sarray"
  >- suspend "dynarray"
  >- (once_rewrite_tac[compile_store_memory_typed_def] >> simp[gas_shadow_compiles_return])
  >> suspend "struct"
QED

Resume gas_shadow_compiles_typed_copy_mutual[store]:
  strip_tac >> once_rewrite_tac[compile_store_memory_typed_def] >>
  Cases_on `is_word_type dst_ty`
  >- simp[gas_shadow_compiles_bind, gas_shadow_compiles_emit_void] >>
  Cases_on `is_bytestring_type dst_ty /\ is_bytestring_type src_ty`
  >- simp[gas_shadow_compiles_store_bytestring] >>
  Cases_on `acyclic_struct_metadata cenv.ce_struct_fields`
  >- (Cases_on `dst_ty` >> Cases_on `src_ty` >>
      gvs[LET_THM, gas_shadow_compiles_copy_memory] >>
      rpt (CASE_TAC >> gvs[gas_shadow_compiles_copy_memory])) >>
  simp[gas_shadow_compiles_emit_void]
QED

Resume gas_shadow_compiles_typed_copy_mutual[fields]:
  strip_tac >> gvs[] >> once_rewrite_tac[compile_store_memory_typed_def] >>
  simp[LET_THM, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_with_byte_offset]
       >> gen_tac >> BETA_TAC) >> simp[]
QED

Resume gas_shadow_compiles_typed_copy_mutual[sarray]:
  strip_tac >> once_rewrite_tac[compile_store_memory_typed_def] >>
  simp[LET_THM] >>
  Cases_on `type_memory_bytes cenv dst_ty = type_memory_bytes cenv src_ty /\
            ~is_abi_dynamic cenv.ce_struct_fields dst_ty`
  >- simp[gas_shadow_compiles_copy_memory] >>
  asm_rewrite_tac[] >> gvs[] >> rewrite_tac[comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_fresh_label, gas_shadow_compiles_fresh_var,
               gas_shadow_compiles_emit_inst, gas_shadow_compiles_new_block]
       >> gen_tac >> BETA_TAC) >> simp[gas_shadow_compiles_return]
QED

Resume gas_shadow_compiles_typed_copy_mutual[dynarray]:
  strip_tac >> once_rewrite_tac[compile_store_memory_typed_def] >>
  simp[LET_THM] >>
  Cases_on `type_memory_bytes cenv dst_ty = type_memory_bytes cenv src_ty /\ dst_ty = src_ty` >>
  asm_rewrite_tac[] >> gvs[] >> rewrite_tac[comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_fresh_label, gas_shadow_compiles_fresh_var,
               gas_shadow_compiles_emit_void, gas_shadow_compiles_emit_inst,
               gas_shadow_compiles_new_block]
       >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_return, gas_shadow_compiles_copy_memory_dynamic]
QED

Resume gas_shadow_compiles_typed_copy_mutual[struct]:
  strip_tac >> once_rewrite_tac[compile_store_memory_typed_def] >>
  Cases_on `ALOOKUP src_fields name`
  >- (gvs[LET_THM] >> rewrite_tac[comp_ignore_bind_def] >>
      rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
           >- simp[gas_shadow_compiles_with_byte_offset]
           >> gen_tac >> BETA_TAC) >> simp[]) >>
  rename1 `ALOOKUP src_fields name = SOME field_info` >>
  PairCases_on `field_info` >> gvs[LET_THM] >>
  rewrite_tac[comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_with_byte_offset]
       >> gen_tac >> BETA_TAC) >> simp[]
QED

Finalise gas_shadow_compiles_typed_copy_mutual


Theorem gas_shadow_compiles_store_memory_typed:
  gas_shadow_compiles (compile_store_memory_typed cenv dst dst_ty src src_ty)
    (compile_store_memory_typed cenv dst dst_ty src src_ty)
Proof
  metis_tac[gas_shadow_compiles_typed_copy_mutual]
QED

Theorem gas_shadow_compiles_typed_copy_fields:
  gas_shadow_compiles (compile_typed_copy_fields cenv dst src dst_tys src_tys dst_off src_off)
    (compile_typed_copy_fields cenv dst src dst_tys src_tys dst_off src_off)
Proof
  metis_tac[gas_shadow_compiles_typed_copy_mutual]
QED

Theorem gas_shadow_compiles_copy_sarray_typed:
  gas_shadow_compiles (compile_copy_sarray_typed cenv dst dst_ty src src_ty ncopy)
    (compile_copy_sarray_typed cenv dst dst_ty src src_ty ncopy)
Proof
  metis_tac[gas_shadow_compiles_typed_copy_mutual]
QED

Theorem gas_shadow_compiles_copy_dynarray_typed:
  gas_shadow_compiles (compile_copy_dynarray_typed cenv dst dst_ty capacity src src_ty)
    (compile_copy_dynarray_typed cenv dst dst_ty capacity src src_ty)
Proof
  metis_tac[gas_shadow_compiles_typed_copy_mutual]
QED

Theorem gas_shadow_compiles_struct_typed_copy:
  gas_shadow_compiles (compile_struct_typed_copy cenv dst src dst_fields src_fields dst_off src_off)
    (compile_struct_typed_copy cenv dst src dst_fields src_fields dst_off src_off)
Proof
  metis_tac[gas_shadow_compiles_typed_copy_mutual]
QED

Theorem gas_shadow_compiles_store_memory:
  gas_shadow_compiles (compile_store_memory cenv src dst dst_ty src_ty)
    (compile_store_memory cenv src dst dst_ty src_ty)
Proof
  Cases_on `is_word_type dst_ty` >> Cases_on `is_bytestring_type dst_ty` >>
  Cases_on `dst_ty = src_ty` >> Cases_on `tuple_memory_layout_eq dst_ty src_ty` >>
  simp[compile_store_memory_def, gas_shadow_compiles_emit_void,
       gas_shadow_compiles_store_bytestring, gas_shadow_compiles_store_memory_typed,
       gas_shadow_compiles_copy_memory]
QED

Theorem gas_shadow_compiles_encode_log_topic:
  gas_shadow_compiles (compile_encode_log_topic val_op bytes)
    (compile_encode_log_topic val_op bytes)
Proof
  Cases_on `bytes` >> simp[compile_encode_log_topic_def,
    gas_shadow_compiles_bind, gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_load_memory:
  gas_shadow_compiles (compile_load_memory ptr_op prim)
    (compile_load_memory ptr_op prim)
Proof
  Cases_on `prim` >> simp[compile_load_memory_def, gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_store_transient:
  gas_shadow_compiles (compile_store_transient val_op slot prim word_count)
    (compile_store_transient val_op slot prim word_count)
Proof
  Cases_on `prim` >> Cases_on `word_count = 1` >>
  simp[compile_store_transient_def, gas_shadow_compiles_bind,
       gas_shadow_compiles_emit_void, gas_shadow_compiles_memory_to_transient,
       gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_dynarray_to_storage:
  gas_shadow_compiles (compile_dynarray_to_storage src dst elem_words elem_mem_size transient)
    (compile_dynarray_to_storage src dst elem_words elem_mem_size transient)
Proof
  Cases_on `elem_words = 1` >> Cases_on `transient` >>
  simp[compile_dynarray_to_storage_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_fresh_label, gas_shadow_compiles_fresh_var,
               gas_shadow_compiles_emit_inst, gas_shadow_compiles_new_block,
               gas_shadow_compiles_emit_void, gas_shadow_compiles_word_copy_loop]
       >> gen_tac >> BETA_TAC) >> simp[gas_shadow_compiles_emit_void]
QED

Theorem gas_shadow_compiles_iload_to_memory:
  !n. gas_shadow_compiles (compile_iload_to_memory src dst n)
    (compile_iload_to_memory src dst n)
Proof
  Induct >> once_rewrite_tac[compile_iload_to_memory_def] >>
  simp[LET_THM, comp_ignore_bind_def, gas_shadow_compiles_return] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_void]
       >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem gas_shadow_compiles_gep_to_memory:
  !n. gas_shadow_compiles (compile_gep_to_memory base_op off dst n)
    (compile_gep_to_memory base_op off dst n)
Proof
  Induct >> once_rewrite_tac[compile_gep_to_memory_def] >>
  simp[LET_THM, comp_ignore_bind_def, gas_shadow_compiles_return] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_void]
       >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem gas_shadow_compiles_load_immutable_ctor:
  gas_shadow_compiles (compile_load_immutable_ctor off prim n sz imm)
    (compile_load_immutable_ctor off prim n sz imm)
Proof
  Cases_on `imm` >> Cases_on `prim` >>
  simp[compile_load_immutable_ctor_def, LET_THM, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_alloc_buffer,
               gas_shadow_compiles_iload_to_memory, gas_shadow_compiles_gep_to_memory]
       >> gen_tac >> BETA_TAC) >> simp[gas_shadow_compiles_return]
QED
