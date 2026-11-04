(* Bound-label preservation for context, ABI and builtin helpers. *)
Theory helperBoundLabels
Ancestors
  boundLabelRules context compileEnv loweringShapeDefs abiEncoder builtinAbi builtinSimple builtinMath

Theorem bound_labels_imm_load_word:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_imm_load_word is_ctor imm off s))))
Proof
  Cases_on `is_ctor` >> Cases_on `imm` >>
  simp[compile_imm_load_word_def, bound_labels_emit_op] >>
  strip_tac >> irule bound_labels_bind >> simp[bound_labels_emit_op]
QED

Theorem bound_labels_imm_store_word:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_imm_store_word imm off v s))))
Proof
  Cases_on `imm` >> simp[compile_imm_store_word_def, bound_labels_emit_void] >>
  strip_tac >> irule bound_labels_bind >>
  simp[bound_labels_emit_op, bound_labels_emit_void]
QED

Theorem bound_labels_ptr_load:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_ptr_load is_ctor imm loc op s))))
Proof
  Cases_on `loc` >>
  simp[compile_ptr_load_def, bound_labels_emit_op, bound_labels_imm_load_word]
QED

Theorem bound_labels_ptr_store:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_ptr_store is_ctor imm loc dst v s))))
Proof
  Cases_on `loc` >> Cases_on `is_ctor` >>
  simp[compile_ptr_store_def, bound_labels_emit_void, bound_labels_imm_store_word]
QED

Theorem bound_labels_copy_memory:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_copy_memory dst src n s))))
Proof
  Cases_on `n` >>
  simp[compile_copy_memory_def, comp_return_def, bound_labels_emit_void]
QED

Theorem bound_labels_fresh_label_bind[local]:
  (!l t. compiler_label l /\
     EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
     EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (g l t))))) ==>
  !s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label)
      (all_blocks (SND (comp_bind (fresh_label suffix) g s))))
Proof
  rpt strip_tac >> irule bound_labels_bind_result >>
  reverse conj_tac >- simp[] >>
  qexists_tac `\l t. compiler_label l /\
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks t))` >>
  simp[] >> qx_gen_tac `t` >> strip_tac >>
  Cases_on `fresh_label suffix t` >>
  drule bound_labels_fresh_label >> simp[]
QED

Theorem bound_labels_word_copy_loop:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_word_copy_loop src dst n ld st ctor s))))
Proof
  strip_tac >> simp[compile_word_copy_loop_def] >>
  irule bound_labels_fresh_label_bind >> simp[] >> rpt strip_tac >>
  irule bound_labels_fresh_label_bind >> simp[] >> rpt strip_tac >>
  irule bound_labels_fresh_label_bind >> simp[] >> rpt strip_tac >>
  rpt (FIRST [
    CHANGED_TAC (simp[bound_labels_emit_inst, bound_labels_emit_op,
      bound_labels_ptr_load, bound_labels_ptr_store, bound_labels_new_block,
      cj 4 bound_labels_primitives]),
    gen_tac, strip_tac,
    irule bound_labels_bind, irule bound_labels_ignore_bind,
    conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_location_copy:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_storage_to_memory src dst n s)))) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_memory_to_storage src dst n s)))) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_transient_to_memory src dst n s)))) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_memory_to_transient src dst n s)))) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_slot_to_memory src dst n loc s))))
Proof
  simp[compile_storage_to_memory_def, compile_memory_to_storage_def,
    compile_transient_to_memory_def, compile_memory_to_transient_def,
    compile_slot_to_memory_def, bound_labels_word_copy_loop]
QED

Theorem bound_labels_alloc_buffer:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_alloc_buffer n s))))
Proof
  strip_tac >> simp[compile_alloc_buffer_def] >>
  irule bound_labels_bind >> simp[bound_labels_emit_op, comp_return_def]
QED

Theorem bound_labels_alloc_dynamic:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_alloc_dynamic n s))))
Proof
  simp[compile_alloc_dynamic_def, bound_labels_emit_op]
QED

Theorem bound_labels_fixed_region:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_fixed_region_with_id n s))))
Proof
  simp[compile_fixed_region_with_id_def, comp_bind_def,
    comp_ignore_bind_def, fresh_id_def, fresh_var_def, emit_def,
    comp_return_def, all_blocks_def]
QED

Theorem bound_labels_code_to_memory:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_code_to_memory src dst n s))))
Proof
  strip_tac >> simp[compile_code_to_memory_def] >>
  Cases_on `n = 0` >> simp[comp_return_def] >>
  irule bound_labels_ignore_bind >>
  simp[bound_labels_word_copy_loop, comp_return_def]
QED

Theorem bound_labels_load_storage:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_load_storage slot prim n sz s))))
Proof
  strip_tac >> simp[compile_load_storage_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_alloc_buffer, bound_labels_location_copy, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_store_storage:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_store_storage v slot prim n s))))
Proof
  strip_tac >> simp[compile_store_storage_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_location_copy, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_load_transient:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_load_transient slot prim n sz s))))
Proof
  strip_tac >> simp[compile_load_transient_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_alloc_buffer, bound_labels_location_copy, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_load_immutable:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_load_immutable slot prim n sz ctor s))))
Proof
  strip_tac >> simp[compile_load_immutable_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_alloc_buffer, bound_labels_code_to_memory, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_nonreentrant_lock:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_nonreentrant_lock key transient view s))))
Proof
  strip_tac >> simp[compile_nonreentrant_lock_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    comp_return_def]), gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_nonreentrant_unlock:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_nonreentrant_unlock key transient view s))))
Proof
  Cases_on `view` >> Cases_on `transient` >>
  simp[compile_nonreentrant_unlock_def, bound_labels_emit_void, comp_return_def]
QED

Theorem bound_labels_zero_memory_loop:
  !ptr i words s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_zero_memory_loop ptr i words s))))
Proof
  recInduct compile_zero_memory_loop_ind >> rpt strip_tac >>
  simp[Once compile_zero_memory_loop_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    comp_return_def]), gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_zero_memory:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_zero_memory ptr_op n s))))
Proof
  Cases_on `n` >> simp[compile_zero_memory_def, comp_return_def,
    bound_labels_zero_memory_loop]
QED

Theorem bound_labels_lit_byte_offset:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_lit_byte_offset op off s))))
Proof
  Cases_on `off = 0` >> Cases_on `op` >>
  simp[compile_lit_byte_offset_def, comp_return_def, bound_labels_emit_op]
QED

Theorem bound_labels_imm_copy_to_memory:
  !n off s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_imm_copy_to_memory ctor imm src dst n off s))))
Proof
  Induct >> simp[compile_imm_copy_to_memory_def, comp_return_def] >>
  rpt strip_tac >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_lit_byte_offset,
    bound_labels_imm_load_word, bound_labels_emit_void]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac])
QED

Theorem bound_labels_imm_store_words:
  !n off s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_imm_store_words imm src dst n off s))))
Proof
  Induct >> simp[compile_imm_store_words_def, comp_return_def] >>
  rpt strip_tac >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_lit_byte_offset,
    bound_labels_imm_store_word, bound_labels_emit_op]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac])
QED

Theorem bound_labels_store_immutable:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_store_immutable imm src dst n s))))
Proof
  simp[compile_store_immutable_def, bound_labels_imm_store_words]
QED

Theorem bound_labels_ensure_in_memory:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_ensure_in_memory ptr_op loc sz n ctor imm s))))
Proof
  strip_tac >> Cases_on `loc` >> simp[compile_ensure_in_memory_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_alloc_buffer, bound_labels_location_copy,
    bound_labels_imm_copy_to_memory, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_load_calldata:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_load_calldata slot prim n sz s))))
Proof
  strip_tac >> simp[compile_load_calldata_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_alloc_buffer, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_copy_memory_dynamic:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_copy_memory_dynamic dst src len s))))
Proof
  simp[compile_copy_memory_dynamic_def, bound_labels_emit_void]
QED

Theorem bound_labels_with_byte_offset:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_with_byte_offset base_op off s))))
Proof
  Cases_on `off = 0` >>
  simp[compile_with_byte_offset_def, comp_return_def, bound_labels_emit_op]
QED

Theorem bound_labels_bytestring_copy_len:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_bytestring_copy_len op s))))
Proof
  strip_tac >> simp[compile_bytestring_copy_len_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op]),
    gen_tac, strip_tac, irule bound_labels_bind, conj_tac])
QED

Theorem bound_labels_store_bytestring:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_store_bytestring src dst s))))
Proof
  strip_tac >> simp[compile_store_bytestring_def] >>
  irule bound_labels_bind >>
  simp[bound_labels_bytestring_copy_len, bound_labels_emit_void]
QED

Theorem bound_labels_memory_typed:
  (!cenv dst dt src st s.
    (!l. compiler_label l ==> P l) /\
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label)
      (all_blocks (SND (compile_store_memory_typed cenv dst dt src st s))))) /\
  (!cenv dst src dts sts doff soff s.
    (!l. compiler_label l ==> P l) /\
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label)
      (all_blocks (SND (compile_typed_copy_fields cenv dst src dts sts doff soff s))))) /\
  (!cenv dst dt src st n s.
    (!l. compiler_label l ==> P l) /\
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label)
      (all_blocks (SND (compile_copy_sarray_typed cenv dst dt src st n s))))) /\
  (!cenv dst dt cap src st s.
    (!l. compiler_label l ==> P l) /\
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label)
      (all_blocks (SND (compile_copy_dynarray_typed cenv dst dt cap src st s))))) /\
  (!cenv dst src dfs sfs doff soff s.
    (!l. compiler_label l ==> P l) /\
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label)
      (all_blocks (SND (compile_struct_typed_copy cenv dst src dfs sfs doff soff s)))))
Proof
  ho_match_mp_tac compile_store_memory_typed_ind >> rpt strip_tac
  >- suspend "dispatch" >>
  simp[Once compile_store_memory_typed_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_emit_inst, bound_labels_copy_memory,
    bound_labels_copy_memory_dynamic, bound_labels_with_byte_offset,
    bound_labels_new_block, cj 4 bound_labels_primitives, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_fresh_label_bind,
    irule bound_labels_bind, irule bound_labels_ignore_bind,
    conj_tac, IF_CASES_TAC]) >>
  gvs[] >> pairarg_tac >> gvs[] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_with_byte_offset]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac])
QED

Resume bound_labels_memory_typed[dispatch]:
  Cases_on `is_word_type dt`
  >- (simp[Once compile_store_memory_typed_def] >>
      irule bound_labels_bind >> simp[bound_labels_emit_op, bound_labels_emit_void]) >>
  Cases_on `is_bytestring_type dt /\ is_bytestring_type st`
  >- simp[Once compile_store_memory_typed_def, bound_labels_store_bytestring] >>
  Cases_on `~acyclic_struct_metadata cenv.ce_struct_fields`
  >- simp[Once compile_store_memory_typed_def, bound_labels_emit_void] >>
  Cases_on `dt` >> Cases_on `st` >>
  simp[Once compile_store_memory_typed_def, bound_labels_copy_memory] >>
  gvs[] >> Cases_on `b` >> Cases_on `b'` >> gvs[bound_labels_copy_memory]
QED

Finalise bound_labels_memory_typed

Theorem bound_labels_store_memory:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_store_memory cenv src dst dt st s))))
Proof
  strip_tac >> simp[compile_store_memory_def] >>
  rpt IF_CASES_TAC >>
  simp[bound_labels_emit_void, bound_labels_store_bytestring,
    cj 1 bound_labels_memory_typed, bound_labels_copy_memory]
QED

Theorem bound_labels_encode_log_topic:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_encode_log_topic op bytes s))))
Proof
  strip_tac >> Cases_on `bytes` >>
  simp[compile_encode_log_topic_def, comp_return_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op]),
    gen_tac, strip_tac, irule bound_labels_bind, conj_tac])
QED

Theorem bound_labels_load_memory:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_load_memory ptr_op prim s))))
Proof
  Cases_on `prim` >>
  simp[compile_load_memory_def, comp_return_def, bound_labels_emit_op]
QED

Theorem bound_labels_store_transient:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_store_transient v slot prim n s))))
Proof
  strip_tac >> simp[compile_store_transient_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_location_copy, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_dynarray_to_storage:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_dynarray_to_storage src dst ew em transient s))))
Proof
  strip_tac >> simp[compile_dynarray_to_storage_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_emit_inst, bound_labels_word_copy_loop,
    bound_labels_new_block, cj 4 bound_labels_primitives]),
    gen_tac, strip_tac, irule bound_labels_fresh_label_bind,
    irule bound_labels_bind, irule bound_labels_ignore_bind,
    conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_iload_to_memory:
  !n s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_iload_to_memory src dst n s))))
Proof
  Induct >> simp[compile_iload_to_memory_def, comp_return_def] >>
  rpt strip_tac >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac])
QED

Theorem bound_labels_gep_to_memory:
  !n s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_gep_to_memory src off dst n s))))
Proof
  Induct >> simp[compile_gep_to_memory_def, comp_return_def] >>
  rpt strip_tac >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac])
QED

Theorem bound_labels_load_immutable_ctor:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_load_immutable_ctor off prim n sz imm s))))
Proof
  strip_tac >> Cases_on `imm` >> simp[compile_load_immutable_ctor_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_alloc_buffer,
    bound_labels_iload_to_memory, bound_labels_gep_to_memory, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_bytes_data_ptr:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_bytes_data_ptr ptr_op loc s))))
Proof
  simp[compile_bytes_data_ptr_def, bound_labels_emit_op]
QED

Theorem bound_labels_bytestring_length:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_bytestring_length ctor imm ptr_op loc s))))
Proof
  simp[compile_bytestring_length_def, bound_labels_ptr_load]
QED

Theorem bound_labels_abi_int_clamp:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_abi_int_clamp op bits signed s))))
Proof
  strip_tac >> Cases_on `signed` >> simp[compile_abi_int_clamp_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void]),
    gen_tac, strip_tac, irule bound_labels_bind, conj_tac])
QED

Theorem bound_labels_abi_bytes_clamp:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_abi_bytes_clamp op n s))))
Proof
  strip_tac >> simp[compile_abi_bytes_clamp_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void]),
    gen_tac, strip_tac, irule bound_labels_bind, conj_tac])
QED

Theorem bound_labels_abi_clamp_basetype:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_abi_clamp_basetype op clamp s))))
Proof
  strip_tac >> Cases_on `clamp` >>
  simp[compile_abi_clamp_basetype_def, bound_labels_abi_int_clamp,
    bound_labels_abi_bytes_clamp, comp_return_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void]),
    gen_tac, strip_tac, irule bound_labels_bind, conj_tac])
QED

Theorem bound_labels_abi_zero_pad:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_abi_zero_pad op len cnt s))))
Proof
  strip_tac >> simp[compile_abi_zero_pad_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void]),
    gen_tac, strip_tac, irule bound_labels_bind, conj_tac])
QED

Theorem bound_labels_get_element_ptr:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_get_element_ptr op off s))))
Proof
  simp[compile_get_element_ptr_def, bound_labels_emit_op]
QED

Theorem bound_labels_get_dynarray_elem_ptr:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_get_dynarray_elem_ptr op idx sz s))))
Proof
  strip_tac >> simp[compile_get_dynarray_elem_ptr_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op]),
    gen_tac, strip_tac, irule bound_labels_bind, conj_tac])
QED

Theorem bound_labels_abi_encode_static:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_abi_encode_static dst src s))))
Proof
  strip_tac >> simp[compile_abi_encode_static_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    comp_return_def]), gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac])
QED

Theorem bound_labels_abi_decode_static:
  (!op t. EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (clamp op t))))) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_abi_decode_static src dst opc clamp s))))
Proof
  strip_tac >> simp[compile_abi_decode_static_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac])
QED

Theorem bound_labels_abi_encode_static_info:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_abi_encode_static_info dst src info s))))
Proof
  strip_tac >> Cases_on `info` >>
  simp[compile_abi_encode_static_info_def, bound_labels_abi_encode_static,
    comp_return_def] >> irule bound_labels_ignore_bind >>
  simp[bound_labels_emit_void, comp_return_def]
QED

Theorem bound_labels_abi_encode_dyn_static_loop:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_abi_encode_dyn_static_loop dst src info asz msz len s))))
Proof
  strip_tac >> simp[compile_abi_encode_dyn_static_loop_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_emit_inst, bound_labels_abi_encode_static_info,
    bound_labels_alloc_buffer, bound_labels_new_block, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_fresh_label_bind,
    irule bound_labels_bind, irule bound_labels_ignore_bind, conj_tac])
QED

Theorem bound_labels_abi_encode:
  (!dst cp ci dyn off dp s.
    (!l. compiler_label l ==> P l) /\
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label)
      (all_blocks (SND (compile_abi_encode_child dst cp ci dyn off dp s))))) /\
  (!dst src info s.
    (!l. compiler_label l ==> P l) /\
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label)
      (all_blocks (SND (compile_abi_encode_to_buf dst src info s))))) /\
  (!dst src elems off ho dp s.
    (!l. compiler_label l ==> P l) /\
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label)
      (all_blocks (SND (compile_abi_encode_complex_elems dst src elems off ho dp s))))) /\
  (!dst src ei asz msz lo s.
    (!l. compiler_label l ==> P l) /\
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label)
      (all_blocks (SND (compile_abi_encode_dyn_loop dst src ei asz msz lo s)))))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >> rpt strip_tac >>
  simp[Once compile_abi_encode_child_def] >>
  rpt (FIRST [CHANGED_TAC (gvs[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_emit_inst, bound_labels_abi_encode_static,
    bound_labels_abi_encode_dyn_static_loop, bound_labels_alloc_buffer,
    bound_labels_new_block, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_fresh_label_bind,
    irule bound_labels_bind, irule bound_labels_ignore_bind,
    conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_getelemptr_abi:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_getelemptr_abi src dyn off opc hi s))))
Proof
  strip_tac >> simp[compile_getelemptr_abi_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    comp_return_def]), gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_abi_decode_dyn_elem_ptr:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_abi_decode_dyn_elem_ptr opc es sd hi asz s))))
Proof
  strip_tac >> simp[compile_abi_decode_dyn_elem_ptr_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    comp_return_def]), gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_abi_decode:
  (!dst src opc hi info s.
    (!l. compiler_label l ==> P l) /\
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label)
      (all_blocks (SND (compile_abi_decode_to_buf dst src opc hi info s))))) /\
  (!dst src opc hi elems ao vo s.
    (!l. compiler_label l ==> P l) /\
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label)
      (all_blocks (SND (compile_abi_decode_complex_elems dst src opc hi elems ao vo s))))) /\
  (!dst src opc hi ei asz msz ip cnt s.
    (!l. compiler_label l ==> P l) /\
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label)
      (all_blocks (SND (compile_abi_decode_dyn_loop dst src opc hi ei asz msz ip cnt s)))))
Proof
  ho_match_mp_tac compile_abi_decode_to_buf_ind >> rpt strip_tac >>
  simp[Once compile_abi_decode_to_buf_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_emit_inst, bound_labels_abi_decode_static,
    bound_labels_abi_clamp_basetype, bound_labels_getelemptr_abi,
    bound_labels_abi_decode_dyn_elem_ptr, bound_labels_alloc_buffer,
    bound_labels_new_block, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_fresh_label_bind,
    irule bound_labels_bind, irule bound_labels_ignore_bind,
    conj_tac, IF_CASES_TAC]) >> gvs[] >>
  Cases_on `opc` >> simp[bound_labels_emit_void]
QED

Theorem bound_labels_lower_abi_encode:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (lower_abi_encode tuple mid src info maxlen s))))
Proof
  strip_tac >> Cases_on `mid` >> simp[lower_abi_encode_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_alloc_buffer, cj 2 bound_labels_abi_encode, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_lower_abi_decode:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (lower_abi_decode src info lo hi sz s))))
Proof
  strip_tac >> simp[lower_abi_decode_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_alloc_buffer, cj 1 bound_labels_abi_decode, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_select:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_select cond_op a b s))))
Proof
  strip_tac >> simp[compile_select_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op]),
    gen_tac, strip_tac, irule bound_labels_bind, conj_tac])
QED

Theorem bound_labels_builtin_len:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_builtin_len ctor imm ptr_op loc s))))
Proof
  simp[compile_builtin_len_def, bound_labels_ptr_load]
QED

Theorem bound_labels_builtin_calldatasize:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_builtin_calldatasize s))))
Proof
  simp[compile_builtin_calldatasize_def, bound_labels_emit_op]
QED

Theorem bound_labels_builtin_empty_prim:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_builtin_empty_prim s))))
Proof
  simp[compile_builtin_empty_prim_def, comp_return_def]
QED

Theorem bound_labels_zero_words:
  !n s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_zero_words op n s))))
Proof
  Induct >> simp[compile_zero_words_def, comp_return_def] >> rpt strip_tac >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac])
QED

Theorem bound_labels_builtin_empty_complex:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_builtin_empty_complex sz bytes s))))
Proof
  strip_tac >> simp[compile_builtin_empty_complex_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_alloc_buffer, bound_labels_emit_void,
    bound_labels_zero_words, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_builtin_min:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_builtin_min a b unsigned s))))
Proof
  strip_tac >> Cases_on `unsigned` >> simp[compile_builtin_min_def] >>
  irule bound_labels_bind >> simp[bound_labels_emit_op, bound_labels_select]
QED

Theorem bound_labels_builtin_max:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_builtin_max a b unsigned s))))
Proof
  strip_tac >> Cases_on `unsigned` >> simp[compile_builtin_max_def] >>
  irule bound_labels_bind >> simp[bound_labels_emit_op, bound_labels_select]
QED

Theorem bound_labels_builtin_abs:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_builtin_abs op s))))
Proof
  strip_tac >> simp[compile_builtin_abs_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_select]), gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac])
QED

Theorem bound_labels_unsafe_binop:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_unsafe_binop opc a b bits signed s))))
Proof
  strip_tac >> simp[compile_unsafe_binop_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_pow_mod256:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_pow_mod256 a b s))))
Proof
  simp[compile_pow_mod256_def, bound_labels_emit_op]
QED

Theorem bound_labels_addmod:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_addmod a b c s))))
Proof
  strip_tac >> simp[compile_addmod_def] >>
  irule bound_labels_ignore_bind >> simp[bound_labels_emit_void, bound_labels_emit_op]
QED

Theorem bound_labels_mulmod:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_mulmod a b c s))))
Proof
  strip_tac >> simp[compile_mulmod_def] >>
  irule bound_labels_ignore_bind >> simp[bound_labels_emit_void, bound_labels_emit_op]
QED

Theorem bound_labels_shift:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_shift op bits signed s))))
Proof
  strip_tac >> simp[compile_shift_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_select]),
    gen_tac, strip_tac, irule bound_labels_bind, conj_tac, IF_CASES_TAC])
QED
