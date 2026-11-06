(* Bound-label preservation for context, ABI and builtin helpers. *)
Theory helperBoundLabels
Ancestors
  boundLabelRules context compileEnv loweringShapeDefs abiEncoder builtinAbi builtinSimple builtinMath
  builtinBytes builtinStrings builtinHashing builtinSystem builtinMisc builtinCreate

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

Theorem bound_labels_fresh_label_bind:
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

Theorem bound_labels_abi_dec_addr:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_abi_dec_addr bp pos s))))
Proof
  rw[compile_abi_dec_addr_def, comp_return_def, bound_labels_emit_op]
QED

Theorem bound_labels_abi_decode_range_check:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_abi_decode_range_check lo hi_end hi s))))
Proof
  strip_tac >> simp[compile_abi_decode_range_check_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void]),
    gen_tac, strip_tac, irule bound_labels_bind, irule bound_labels_ignore_bind,
    conj_tac])
QED

Theorem bound_labels_getelemptr_abi:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_getelemptr_abi src dyn off opc bp hi s))))
Proof
  strip_tac >> simp[compile_getelemptr_abi_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_abi_dec_addr, bound_labels_abi_decode_range_check,
    comp_return_def]), gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_abi_decode_dyn_elem_ptr:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_abi_decode_dyn_elem_ptr opc bp es sd hi asz s))))
Proof
  strip_tac >> simp[compile_abi_decode_dyn_elem_ptr_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_abi_dec_addr, bound_labels_abi_decode_range_check,
    comp_return_def]), gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

val bound_labels_decode_tac =
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_emit_inst, bound_labels_abi_decode_static,
    bound_labels_abi_clamp_basetype, bound_labels_getelemptr_abi,
    bound_labels_abi_decode_dyn_elem_ptr, bound_labels_alloc_buffer,
    bound_labels_new_block, bound_labels_abi_dec_addr,
    bound_labels_abi_decode_range_check, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_fresh_label_bind,
    irule bound_labels_bind, irule bound_labels_ignore_bind,
    conj_tac, IF_CASES_TAC]) >> gvs[] >>
  Cases_on `opc` >> simp[bound_labels_emit_void];

Theorem bound_labels_abi_decode:
  (!dst src opc bp hi info s.
    (!l. compiler_label l ==> P l) /\
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label)
      (all_blocks (SND (compile_abi_decode_to_buf dst src opc bp hi info s))))) /\
  (!dst src opc bp hi elems ao vo s.
    (!l. compiler_label l ==> P l) /\
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label)
      (all_blocks (SND (compile_abi_decode_complex_elems dst src opc bp hi elems ao vo s))))) /\
  (!dst src opc bp hi ei asz msz ip cnt s.
    (!l. compiler_label l ==> P l) /\
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label)
      (all_blocks (SND (compile_abi_decode_dyn_loop dst src opc bp hi ei asz msz ip cnt s)))))
Proof
  ho_match_mp_tac compile_abi_decode_to_buf_ind >> rpt strip_tac >>
  simp[Once compile_abi_decode_to_buf_def]
  >- bound_labels_decode_tac >- bound_labels_decode_tac
  >- bound_labels_decode_tac >- bound_labels_decode_tac
  >- bound_labels_decode_tac >- bound_labels_decode_tac
  >> bound_labels_decode_tac
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

Theorem bound_labels_assert_slice_bounds[local]:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_assert_slice_bounds start_op len src_len s))))
Proof
  strip_tac >> simp[compile_assert_slice_bounds_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac])
QED

Theorem bound_labels_bytestring_src:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_bytestring_src ptr_op s))))
Proof
  strip_tac >> simp[compile_bytestring_src_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_bind, conj_tac])
QED

Theorem bound_labels_slice_data:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_slice_data len src start_op length_op sz s))))
Proof
  strip_tac >> simp[compile_slice_data_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_alloc_buffer, bound_labels_assert_slice_bounds, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac])
QED

Theorem bound_labels_slice_out_buf:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_slice_out_buf sz s))))
Proof
  strip_tac >> simp[compile_slice_out_buf_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op,
    bound_labels_alloc_buffer, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_bind, conj_tac])
QED

Theorem bound_labels_slice_calldata:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_slice_calldata start_op length_op sz s))))
Proof
  strip_tac >> simp[compile_slice_calldata_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_slice_out_buf, bound_labels_assert_slice_bounds, comp_return_def]),
    gen_tac, strip_tac, split_pair_case_tac, pairarg_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac])
QED

Theorem bound_labels_slice_code:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_slice_code start_op length_op sz s))))
Proof
  strip_tac >> simp[compile_slice_code_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_slice_out_buf, bound_labels_assert_slice_bounds, comp_return_def]),
    gen_tac, strip_tac, split_pair_case_tac, pairarg_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac])
QED

Theorem bound_labels_slice_extcode:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_slice_extcode addr start_op length_op out_buf out_data s))))
Proof
  strip_tac >> simp[compile_slice_extcode_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_assert_slice_bounds, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac])
QED

Theorem bound_labels_extract32_load:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_extract32_load len src start_op s))))
Proof
  strip_tac >> simp[compile_extract32_load_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op,
    bound_labels_assert_slice_bounds]), gen_tac, strip_tac,
    irule bound_labels_bind, irule bound_labels_ignore_bind, conj_tac])
QED

Theorem bound_labels_uint2str:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_uint2str v digits sz s))))
Proof
  strip_tac >> simp[compile_uint2str_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_emit_inst, bound_labels_alloc_buffer, bound_labels_new_block,
    cj 4 bound_labels_primitives, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_fresh_label_bind,
    irule bound_labels_bind, irule bound_labels_ignore_bind, conj_tac])
QED

Theorem bound_labels_keccak256_word:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_keccak256_word v s))))
Proof
  strip_tac >> simp[compile_keccak256_word_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_alloc_buffer, comp_return_def]), gen_tac, strip_tac,
    irule bound_labels_bind, irule bound_labels_ignore_bind, conj_tac])
QED

Theorem bound_labels_keccak256_bytes:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_keccak256_bytes ptr_op s))))
Proof
  strip_tac >> simp[compile_keccak256_bytes_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op]), gen_tac, strip_tac,
    irule bound_labels_bind, conj_tac])
QED

Theorem bound_labels_keccak256_bytesm:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_keccak256_bytesm v m s))))
Proof
  strip_tac >> simp[compile_keccak256_bytesm_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_alloc_buffer, comp_return_def]), gen_tac, strip_tac,
    irule bound_labels_bind, irule bound_labels_ignore_bind, conj_tac])
QED

Theorem bound_labels_method_id_hash[local]:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_method_id_hash ty v s))))
Proof
  Cases_on `ty` >> simp[compile_method_id_hash_def, bound_labels_keccak256_bytes] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[compile_method_id_hash_def, bound_labels_keccak256_bytes] >>
  rename1 `BytesT sz` >> Cases_on `sz` >>
  simp[compile_method_id_hash_def, bound_labels_keccak256_bytes,
    bound_labels_keccak256_bytesm]
QED

Theorem bound_labels_method_id_runtime:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_method_id_runtime ty v bytes4 s))))
Proof
  strip_tac >> simp[compile_method_id_runtime_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_alloc_buffer, bound_labels_method_id_hash, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_sha256_word:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_sha256_word v s))))
Proof
  strip_tac >> simp[compile_sha256_word_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_alloc_buffer, comp_return_def]), gen_tac, strip_tac,
    irule bound_labels_bind, irule bound_labels_ignore_bind, conj_tac])
QED

Theorem bound_labels_sha256_bytes:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_sha256_bytes ptr_op s))))
Proof
  strip_tac >> simp[compile_sha256_bytes_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_alloc_buffer, comp_return_def]), gen_tac, strip_tac,
    irule bound_labels_bind, irule bound_labels_ignore_bind, conj_tac])
QED

Theorem bound_labels_sha256_bytesm:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_sha256_bytesm v m s))))
Proof
  strip_tac >> simp[compile_sha256_bytesm_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_alloc_buffer, comp_return_def]), gen_tac, strip_tac,
    irule bound_labels_bind, irule bound_labels_ignore_bind, conj_tac])
QED

Theorem bound_labels_msg_data_to_memory:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_msg_data_to_memory s))))
Proof
  strip_tac >> simp[compile_msg_data_to_memory_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_alloc_dynamic, comp_return_def]), gen_tac, strip_tac,
    irule bound_labels_bind, irule bound_labels_ignore_bind, conj_tac])
QED

Theorem bound_labels_raw_call_outbuf:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_raw_call_outbuf sz s))))
Proof
  strip_tac >> simp[compile_raw_call_outbuf_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op,
    bound_labels_alloc_buffer, comp_return_def]), gen_tac, strip_tac,
    irule bound_labels_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_raw_call_finish:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_raw_call_finish addr data_ptr data_len gas_op val_op
      call_ty sz revert_fail out_val out_ptr s))))
Proof
  strip_tac >> Cases_on `call_ty` >> simp[compile_raw_call_finish_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_emit_inst, bound_labels_alloc_buffer, bound_labels_new_block,
    bound_labels_select, comp_return_def]), gen_tac, strip_tac,
    irule bound_labels_fresh_label_bind, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_send:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_send addr v gas_op s))))
Proof
  strip_tac >> simp[compile_send_def] >>
  irule bound_labels_bind >> simp[bound_labels_emit_op, bound_labels_emit_void]
QED

Theorem bound_labels_raw_log:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_raw_log n ptr_op len topics s))))
Proof
  simp[compile_raw_log_def, bound_labels_emit_void]
QED

Theorem bound_labels_raw_revert:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_raw_revert ptr_op s))))
Proof
  strip_tac >> simp[compile_raw_revert_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_inst]),
    gen_tac, strip_tac, irule bound_labels_bind, conj_tac])
QED

Theorem bound_labels_selfdestruct:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_selfdestruct addr s))))
Proof
  simp[compile_selfdestruct_def, bound_labels_emit_void]
QED

Theorem bound_labels_ecrecover:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_ecrecover h v r sig_s s))))
Proof
  strip_tac >> simp[compile_ecrecover_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_alloc_buffer, comp_return_def]), gen_tac, strip_tac,
    irule bound_labels_bind, irule bound_labels_ignore_bind, conj_tac])
QED

Theorem bound_labels_ecadd_points:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_ecadd_points p1 p2 s))))
Proof
  strip_tac >> simp[compile_ecadd_points_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_alloc_buffer, comp_return_def]), gen_tac, strip_tac,
    irule bound_labels_bind, irule bound_labels_ignore_bind, conj_tac])
QED

Theorem bound_labels_ecmul_point:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_ecmul_point ptr_op scalar s))))
Proof
  strip_tac >> simp[compile_ecmul_point_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_alloc_buffer, comp_return_def]), gen_tac, strip_tac,
    irule bound_labels_bind, irule bound_labels_ignore_bind, conj_tac])
QED

Theorem bound_labels_blockhash:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_blockhash n s))))
Proof
  strip_tac >> simp[compile_blockhash_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac])
QED

Theorem bound_labels_blobhash:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_blobhash n s))))
Proof
  simp[compile_blobhash_def, bound_labels_emit_op]
QED

Theorem bound_labels_floor:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_floor v divisor s))))
Proof
  strip_tac >> simp[compile_floor_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_select]),
    gen_tac, strip_tac, irule bound_labels_bind, conj_tac])
QED

Theorem bound_labels_ceil:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_ceil v divisor s))))
Proof
  strip_tac >> simp[compile_ceil_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_select]),
    gen_tac, strip_tac, irule bound_labels_bind, conj_tac])
QED

Theorem bound_labels_as_wei_value_int:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_as_wei_value_int v scale signed s))))
Proof
  strip_tac >> simp[compile_as_wei_value_int_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    comp_return_def]), gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_as_wei_value_decimal:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_as_wei_value_decimal v scale divisor s))))
Proof
  strip_tac >> simp[compile_as_wei_value_decimal_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_check_create_result[local]:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_check_create_result v revert_fail s))))
Proof
  strip_tac >> simp[compile_check_create_result_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_emit_inst, bound_labels_new_block, bound_labels_alloc_buffer,
    comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_fresh_label_bind,
    irule bound_labels_bind, irule bound_labels_ignore_bind,
    conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_create_dispatch:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_create_dispatch ptr_op len v salt revert_fail s))))
Proof
  strip_tac >> Cases_on `salt` >> simp[compile_create_dispatch_def] >>
  irule bound_labels_bind >>
  simp[bound_labels_emit_op, bound_labels_check_create_result]
QED

Theorem bound_labels_create_proxy_buf:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_create_proxy_buf target s))))
Proof
  strip_tac >> simp[compile_create_proxy_buf_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_check_create_result, bound_labels_alloc_buffer,
    bound_labels_alloc_dynamic, bound_labels_copy_memory_dynamic,
    comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_create_proxy:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_create_proxy target v salt revert_fail s))))
Proof
  strip_tac >> simp[compile_create_proxy_def] >>
  irule bound_labels_bind >>
  simp[bound_labels_create_proxy_buf, bound_labels_create_dispatch]
QED

Theorem bound_labels_create_copy:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_create_copy target v salt revert_fail s))))
Proof
  strip_tac >> Cases_on `salt` >> simp[compile_create_copy_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_check_create_result, bound_labels_alloc_buffer,
    bound_labels_alloc_dynamic, bound_labels_copy_memory_dynamic,
    comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_create_blueprint_check:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_create_blueprint_check target offset s))))
Proof
  strip_tac >> simp[compile_create_blueprint_check_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_check_create_result, bound_labels_alloc_buffer,
    bound_labels_alloc_dynamic, bound_labels_copy_memory_dynamic,
    comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_create_blueprint_append:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_create_blueprint_append target v salt offset csz aptr alen
            revert_fail s))))
Proof
  strip_tac >> Cases_on `salt` >> simp[compile_create_blueprint_append_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_check_create_result, bound_labels_alloc_buffer,
    bound_labels_alloc_dynamic, bound_labels_copy_memory_dynamic,
    comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_create_blueprint:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_create_blueprint target v salt offset args_info revert_fail s))))
Proof
  strip_tac >>
  `?p l. (case args_info of NONE => (Lit 0w,Lit 0w) | SOME info => info) =
         (p,l)` by metis_tac[pairTheory.PAIR] >>
  simp[compile_create_blueprint_def] >> irule bound_labels_bind >>
  simp[bound_labels_create_blueprint_check,
       bound_labels_create_blueprint_append]
QED
