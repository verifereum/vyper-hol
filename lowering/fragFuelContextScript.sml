(*
 * Fuel bounds (fuel_ok) for the context-level emission helpers.
 *
 * TOP-LEVEL:
 *   fuel_ok_context_copies, fuel_ok_context_storage,
 *   fuel_ok_compile_store_immutable, fuel_ok_compile_zero_memory,
 *   fuel_ok_context_misc, fuel_ok_typed_memory_family,
 *   fuel_ok_compile_store_memory
 *)

Theory fragFuelContext
Ancestors
  fragFuel fragFuelContextBase fragFuelLoopWcopy fragFuelLoopSarray
  fragFuelLoopDynarray compileEnv emitHelper context venomInst
Libs
  fragFuelLib

Theorem fuel_ok_compile_word_copy_loop:
  (!src dst count load_loc store_loc is_ctor Wv E.
     fuel_okS (\st. !x. count = Var x ==> var_below st.cs_next_var x) Wv {} E
       (compile_word_copy_loop_op src dst count load_loc store_loc is_ctor)) /\
  (!src dst n load_loc store_loc is_ctor Wv E.
     fuel_ok Wv {} E
       (compile_word_copy_loop src dst n load_loc store_loc is_ctor))
Proof
  conj_tac >> rpt gen_tac
  >- simp[compile_word_copy_loop_op_def, fuel_okS_compile_word_copy_loop_base] >>
  simp[compile_word_copy_loop_def, compile_word_copy_loop_op_def] >>
  irule fuel_ok_of_okS >>
  qexists_tac `\st. !x. Lit (n2w n) = Var x ==> var_below st.cs_next_var x` >>
  simp[fuel_okS_compile_word_copy_loop_base]
QED

Theorem compile_bytestring_word_count_var:
  !src st x st'.
    compile_bytestring_word_count src st = (x, st') ==>
    !y. x = Var y ==> var_below st'.cs_next_var y
Proof
  simp[compile_bytestring_word_count_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       emit_def] >>
  rpt strip_tac >> gvs[] >> simp[var_below_def] >> rpt strip_tac >>
  fs[ASCIInumbersTheory.toString_inj]
QED

Theorem fuel_ok_compile_store_immutable_bytestring:
  !imm src dst Wv E.
    fuel_ok Wv {} E (compile_store_immutable_bytestring imm src dst)
Proof
  rpt gen_tac >> irule fuel_ok_of_okS >> qexists_tac `\st. T` >> simp[] >>
  simp[compile_store_immutable_bytestring_def] >>
  `fuel_okS (\st. T) Wv ({} UNION {}) E
     (comp_bind (compile_bytestring_word_count src)
        (\count. comp_ignore_bind
           (compile_word_copy_loop_base src dst count LocMemory LocCode T imm)
           (comp_return ())))` suffices_by simp[] >>
  match_mp_tac fuel_okS_bind >>
  qexistsl_tac [`\c st. !x. c = Var x ==> var_below st.cs_next_var x`,
                `E`, `E`] >>
  simp[pred_setTheory.SUBSET_DEF] >> rpt conj_tac
  >- (irule fuel_okS_of_ok >> simp_tac std_ss [compile_bytestring_word_count_def] >>
      fuel_auto [fuel_ok_emit_op] >> simp[is_terminator_def])
  >- metis_tac[compile_bytestring_word_count_var] >>
  gen_tac >> match_mp_tac fuel_okS_ignore_bind_keep >>
  simp[fuel_okS_compile_word_copy_loop_base, fuel_okS_of_ok, fuel_ok_return] >>
  rw[next_stable_def, var_below_def]
QED

Theorem fuel_ok_context_copies:
  (!src. fuel_ok Wv {} E (compile_bytestring_word_count src)) /\
  (!slot buf n. fuel_ok Wv {} E (compile_storage_to_memory slot buf n)) /\
  (!buf slot n. fuel_ok Wv {} E (compile_memory_to_storage buf slot n)) /\
  (!slot buf n. fuel_ok Wv {} E (compile_transient_to_memory slot buf n)) /\
  (!buf slot n. fuel_ok Wv {} E (compile_memory_to_transient buf slot n)) /\
  (!src dst n loc. fuel_ok Wv {} E (compile_slot_to_memory src dst n loc)) /\
  (!off dst n. fuel_ok Wv {} E (compile_code_to_memory off dst n))
Proof
  rpt conj_tac >> rpt gen_tac >>
  simp_tac std_ss [compile_bytestring_word_count_def,
    compile_storage_to_memory_def,
    compile_memory_to_storage_def, compile_transient_to_memory_def,
    compile_memory_to_transient_def, compile_slot_to_memory_def,
    compile_code_to_memory_def] >>
  fuel_auto [fuel_ok_emit_op, CONJUNCT2 fuel_ok_compile_word_copy_loop] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_context_storage:
  (!slot p n sz. fuel_ok Wv {} E (compile_load_storage slot p n sz)) /\
  (!v slot p n. fuel_ok Wv {} E (compile_store_storage v slot p n)) /\
  (!slot p n sz. fuel_ok Wv {} E (compile_load_transient slot p n sz)) /\
  (!off p n sz c. fuel_ok Wv {} E (compile_load_immutable off p n sz c)) /\
  (!off p n sz. fuel_ok Wv {} E (compile_load_calldata off p n sz)) /\
  (!k t v. fuel_ok Wv {} E (compile_nonreentrant_lock k t v)) /\
  (!k t v. fuel_ok Wv {} E (compile_nonreentrant_unlock k t v)) /\
  (!d s l. fuel_ok Wv {} E (compile_copy_memory_dynamic d s l)) /\
  (!b off. fuel_ok Wv {} E (compile_with_byte_offset b off)) /\
  (!p loc. fuel_ok Wv {} E (compile_bytes_data_ptr p loc)) /\
  (!c imm p loc. fuel_ok Wv {} E (compile_bytestring_length c imm p loc)) /\
  (!v. fuel_ok Wv {} E (compile_bytestring_copy_len v)) /\
  (!v d. fuel_ok Wv {} E (compile_store_bytestring v d))
Proof
  rpt conj_tac >> rpt gen_tac >>
  simp_tac std_ss [compile_load_storage_def, compile_store_storage_def,
    compile_load_transient_def, compile_load_immutable_def,
    compile_load_calldata_def, compile_nonreentrant_lock_def,
    compile_nonreentrant_unlock_def, compile_copy_memory_dynamic_def,
    compile_with_byte_offset_def, compile_bytes_data_ptr_def,
    compile_bytestring_length_def, compile_bytestring_copy_len_def,
    compile_store_bytestring_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any, fuel_ok_compile_alloc_buffer,
             fuel_ok_compile_ptr_load, fuel_ok_context_copies,
             fuel_ok_compile_store_immutable_bytestring,
             CONJUNCT2 fuel_ok_compile_word_copy_loop] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_lit_byte_offset:
  !op off Wv E. fuel_ok Wv {} E (compile_lit_byte_offset op off)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_lit_byte_offset_def] >>
  Cases_on `off = 0` >> simp[fuel_ok_return] >>
  Cases_on `op` >> simp[fuel_ok_return, fuel_ok_emit_op, is_terminator_def]
QED

Theorem fuel_ok_compile_imm_copy_to_memory:
  !n is_ctor imm src dst off Wv E.
    fuel_ok Wv {} E (compile_imm_copy_to_memory is_ctor imm src dst n off)
Proof
  Induct >> simp_tac std_ss [compile_imm_copy_to_memory_def] >> rpt gen_tac >>
  fuel_auto [fuel_ok_emit_void_any, fuel_ok_compile_lit_byte_offset,
             fuel_ok_compile_imm_load_word] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_imm_store_words:
  !n imm src dst off Wv E.
    fuel_ok Wv {} E (compile_imm_store_words imm src dst n off)
Proof
  Induct >> simp_tac std_ss [compile_imm_store_words_def] >> rpt gen_tac >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_compile_lit_byte_offset,
             fuel_ok_compile_imm_store_word] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_ensure_in_memory:
  !ptr loc mb wc is_ctor imm Wv E.
    fuel_ok Wv {} E (compile_ensure_in_memory ptr loc mb wc is_ctor imm)
Proof
  Cases_on `loc` >> simp_tac (srw_ss()) [compile_ensure_in_memory_def] >>
  rpt gen_tac >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any, fuel_ok_compile_alloc_buffer,
             fuel_ok_context_copies, fuel_ok_compile_imm_copy_to_memory] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_store_immutable:
  !imm src off n Wv E. fuel_ok Wv {} E (compile_store_immutable imm src off n)
Proof
  simp[compile_store_immutable_def, fuel_ok_compile_imm_store_words]
QED

Theorem fuel_ok_compile_zero_memory_loop:
  !p i words Wv E. fuel_ok Wv {} E (compile_zero_memory_loop p i words)
Proof
  recInduct compile_zero_memory_loop_ind >> rpt strip_tac >>
  ONCE_REWRITE_TAC [compile_zero_memory_loop_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_zero_memory:
  !p n Wv E. fuel_ok Wv {} E (compile_zero_memory p n)
Proof
  Cases_on `n` >> simp_tac std_ss [compile_zero_memory_def] >> rpt gen_tac >>
  fuel_auto [fuel_ok_compile_zero_memory_loop]
QED

Theorem fuel_ok_compile_iload_to_memory:
  !n src dst Wv E. fuel_ok Wv {} E (compile_iload_to_memory src dst n)
Proof
  Induct >> simp_tac std_ss [compile_iload_to_memory_def] >> rpt gen_tac >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_gep_to_memory:
  !n base off dst Wv E. fuel_ok Wv {} E (compile_gep_to_memory base off dst n)
Proof
  Induct >> simp_tac std_ss [compile_gep_to_memory_def] >> rpt gen_tac >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_context_misc:
  (!v b. fuel_ok Wv {} E (compile_encode_log_topic v b)) /\
  (!p b. fuel_ok Wv {} E (compile_load_memory p b)) /\
  (!v slot b n. fuel_ok Wv {} E (compile_store_transient v slot b n)) /\
  (!off b n sz opt.
     fuel_ok Wv {} E (compile_load_immutable_ctor off b n sz opt))
Proof
  rpt conj_tac >> rpt gen_tac
  >- (simp_tac std_ss [compile_encode_log_topic_def] >>
      fuel_auto [fuel_ok_emit_op] >> simp[is_terminator_def])
  >- (simp_tac std_ss [compile_load_memory_def] >>
      fuel_auto [fuel_ok_emit_op] >> simp[is_terminator_def])
  >- (simp_tac std_ss [compile_store_transient_def] >>
      fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any,
                 fuel_ok_context_copies] >>
      simp[is_terminator_def]) >>
  Cases_on `opt` >>
  simp_tac (srw_ss()) [compile_load_immutable_ctor_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_compile_alloc_buffer,
             fuel_ok_compile_iload_to_memory, fuel_ok_compile_gep_to_memory] >>
  simp[is_terminator_def]
QED

(* ===== The typed memory copy family ===== *)

Theorem fuel_ok_typed_memory_family:
  (!cenv dst dst_ty src src_ty Wv E.
     fuel_ok Wv {} E (compile_store_memory_typed cenv dst dst_ty src src_ty)) /\
  (!cenv dst src dst_tys src_tys dst_off src_off Wv E.
     fuel_ok Wv {} E
       (compile_typed_copy_fields cenv dst src dst_tys src_tys dst_off src_off)) /\
  (!cenv dst dst_ty src src_ty count Wv E.
     fuel_ok Wv {} E
       (compile_copy_sarray_typed cenv dst dst_ty src src_ty count)) /\
  (!cenv dst dst_ty cap src src_ty Wv E.
     fuel_ok Wv {} E
       (compile_copy_dynarray_typed cenv dst dst_ty cap src src_ty)) /\
  (!cenv dst src dst_fields src_fields dst_off src_off Wv E.
     fuel_ok Wv {} E
       (compile_struct_typed_copy cenv dst src dst_fields src_fields dst_off
          src_off))
Proof
  ho_match_mp_tac compile_store_memory_typed_ind
  >> rpt conj_tac
  >- suspend "dispatch"
  >- suspend "fields_nil"
  >- suspend "fields_mismatch"
  >- suspend "fields_cons"
  >- suspend "sarray"
  >- suspend "dynarray"
  >- suspend "struct_nil"
  >> suspend "struct_cons"
QED

Resume fuel_ok_typed_memory_family[dispatch]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  Cases_on `is_word_type dst_ty`
  >- (simp_tac std_ss [Once compile_store_memory_typed_def] >>
      asm_rewrite_tac[] >>
      fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any] >>
      simp[is_terminator_def]) >>
  Cases_on `is_bytestring_type dst_ty /\ is_bytestring_type src_ty`
  >- (simp_tac std_ss [Once compile_store_memory_typed_def] >>
      asm_rewrite_tac[] >> simp[fuel_ok_context_copies, fuel_ok_context_storage]) >>
  Cases_on `acyclic_struct_metadata cenv.ce_struct_fields`
  >- (Cases_on `dst_ty` >> Cases_on `src_ty` >>
      TRY (rename1 `compile_store_memory_typed cenv dst (ArrayT dt db) src
                      (ArrayT st sb)` >>
           Cases_on `db` >> Cases_on `sb`) >> gvs[] >>
      simp[Once compile_store_memory_typed_def, LET_THM,
           fuel_ok_compile_copy_memory] >> metis_tac[]) >>
  simp_tac std_ss [Once compile_store_memory_typed_def] >>
  asm_rewrite_tac[] >> fuel_auto [fuel_ok_emit_void_any] >>
  simp[is_terminator_def]
QED

Resume fuel_ok_typed_memory_family[fields_nil]:
  simp[Once compile_store_memory_typed_def, fuel_ok_return]
QED

Resume fuel_ok_typed_memory_family[fields_mismatch]:
  simp[Once compile_store_memory_typed_def, fuel_ok_return]
QED

Resume fuel_ok_typed_memory_family[fields_cons]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> gvs[] >>
  simp_tac std_ss [Once compile_store_memory_typed_def] >>
  fuel_auto [fuel_ok_context_copies, fuel_ok_context_storage] >> metis_tac[]
QED

Resume fuel_ok_typed_memory_family[sarray]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  Cases_on `type_memory_bytes cenv dst_ty = type_memory_bytes cenv src_ty /\
            ~is_abi_dynamic cenv.ce_struct_fields dst_ty`
  >- (simp_tac std_ss [Once compile_store_memory_typed_def, LET_THM] >>
      asm_rewrite_tac[] >> simp[fuel_ok_compile_copy_memory]) >>
  irule fuel_ok_compile_copy_sarray_typed >> gvs[] >> metis_tac[]
QED

Resume fuel_ok_typed_memory_family[dynarray]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  Cases_on `type_memory_bytes cenv dst_ty = type_memory_bytes cenv src_ty /\
            dst_ty = src_ty`
  >- (gvs[] >> simp_tac std_ss [Once compile_store_memory_typed_def, LET_THM] >>
      simp[] >>
      fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any,
                 fuel_ok_context_storage] >>
      simp[is_terminator_def]) >>
  irule fuel_ok_compile_copy_dynarray_typed >> gvs[] >> metis_tac[]
QED

Resume fuel_ok_typed_memory_family[struct_nil]:
  simp[Once compile_store_memory_typed_def, fuel_ok_return]
QED

Resume fuel_ok_typed_memory_family[struct_cons]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> gvs[] >>
  simp_tac std_ss [Once compile_store_memory_typed_def] >>
  Cases_on `ALOOKUP src_fields name`
  >- (gvs[] >> fuel_auto [fuel_ok_context_copies, fuel_ok_context_storage] >>
      metis_tac[]) >>
  rename1 `ALOOKUP src_fields name = SOME p` >> PairCases_on `p` >> gvs[] >>
  fuel_auto [fuel_ok_context_copies, fuel_ok_context_storage] >> metis_tac[]
QED

Finalise fuel_ok_typed_memory_family

Theorem fuel_ok_compile_store_memory:
  !cenv src dst dst_ty src_ty Wv E.
    fuel_ok Wv {} E (compile_store_memory cenv src dst dst_ty src_ty)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_store_memory_def] >>
  fuel_auto [fuel_ok_emit_void_any, fuel_ok_context_copies, fuel_ok_context_storage,
             fuel_ok_typed_memory_family, fuel_ok_compile_copy_memory] >>
  simp[is_terminator_def]
QED
