Theory bodyPtrBytestringBuiltinsAggregateConsumer
Ancestors bodyPtrBytestringBuiltinsUnwrapEntry
          bodyPtrBytestringBuiltinsUnwrapAllocationTrace
          bodyPtrBytestringBuiltinsMemoryEntry
          bodyPtrBytestringBuiltinsStoreAllocationTrace
          bodyPtrBytestringBuiltinsAllocationTrace
          exprLowering context compileEnv emitHelper list

Theorem zero_layout_not_bytestring:
  !cenv ty. type_memory_bytes cenv ty = 0 ==> ~is_bytestring_type ty
Proof
  rpt gen_tac >> Cases_on `ty` >> simp[is_bytestring_type_def] >>
  rename1 `BaseT b` >> Cases_on `b` >>
  simp[is_bytestring_type_def, type_memory_bytes_def] >>
  rename1 `BytesT bound` >> Cases_on `bound` >>
  simp[is_bytestring_type_def, type_memory_bytes_def]
QED

Theorem compile_store_memory_zero_layout:
  !cenv ty src dst.
  ~is_word_type ty /\ type_memory_bytes cenv ty = 0 ==>
  compile_store_memory cenv src dst ty ty = comp_return ()
Proof
  rpt gen_tac >> strip_tac >>
  drule zero_layout_not_bytestring >> strip_tac >>
  simp[compile_store_memory_def, compile_copy_memory_def]
QED

Theorem unwrap_store_zero_code_entry:
  !cenv ty p dst s op u r t.
  ~is_word_type ty /\ p.ptr_location = LocCode /\ type_memory_bytes cenv ty = 0 /\
  image_entry s /\
  unwrap_value cenv (LocatedValue ty p) s = (op,u) /\
  compile_store_memory cenv op dst ty ty u = (r,t) ==>
  image_entry t /\ allocation_trace s t
Proof
  rpt gen_tac >> strip_tac >>
  `compile_store_memory cenv op dst ty ty = comp_return ()` by
    metis_tac[compile_store_memory_zero_layout] >>
  gvs[comp_return_def] >>
  conj_tac
  >- (qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
      simp[unwrap_value_def, compile_ensure_in_memory_def, comp_bind_def] >>
      Cases_on `compile_alloc_buffer 0 s` >>
      simp[compile_imm_copy_to_memory_def, comp_return_def, comp_ignore_bind_def, comp_bind_def] >>
      metis_tac[memory_entry_alloc_buffer, pairTheory.SND]) >>
  metis_tac[unwrap_value_allocation_trace, pairTheory.SND]
QED

Theorem unwrap_store_memory_entry:
  !cenv vv dst dty sty s op u r t.
  image_entry s /\ (!b. ~tail_alloc b s.cs_current_insts) /\
  (!ty p. vv = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location = LocCode /\
    type_memory_bytes cenv ty = 0 ==> dty = ty /\ sty = ty) /\
  unwrap_value cenv vv s = (op,u) /\
  compile_store_memory cenv op dst dty sty u = (r,t) ==>
  image_entry t /\ allocation_trace s t
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `?ty p. vv = LocatedValue ty p /\ ~is_word_type ty /\
    p.ptr_location = LocCode /\ type_memory_bytes cenv ty = 0`
  >- (pop_assum strip_assume_tac >> gvs[] >>
      metis_tac[unwrap_store_zero_code_entry]) >>
  `!ty p. vv = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location = LocCode ==>
     0 < type_memory_bytes cenv ty` by metis_tac[arithmeticTheory.NOT_ZERO_LT_ZERO] >>
  `image_entry u /\ (!b. ~tail_alloc b u.cs_current_insts) /\ allocation_trace s u` by
    metis_tac[unwrap_value_entry_trace_result] >>
  `image_entry t` by metis_tac[compile_store_memory_entry, pairTheory.SND] >>
  `allocation_trace u t` by
    metis_tac[compile_store_memory_allocation_trace, pairTheory.SND] >>
  metis_tac[allocation_trace_trans]
QED
