Theory bodyPtrBytestringBuiltinsLiteralAllocationTrace
Ancestors bodyPtrBytestringBuiltinsAllocationTrace
          bodyPtrBytestringBuiltinsUnwrapAllocationTrace exprLowering

Theorem compile_store_byte_chunks_allocation_trace[simp]:
  !p bs off s. allocation_trace s (SND (compile_store_byte_chunks p bs off s))
Proof
  recInduct compile_store_byte_chunks_ind >> rpt strip_tac >>
  simp[Once compile_store_byte_chunks_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[allocation_trace_emit_inst_snd]) >>
  gvs[]
QED

Theorem compile_bytelike_literal_allocation_trace[simp]:
  !bs n s. allocation_trace s (SND (compile_bytelike_literal bs n s))
Proof
  rpt gen_tac >> simp[compile_bytelike_literal_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_literal_vv_allocation_trace[simp]:
  !ty l s. allocation_trace s (SND (compile_literal_vv ty l s))
Proof
  rpt gen_tac >> Cases_on `l` >> simp[compile_literal_vv_def] >>
  TRY (rename1 `BoolL b` >> Cases_on `b` >> simp[compile_literal_vv_def]) >>
  Cases_on `ty` >> simp[compile_literal_vv_def] >>
  TRY (rename1 `BaseT bt` >> Cases_on `bt` >> simp[compile_literal_vv_def]) >>
  TRY (rename1 `BytesT sz` >> Cases_on `sz` >> simp[compile_literal_vv_def]) >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_name_vv_allocation_trace[simp]:
  !ce ty id s. allocation_trace s (SND (compile_name_vv ce ty id s))
Proof
  rpt gen_tac >> simp[compile_name_vv_def] >>
  Cases_on `FLOOKUP ce.ce_vars id` >> simp[] >>
  TRY (rename1 `SOME loc` >> Cases_on `loc` >> simp[]) >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[allocation_trace_emit_inst_snd])
QED
