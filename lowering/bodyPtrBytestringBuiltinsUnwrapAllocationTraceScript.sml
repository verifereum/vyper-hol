Theory bodyPtrBytestringBuiltinsUnwrapAllocationTrace
Ancestors bodyPtrBytestringBuiltinsAllocationTrace exprLowering context
          compileEnv emitHelper list

Theorem allocation_trace_emit_op_snd[simp]:
  allocation_trace s (SND (emit_op opc args s))
Proof
  metis_tac[allocation_trace_emit_op, pairTheory.PAIR]
QED

Theorem allocation_trace_emit_void_snd[simp]:
  allocation_trace s (SND (emit_void opc args s))
Proof
  metis_tac[allocation_trace_emit_void, pairTheory.PAIR]
QED

Theorem allocation_trace_emit_inst_snd:
  (opc = ALLOCA ==> outs = []) ==>
  allocation_trace s (SND (emit_inst opc args outs s))
Proof
  metis_tac[allocation_trace_emit_inst, pairTheory.PAIR]
QED

Theorem allocation_trace_new_block_snd[simp]:
  allocation_trace s (SND (new_block lbl s))
Proof
  metis_tac[allocation_trace_new_block, pairTheory.PAIR]
QED

Theorem allocation_trace_fresh_var_snd[simp]:
  allocation_trace s (SND (fresh_var s))
Proof
  metis_tac[allocation_trace_fresh_var, pairTheory.PAIR]
QED

Theorem allocation_trace_fresh_label_snd[simp]:
  allocation_trace s (SND (fresh_label suffix s))
Proof
  metis_tac[allocation_trace_fresh_label, pairTheory.PAIR]
QED

Theorem compile_imm_load_word_allocation_trace[simp]:
  !is_ctor imm off s.
    allocation_trace s (SND (compile_imm_load_word is_ctor imm off s))
Proof
  rpt gen_tac >> Cases_on `is_ctor` >> Cases_on `imm` >>
  simp[compile_imm_load_word_def] >>
  irule allocation_trace_bind >> simp[]
QED

Theorem compile_imm_store_word_allocation_trace[simp]:
  !imm off v s.
    allocation_trace s (SND (compile_imm_store_word imm off v s))
Proof
  rpt gen_tac >> Cases_on `imm` >>
  simp[compile_imm_store_word_def] >>
  irule allocation_trace_bind >> simp[]
QED

Theorem compile_ptr_load_allocation_trace[simp]:
  !is_ctor imm loc op s.
    allocation_trace s (SND (compile_ptr_load is_ctor imm loc op s))
Proof
  rpt gen_tac >> Cases_on `loc` >> simp[compile_ptr_load_def]
QED

Theorem compile_ptr_store_allocation_trace[simp]:
  !is_ctor imm loc dst v s.
    allocation_trace s (SND (compile_ptr_store is_ctor imm loc dst v s))
Proof
  rpt gen_tac >> Cases_on `loc` >> Cases_on `is_ctor` >>
  simp[compile_ptr_store_def]
QED

Theorem compile_alloc_buffer_allocation_trace[simp]:
  !size s. allocation_trace s (SND (compile_alloc_buffer size s))
Proof
  rpt gen_tac >> simp[compile_alloc_buffer_def] >>
  irule allocation_trace_bind >> simp[]
QED

Theorem compile_lit_byte_offset_allocation_trace[simp]:
  !op off s. allocation_trace s (SND (compile_lit_byte_offset op off s))
Proof
  rpt gen_tac >> Cases_on `off = 0` >> Cases_on `op` >>
  simp[compile_lit_byte_offset_def]
QED

Theorem compile_word_copy_loop_allocation_trace[simp]:
  !src dst count load_loc store_loc is_ctor s.
    allocation_trace s
      (SND (compile_word_copy_loop src dst count load_loc store_loc is_ctor s))
Proof
  rpt gen_tac >>
  Cases_on `word_scale load_loc = 1` >>
  Cases_on `word_scale store_loc = 1` >>
  simp[compile_word_copy_loop_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >>
       simp[allocation_trace_emit_inst_snd])
QED

Theorem compile_storage_to_memory_allocation_trace[simp]:
  !slot buf count s.
    allocation_trace s (SND (compile_storage_to_memory slot buf count s))
Proof
  simp[compile_storage_to_memory_def]
QED

Theorem compile_transient_to_memory_allocation_trace[simp]:
  !slot buf count s.
    allocation_trace s (SND (compile_transient_to_memory slot buf count s))
Proof
  simp[compile_transient_to_memory_def]
QED

Theorem compile_imm_copy_to_memory_allocation_trace[simp]:
  !is_ctor imm src dst count off s.
    allocation_trace s
      (SND (compile_imm_copy_to_memory is_ctor imm src dst count off s))
Proof
  ntac 4 gen_tac >> Induct >> simp[compile_imm_copy_to_memory_def] >> rpt gen_tac >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem compile_ensure_in_memory_allocation_trace[simp]:
  !op loc bytes count is_ctor imm s.
    allocation_trace s
      (SND (compile_ensure_in_memory op loc bytes count is_ctor imm s))
Proof
  map_every qx_gen_tac [`op`, `loc`, `bytes`, `nwords`, `is_ctor`, `imm`, `s`] >>
  Cases_on `loc` >> Cases_on `nwords = 1` >>
  simp[compile_ensure_in_memory_def] >>
  rpt (rpt gen_tac >> FIRST [conj_tac, irule allocation_trace_bind,
              irule allocation_trace_ignore_bind] >> simp[])
QED

Theorem unwrap_value_allocation_trace[simp]:
  !cenv vv s. allocation_trace s (SND (unwrap_value cenv vv s))
Proof
  rpt gen_tac >> Cases_on `vv` >> simp[unwrap_value_def] >>
  rename1 `is_word_type ty` >> Cases_on `is_word_type ty` >>
  simp[] >> Cases_on `p.ptr_location` >> simp[]
QED
