Theory bodyPtrBytestringBuiltinsUnwrapEntry
Ancestors bodyPtrBytestringBuiltinsMemoryEntry
          bodyPtrBytestringBuiltinsUnwrapAllocationTrace
          bodyPtrBytestringBuiltinsImageTupleHistory
          bodyPtrBytestringBuiltinsImageFrontier
          bodyPtrBytestringBuiltinsImageIfExp
          context exprLowering compileEnv emitHelper venomInst list

Theorem compile_imm_load_word_memory_entry:
  !ctor imm off s. image_entry s /\ (!b. ~tail_alloc b s.cs_current_insts) ==>
  image_entry (SND (compile_imm_load_word ctor imm off s)) /\
  (!b. ~tail_alloc b (SND (compile_imm_load_word ctor imm off s)).cs_current_insts)
Proof
  rpt gen_tac >> Cases_on `ctor` >> Cases_on `imm` >>
  simp[compile_imm_load_word_def, memory_entry_emit_op] >> strip_tac >>
  irule memory_entry_bind >> simp[memory_entry_emit_op]
QED

Theorem compile_imm_store_word_memory_entry:
  !imm off op s. image_entry s /\ (!b. ~tail_alloc b s.cs_current_insts) ==>
  image_entry (SND (compile_imm_store_word imm off op s)) /\
  (!b. ~tail_alloc b (SND (compile_imm_store_word imm off op s)).cs_current_insts)
Proof
  rpt gen_tac >> Cases_on `imm` >>
  simp[compile_imm_store_word_def, memory_entry_emit_void] >> strip_tac >>
  irule memory_entry_bind >> simp[memory_entry_emit_op, memory_entry_emit_void]
QED

Theorem compile_ptr_load_memory_entry:
  !ctor imm loc op s. image_entry s /\ (!b. ~tail_alloc b s.cs_current_insts) ==>
  image_entry (SND (compile_ptr_load ctor imm loc op s)) /\
  (!b. ~tail_alloc b (SND (compile_ptr_load ctor imm loc op s)).cs_current_insts)
Proof
  rpt gen_tac >> Cases_on `loc` >>
  simp[compile_ptr_load_def, memory_entry_emit_op, compile_imm_load_word_memory_entry]
QED

Theorem compile_ptr_store_memory_entry:
  !ctor imm loc dst op s. image_entry s /\ (!b. ~tail_alloc b s.cs_current_insts) ==>
  image_entry (SND (compile_ptr_store ctor imm loc dst op s)) /\
  (!b. ~tail_alloc b (SND (compile_ptr_store ctor imm loc dst op s)).cs_current_insts)
Proof
  rpt gen_tac >> Cases_on `loc` >> Cases_on `ctor` >>
  simp[compile_ptr_store_def, memory_entry_emit_void, compile_imm_store_word_memory_entry]
QED

Theorem compile_lit_byte_offset_memory_entry:
  !op off s. image_entry s /\ (!b. ~tail_alloc b s.cs_current_insts) ==>
  image_entry (SND (compile_lit_byte_offset op off s)) /\
  (!b. ~tail_alloc b (SND (compile_lit_byte_offset op off s)).cs_current_insts)
Proof
  rpt gen_tac >> Cases_on `off = 0` >> Cases_on `op` >>
  simp[compile_lit_byte_offset_def, memory_entry_emit_op]
QED

Theorem compile_word_copy_loop_memory_entry:
  !src dst n load store ctor s.
  image_entry s /\ (!b. ~tail_alloc b s.cs_current_insts) ==>
  image_entry (SND (compile_word_copy_loop src dst n load store ctor s)) /\
  (!b. ~tail_alloc b (SND (compile_word_copy_loop src dst n load store ctor s)).cs_current_insts)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `word_scale load = 1` >> Cases_on `word_scale store = 1` >>
  simp[compile_word_copy_loop_def] >>
  rpt (rpt gen_tac >> FIRST [disch_then strip_assume_tac,
    irule memory_entry_bind, irule memory_entry_ignore_bind, conj_tac] >>
    simp[memory_entry_emit_inst, memory_entry_emit_op, memory_entry_emit_void,
      memory_entry_new_block, compile_ptr_load_memory_entry, compile_ptr_store_memory_entry])
QED

Theorem compile_imm_copy_to_memory_memory_entry:
  !ctor imm src dst n off s.
  image_entry s /\ (!b. ~tail_alloc b s.cs_current_insts) ==>
  image_entry (SND (compile_imm_copy_to_memory ctor imm src dst n off s)) /\
  (!b. ~tail_alloc b (SND (compile_imm_copy_to_memory ctor imm src dst n off s)).cs_current_insts)
Proof
  ntac 4 gen_tac >> Induct >> rpt gen_tac >> strip_tac >>
  once_rewrite_tac[compile_imm_copy_to_memory_def] >> simp[] >>
  rpt (rpt gen_tac >> FIRST [disch_then strip_assume_tac,
    irule memory_entry_bind, irule memory_entry_ignore_bind, conj_tac] >>
    simp[memory_entry_emit_void, compile_lit_byte_offset_memory_entry,
      compile_imm_load_word_memory_entry])
QED

Theorem image_bad_nonstore_append:
  !xs i opc args outs. opc <> MSTORE ==>
  (image_bad (xs ++ [mk_inst i opc args outs]) <=> image_bad xs)
Proof
  rpt gen_tac >> strip_tac >>
  `!a b c d p q. [mk_inst i opc args outs] <> p ++ [a;b;c;d] ++ q` by
    (rpt strip_tac >>
     qpat_x_assum `[_] = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[]) >>
  simp[image_bad_def, bodyPtrBytestringBuiltinsWindowsTheory.four_window_append, mk_inst_def]
QED

Theorem memory_entry_alloca:
  !args s. image_entry s ==>
  image_entry (SND (emit_op ALLOCA args s))
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_var_def, fresh_id_def, emit_def, image_entry_def,
    image_bad_nonstore_append, image_pending2_def, image_pending3_def, mk_inst_def] >>
  simp[GSYM mk_inst_def, image_bad_nonstore_append]
QED

Theorem memory_entry_alloc_buffer:
  !n s. image_entry s ==> image_entry (SND (compile_alloc_buffer n s))
Proof
  simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `emit_op ALLOCA [Lit (n2w n)] s` >>
  gvs[] >> metis_tac[memory_entry_alloca, pairTheory.SND]
QED

Theorem compile_imm_load_word_entry:
  !ctor imm off s. image_entry s ==>
  image_entry (SND (compile_imm_load_word ctor imm off s)) /\
  (!b. ~tail_alloc b (SND (compile_imm_load_word ctor imm off s)).cs_current_insts)
Proof
  rpt gen_tac >> Cases_on `ctor` >> Cases_on `imm` >>
  simp[compile_imm_load_word_def, emit_op_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def,
    image_entry_def, tail_alloc_append, image_pending2_def, image_pending3_def,
    mk_inst_def] >>
  simp[GSYM mk_inst_def, image_bad_nonstore_append]
QED

Theorem memory_entry_emit_barrier:
  !opc args s. opc <> ALLOCA /\ opc <> ADD /\ opc <> MSTORE /\ image_entry s ==>
  image_entry (SND (emit_op opc args s)) /\
  (!b. ~tail_alloc b (SND (emit_op opc args s)).cs_current_insts)
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_var_def, fresh_id_def, emit_def, image_entry_def, tail_alloc_append,
    image_bad_barrier, image_pending_barrier] >>
  simp[mk_inst_def] >> simp[GSYM mk_inst_def, image_bad_nonstore_append,
    image_pending2_def, image_pending3_def, mk_inst_def]
QED
