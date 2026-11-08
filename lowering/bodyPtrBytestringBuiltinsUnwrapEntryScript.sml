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

Theorem entry_reset_bind:
  !f g s.
  image_entry (SND (f s)) /\
  (!v u. image_entry u ==>
    image_entry (SND (g v u)) /\
    (!b. ~tail_alloc b (SND (g v u)).cs_current_insts)) ==>
  image_entry (SND (comp_bind f g s)) /\
  (!b. ~tail_alloc b (SND (comp_bind f g s)).cs_current_insts)
Proof
  rpt gen_tac >> Cases_on `f s` >> simp[comp_bind_def] >> metis_tac[]
QED

Theorem compile_imm_copy_zero_entry:
  !ctor imm src dst n s. image_entry s ==>
  image_entry (SND (compile_imm_copy_to_memory ctor imm src dst n 0 s)) /\
  (0 < n ==> !b. ~tail_alloc b
    (SND (compile_imm_copy_to_memory ctor imm src dst n 0 s)).cs_current_insts)
Proof
  rpt gen_tac >> Cases_on `n` >> strip_tac >>
  once_rewrite_tac[compile_imm_copy_to_memory_def] >>
  simp[compile_lit_byte_offset_def, comp_return_def, comp_bind_def] >>
  Cases_on `compile_imm_load_word ctor imm src s` >> simp[] >>
  drule compile_imm_load_word_entry >>
  disch_then (qspecl_then [`ctor`, `imm`, `src`] mp_tac) >> simp[] >> strip_tac >>
  rpt (rpt gen_tac >> FIRST [disch_then strip_assume_tac,
    irule memory_entry_bind, irule memory_entry_ignore_bind, conj_tac] >>
    simp[compile_lit_byte_offset_memory_entry, memory_entry_emit_void,
      compile_imm_copy_to_memory_memory_entry])
QED

Theorem entry_fresh_label[simp]:
  !p s. image_entry (SND (fresh_label p s)) <=> image_entry s
Proof simp[fresh_label_def, image_entry_def]
QED

Theorem entry_fresh_var[simp]:
  !s. image_entry (SND (fresh_var s)) <=> image_entry s
Proof simp[fresh_var_def, image_entry_def]
QED

Theorem memory_entry_emit_inst_barrier:
  !opc args outs s. opc <> ALLOCA /\ opc <> ADD /\ opc <> MSTORE /\ image_entry s ==>
  image_entry (SND (emit_inst opc args outs s)) /\
  (!b. ~tail_alloc b (SND (emit_inst opc args outs s)).cs_current_insts)
Proof
  simp[emit_inst_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, emit_def, image_entry_def, tail_alloc_append,
    image_bad_barrier, image_pending_barrier] >>
  simp[mk_inst_def] >> simp[GSYM mk_inst_def, image_bad_nonstore_append,
    image_pending2_def, image_pending3_def, mk_inst_def]
QED

Theorem memory_reset_bind:
  !f g s.
  (image_entry (SND (f s)) /\
    (!b. ~tail_alloc b (SND (f s)).cs_current_insts)) /\
  (!v u. image_entry u /\ (!b. ~tail_alloc b u.cs_current_insts) ==>
    image_entry (SND (g v u)) /\
    (!b. ~tail_alloc b (SND (g v u)).cs_current_insts)) ==>
  image_entry (SND (comp_bind f g s)) /\
  (!b. ~tail_alloc b (SND (comp_bind f g s)).cs_current_insts)
Proof
  rpt gen_tac >> Cases_on `f s` >> simp[comp_bind_def] >> metis_tac[]
QED

Theorem compile_word_copy_loop_entry:
  !src dst n load store ctor s. image_entry s ==>
  image_entry (SND (compile_word_copy_loop src dst n load store ctor s)) /\
  (!b. ~tail_alloc b (SND (compile_word_copy_loop src dst n load store ctor s)).cs_current_insts)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `word_scale load = 1` >> Cases_on `word_scale store = 1` >>
  simp[compile_word_copy_loop_def] >>
  ntac 4 (irule entry_reset_bind >> simp[] >> rpt gen_tac >> strip_tac) >>
  simp[comp_ignore_bind_def] >>
  irule memory_reset_bind >> simp[memory_entry_emit_inst_barrier] >>
  rpt (rpt gen_tac >> FIRST [disch_then strip_assume_tac,
    irule memory_entry_bind, irule memory_entry_ignore_bind, conj_tac] >>
    simp[memory_entry_emit_inst, memory_entry_emit_op, memory_entry_emit_void,
      memory_entry_new_block, compile_ptr_load_memory_entry, compile_ptr_store_memory_entry])
QED

Theorem memory_entry_mstore:
  !args s. image_entry s ==>
  image_entry (SND (emit_void MSTORE args s)) /\
  (!b. ~tail_alloc b (SND (emit_void MSTORE args s)).cs_current_insts)
Proof
  rpt gen_tac >> strip_tac >>
  `~image_bad s.cs_current_insts /\ ~image_pending3 s.cs_current_insts` by
    gvs[image_entry_def] >>
  simp[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, emit_def, image_entry_def, tail_alloc_append,
    image_pending2_def, image_pending3_def, mk_inst_def] >>
  gvs[image_entry_def] >> simp[GSYM mk_inst_def] >>
  metis_tac[image_bad_mstore]
QED

Theorem entry_ignore_return_snd[simp]:
  !f v s. SND (comp_ignore_bind f (comp_return v) s) = SND (f s)
Proof
  rpt gen_tac >> Cases_on `f s` >>
  simp[comp_ignore_bind_def, comp_bind_def, comp_return_def]
QED

Theorem compile_ensure_noncode_memory_entry:
  !ptr loc bytes n ctor imm s.
  loc <> LocCode /\ image_entry s /\ (!b. ~tail_alloc b s.cs_current_insts) ==>
  image_entry (SND (compile_ensure_in_memory ptr loc bytes n ctor imm s)) /\
  (!b. ~tail_alloc b (SND (compile_ensure_in_memory ptr loc bytes n ctor imm s)).cs_current_insts)
Proof
  rpt gen_tac >> Cases_on `loc` >> simp[compile_ensure_in_memory_def]
  >~ [`emit_op CALLDATALOAD`]
  >- (strip_tac >> irule memory_entry_bind >> simp[memory_entry_emit_op] >>
      rpt gen_tac >> strip_tac >> irule entry_reset_bind >>
      simp[memory_entry_alloc_buffer] >> rpt gen_tac >> strip_tac >>
      simp[comp_ignore_bind_def] >> irule memory_reset_bind >>
      simp[memory_entry_mstore] >>
      rpt (rpt gen_tac >> FIRST [disch_then strip_assume_tac,
        irule memory_entry_bind, irule memory_entry_ignore_bind, conj_tac] >>
        simp[memory_entry_emit_op, memory_entry_emit_void])) >>
  strip_tac >> irule entry_reset_bind >> simp[memory_entry_alloc_buffer] >>
  rpt gen_tac >> strip_tac >> Cases_on `n = 1` >>
  simp[compile_storage_to_memory_def, compile_transient_to_memory_def,
    compile_word_copy_loop_entry] >>
  irule memory_reset_bind >> simp[memory_entry_emit_barrier] >>
  rpt gen_tac >> strip_tac >> simp[memory_entry_emit_void]
QED

Theorem compile_ensure_code_entry:
  !ptr bytes n ctor imm s. image_entry s ==>
  image_entry (SND (compile_ensure_in_memory ptr LocCode bytes n ctor imm s)) /\
  (0 < bytes ==> !b. ~tail_alloc b
    (SND (compile_ensure_in_memory ptr LocCode bytes n ctor imm s)).cs_current_insts)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `compile_alloc_buffer bytes s` >>
  `image_entry r` by metis_tac[memory_entry_alloc_buffer, pairTheory.SND] >>
  simp[compile_ensure_in_memory_def, comp_bind_def] >>
  mp_tac compile_imm_copy_zero_entry >>
  disch_then (qspecl_then [`ctor`, `imm`, `ptr'`, `q.buf_operand`] mp_tac) >>
  disch_then (qspec_then `(bytes + 31) DIV 32` mp_tac) >>
  disch_then (qspec_then `r` mp_tac) >> simp[] >>
  `0 < bytes ==> 0 < (bytes + 31) DIV 32` by intLib.COOPER_TAC >>
  metis_tac[]
QED

Theorem unwrap_value_entry:
  !cenv vv s. image_entry s /\ (!b. ~tail_alloc b s.cs_current_insts) ==>
    image_entry (SND (unwrap_value cenv vv s))
Proof
  rpt gen_tac >> Cases_on `vv` >> simp[unwrap_value_def, comp_return_def] >>
  strip_tac >> Cases_on `is_word_type t` >>
  simp[compile_ptr_load_memory_entry] >>
  Cases_on `p.ptr_location` >>
  simp[comp_return_def, compile_ensure_noncode_memory_entry, compile_ensure_code_entry]
QED

Theorem unwrap_value_memory_entry:
  !cenv vv s.
  image_entry s /\ (!b. ~tail_alloc b s.cs_current_insts) /\
  (!ty p. vv = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location = LocCode ==>
      0 < type_memory_bytes cenv ty) ==>
  image_entry (SND (unwrap_value cenv vv s)) /\
  (!b. ~tail_alloc b (SND (unwrap_value cenv vv s)).cs_current_insts)
Proof
  rpt gen_tac >> Cases_on `vv` >> simp[unwrap_value_def, comp_return_def] >>
  strip_tac >> Cases_on `is_word_type t` >>
  simp[compile_ptr_load_memory_entry] >>
  Cases_on `p.ptr_location` >>
  gvs[comp_return_def, compile_ensure_noncode_memory_entry, compile_ensure_code_entry]
QED

Theorem unwrap_value_entry_result:
  !cenv vv s op t. image_entry s /\ (!b. ~tail_alloc b s.cs_current_insts) /\
    unwrap_value cenv vv s = (op,t) ==> image_entry t
Proof
  metis_tac[unwrap_value_entry, pairTheory.SND]
QED

Theorem unwrap_value_entry_trace_result:
  !cenv vv s op t.
  image_entry s /\ (!b. ~tail_alloc b s.cs_current_insts) /\
  (!ty p. vv = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location = LocCode ==>
      0 < type_memory_bytes cenv ty) /\
  unwrap_value cenv vv s = (op,t) ==>
  image_entry t /\ (!b. ~tail_alloc b t.cs_current_insts) /\ allocation_trace s t
Proof
  metis_tac[unwrap_value_memory_entry, unwrap_value_allocation_trace, pairTheory.SND]
QED

(* This refutes the unqualified no-tail helper contract, not the frozen
   body judgment: an empty code tuple emits only its zero-byte allocation. *)
Theorem unwrap_zero_code_tail_example:
  !cenv s.
  image_entry (s with <|cs_current_insts := []; cs_blocks := []|>) /\
  (!b. ~tail_alloc b (s with <|cs_current_insts := []; cs_blocks := []|>).cs_current_insts) /\
  tail_alloc (Var ("%" ++ toString s.cs_next_var))
    (SND (unwrap_value cenv (LocatedValue (TupleT []) (mk_ptr (Lit 0w) LocCode))
       (s with <|cs_current_insts := []; cs_blocks := []|>))).cs_current_insts
Proof
  simp[unwrap_value_def, is_word_type_def, mk_ptr_def, type_memory_bytes_def,
    compile_ensure_in_memory_def, compile_alloc_buffer_def,
    compile_imm_copy_to_memory_def, emit_op_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def,
    image_entry_def, image_bad_def, image_pending2_def, image_pending3_def,
    tail_alloc_def] >> metis_tac[APPEND_NIL, APPEND]
QED
