Theory bodyPtrBytestringBuiltinsMemoryEntry
Ancestors bodyPtrBytestringBuiltinsImageTupleHistory
          bodyPtrBytestringBuiltinsImageFrontier
          bodyPtrBytestringBuiltinsImageIfExp
          bodyPtrBytestringBuiltinsWindows
          bodyPtrBytestringBuiltinsImageProtectedIdentity
          compileEnv emitHelper context venomInst list rich_list

Theorem image_pending2_predecessor:
  !xs i opc args outs. image_pending2 (xs ++ [mk_inst i opc args outs]) ==>
    ?b. tail_alloc b xs
Proof
  simp[image_pending2_def, tail_alloc_def, mk_inst_def] >> metis_tac[]
QED

Theorem image_pending3_nonalloc:
  !xs i opc args outs. opc <> ALLOCA ==>
    ~image_pending3 (xs ++ [mk_inst i opc args outs])
Proof
  simp[image_pending3_def, mk_inst_def]
QED

Theorem image_entry_nonalloc_append:
  !s i opc args outs.
  opc <> ALLOCA /\ image_entry s /\ (!b. ~tail_alloc b s.cs_current_insts) ==>
  image_entry (s with cs_current_insts := s.cs_current_insts ++ [mk_inst i opc args outs]) /\
  (!b. ~tail_alloc b (s.cs_current_insts ++ [mk_inst i opc args outs]))
Proof
  rpt gen_tac >> strip_tac >> reverse conj_tac
  >- simp[tail_alloc_append, mk_inst_def] >>
  gvs[image_entry_def] >>
  `~image_pending2 (s.cs_current_insts ++ [mk_inst i opc args outs])` by
    metis_tac[image_pending2_predecessor] >>
  simp[image_pending3_nonalloc] >>
  Cases_on `opc = ADD` >- gvs[] >>
  Cases_on `opc = MSTORE` >- metis_tac[image_bad_mstore] >>
  simp[image_bad_barrier, emitHelperPropsTheory.mk_inst_opcode]
QED

Theorem memory_entry_emit_inst:
  !opc args outs s.
  opc <> ALLOCA /\ image_entry s /\ (!b. ~tail_alloc b s.cs_current_insts) ==>
  image_entry (SND (emit_inst opc args outs s)) /\
  (!b. ~tail_alloc b (SND (emit_inst opc args outs s)).cs_current_insts)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all image_entry_nonalloc_append >>
  disch_then (qspec_then `s.cs_next_id` mp_tac) >>
  simp[emit_inst_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, emit_def, image_entry_def]
QED

Theorem memory_entry_emit_void:
  !opc args s.
  opc <> ALLOCA /\ image_entry s /\ (!b. ~tail_alloc b s.cs_current_insts) ==>
  image_entry (SND (emit_void opc args s)) /\
  (!b. ~tail_alloc b (SND (emit_void opc args s)).cs_current_insts)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all image_entry_nonalloc_append >>
  disch_then (qspec_then `s.cs_next_id` mp_tac) >>
  simp[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, emit_def, image_entry_def]
QED

Theorem memory_entry_emit_op:
  !opc args s.
  opc <> ALLOCA /\ image_entry s /\ (!b. ~tail_alloc b s.cs_current_insts) ==>
  image_entry (SND (emit_op opc args s)) /\
  (!b. ~tail_alloc b (SND (emit_op opc args s)).cs_current_insts)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all image_entry_nonalloc_append >>
  disch_then (qspec_then `s.cs_next_id` mp_tac) >>
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def, image_entry_def]
QED

Theorem memory_entry_new_block:
  !lbl s. image_entry s ==>
  image_entry (SND (new_block lbl s)) /\
  (!b. ~tail_alloc b (SND (new_block lbl s)).cs_current_insts)
Proof
  simp[new_block_def, image_entry_def, tail_alloc_def]
QED

Theorem memory_entry_bind:
  !f g s.
  (!u. image_entry u /\ (!b. ~tail_alloc b u.cs_current_insts) ==>
    image_entry (SND (f u)) /\ (!b. ~tail_alloc b (SND (f u)).cs_current_insts)) /\
  (!v u. image_entry u /\ (!b. ~tail_alloc b u.cs_current_insts) ==>
    image_entry (SND (g v u)) /\ (!b. ~tail_alloc b (SND (g v u)).cs_current_insts)) /\
  image_entry s /\ (!b. ~tail_alloc b s.cs_current_insts) ==>
  image_entry (SND (comp_bind f g s)) /\
  (!b. ~tail_alloc b (SND (comp_bind f g s)).cs_current_insts)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `f s` >> gvs[comp_bind_def] >>
  qpat_x_assum `!u. _` (qspec_then `s` mp_tac) >> simp[] >> strip_tac >>
  first_x_assum irule >> simp[]
QED

Theorem memory_entry_ignore_bind:
  !f g s.
  (!u. image_entry u /\ (!b. ~tail_alloc b u.cs_current_insts) ==>
    image_entry (SND (f u)) /\ (!b. ~tail_alloc b (SND (f u)).cs_current_insts)) /\
  (!u. image_entry u /\ (!b. ~tail_alloc b u.cs_current_insts) ==>
    image_entry (SND (g u)) /\ (!b. ~tail_alloc b (SND (g u)).cs_current_insts)) /\
  image_entry s /\ (!b. ~tail_alloc b s.cs_current_insts) ==>
  image_entry (SND (comp_ignore_bind f g s)) /\
  (!b. ~tail_alloc b (SND (comp_ignore_bind f g s)).cs_current_insts)
Proof
  rpt gen_tac >> strip_tac >> simp[comp_ignore_bind_def] >>
  irule memory_entry_bind >> simp[]
QED

Theorem memory_entry_return[simp]:
  !v s. image_entry s /\ (!b. ~tail_alloc b s.cs_current_insts) ==>
  image_entry (SND (comp_return v s)) /\
  (!b. ~tail_alloc b (SND (comp_return v s)).cs_current_insts)
Proof simp[comp_return_def]
QED

Theorem memory_entry_fresh_var[simp]:
  !s. image_entry s /\ (!b. ~tail_alloc b s.cs_current_insts) ==>
  image_entry (SND (fresh_var s)) /\
  (!b. ~tail_alloc b (SND (fresh_var s)).cs_current_insts)
Proof simp[fresh_var_def, image_entry_def]
QED

Theorem memory_entry_fresh_label[simp]:
  !p s. image_entry s /\ (!b. ~tail_alloc b s.cs_current_insts) ==>
  image_entry (SND (fresh_label p s)) /\
  (!b. ~tail_alloc b (SND (fresh_label p s)).cs_current_insts)
Proof simp[fresh_label_def, image_entry_def]
QED

Theorem compile_copy_memory_entry:
  !dst src n s. image_entry s /\ (!b. ~tail_alloc b s.cs_current_insts) ==>
  image_entry (SND (compile_copy_memory dst src n s)) /\
  (!b. ~tail_alloc b (SND (compile_copy_memory dst src n s)).cs_current_insts)
Proof
  rpt gen_tac >> Cases_on `n` >>
  simp[compile_copy_memory_def, memory_entry_emit_void]
QED

Theorem compile_copy_memory_dynamic_entry:
  !dst src len s. image_entry s /\ (!b. ~tail_alloc b s.cs_current_insts) ==>
  image_entry (SND (compile_copy_memory_dynamic dst src len s)) /\
  (!b. ~tail_alloc b (SND (compile_copy_memory_dynamic dst src len s)).cs_current_insts)
Proof simp[compile_copy_memory_dynamic_def, memory_entry_emit_void]
QED

Theorem compile_with_byte_offset_entry:
  !base off s. image_entry s /\ (!b. ~tail_alloc b s.cs_current_insts) ==>
  image_entry (SND (compile_with_byte_offset base off s)) /\
  (!b. ~tail_alloc b (SND (compile_with_byte_offset base off s)).cs_current_insts)
Proof
  rpt gen_tac >> Cases_on `off = 0` >>
  simp[compile_with_byte_offset_def, memory_entry_emit_op]
QED

Theorem compile_bytestring_copy_len_entry:
  !src s. image_entry s /\ (!b. ~tail_alloc b s.cs_current_insts) ==>
  image_entry (SND (compile_bytestring_copy_len src s)) /\
  (!b. ~tail_alloc b (SND (compile_bytestring_copy_len src s)).cs_current_insts)
Proof
  rpt gen_tac >> strip_tac >> simp[compile_bytestring_copy_len_def] >>
  irule memory_entry_bind >> simp[memory_entry_emit_op] >>
  rpt gen_tac >> strip_tac >> irule memory_entry_bind >>
  simp[memory_entry_emit_op] >> rpt gen_tac >> strip_tac >>
  irule memory_entry_bind >> simp[memory_entry_emit_op]
QED

Theorem compile_store_bytestring_entry:
  !src dst s. image_entry s /\ (!b. ~tail_alloc b s.cs_current_insts) ==>
  image_entry (SND (compile_store_bytestring src dst s)) /\
  (!b. ~tail_alloc b (SND (compile_store_bytestring src dst s)).cs_current_insts)
Proof
  rpt gen_tac >> strip_tac >> simp[compile_store_bytestring_def] >>
  irule memory_entry_bind >>
  simp[compile_bytestring_copy_len_entry, memory_entry_emit_void]
QED

Theorem typed_copy_memory_entry:
  (!cenv dst dt src st s.
    image_entry s /\ (!b. ~tail_alloc b s.cs_current_insts) ==>
    image_entry (SND (compile_store_memory_typed cenv dst dt src st s)) /\
    (!b. ~tail_alloc b (SND (compile_store_memory_typed cenv dst dt src st s)).cs_current_insts)) /\
  (!cenv dst src dts sts doff soff s.
    image_entry s /\ (!b. ~tail_alloc b s.cs_current_insts) ==>
    image_entry (SND (compile_typed_copy_fields cenv dst src dts sts doff soff s)) /\
    (!b. ~tail_alloc b (SND (compile_typed_copy_fields cenv dst src dts sts doff soff s)).cs_current_insts)) /\
  (!cenv dst dt src st n s.
    image_entry s /\ (!b. ~tail_alloc b s.cs_current_insts) ==>
    image_entry (SND (compile_copy_sarray_typed cenv dst dt src st n s)) /\
    (!b. ~tail_alloc b (SND (compile_copy_sarray_typed cenv dst dt src st n s)).cs_current_insts)) /\
  (!cenv dst dt cap src st s.
    image_entry s /\ (!b. ~tail_alloc b s.cs_current_insts) ==>
    image_entry (SND (compile_copy_dynarray_typed cenv dst dt cap src st s)) /\
    (!b. ~tail_alloc b (SND (compile_copy_dynarray_typed cenv dst dt cap src st s)).cs_current_insts)) /\
  (!cenv dst src dfs sfs doff soff s.
    image_entry s /\ (!b. ~tail_alloc b s.cs_current_insts) ==>
    image_entry (SND (compile_struct_typed_copy cenv dst src dfs sfs doff soff s)) /\
    (!b. ~tail_alloc b (SND (compile_struct_typed_copy cenv dst src dfs sfs doff soff s)).cs_current_insts))
Proof
  ho_match_mp_tac compile_store_memory_typed_ind >>
  conj_tac >- suspend "dispatch" >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  once_rewrite_tac[compile_store_memory_typed_def] >> simp[] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  TRY (pairarg_tac >> gvs[]) >>
  rpt (rpt gen_tac >> FIRST [disch_then strip_assume_tac, irule memory_entry_bind,
              irule memory_entry_ignore_bind, IF_CASES_TAC, conj_tac] >>
       simp[memory_entry_emit_inst, memory_entry_emit_op, memory_entry_emit_void,
            memory_entry_new_block, compile_copy_memory_entry,
            compile_copy_memory_dynamic_entry, compile_with_byte_offset_entry]) >> gvs[]
QED

Resume typed_copy_memory_entry[dispatch]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  once_rewrite_tac[compile_store_memory_typed_def] >> simp[] >>
  IF_CASES_TAC >- (irule memory_entry_bind >>
    simp[memory_entry_emit_op, memory_entry_emit_void]) >>
  IF_CASES_TAC >- simp[compile_store_bytestring_entry] >>
  IF_CASES_TAC >- simp[memory_entry_emit_void] >>
  Cases_on `dt` >> simp[compile_copy_memory_entry] >>
  Cases_on `st` >> gvs[compile_copy_memory_entry] >>
  BasicProvers.TOP_CASE_TAC >> gvs[compile_copy_memory_entry] >>
  BasicProvers.TOP_CASE_TAC >> gvs[compile_copy_memory_entry]
QED

Finalise typed_copy_memory_entry

Theorem compile_store_memory_typed_entry:
  !cenv dst dt src st s. image_entry s /\ (!b. ~tail_alloc b s.cs_current_insts) ==>
  image_entry (SND (compile_store_memory_typed cenv dst dt src st s)) /\
  (!b. ~tail_alloc b (SND (compile_store_memory_typed cenv dst dt src st s)).cs_current_insts)
Proof
  metis_tac[typed_copy_memory_entry]
QED

Theorem compile_typed_copy_fields_entry:
  !cenv dst src dts sts doff soff s.
  image_entry s /\ (!b. ~tail_alloc b s.cs_current_insts) ==>
  image_entry (SND (compile_typed_copy_fields cenv dst src dts sts doff soff s)) /\
  (!b. ~tail_alloc b (SND (compile_typed_copy_fields cenv dst src dts sts doff soff s)).cs_current_insts)
Proof
  metis_tac[typed_copy_memory_entry]
QED

Theorem compile_copy_sarray_typed_entry:
  !cenv dst dt src st n s. image_entry s /\ (!b. ~tail_alloc b s.cs_current_insts) ==>
  image_entry (SND (compile_copy_sarray_typed cenv dst dt src st n s)) /\
  (!b. ~tail_alloc b (SND (compile_copy_sarray_typed cenv dst dt src st n s)).cs_current_insts)
Proof
  metis_tac[typed_copy_memory_entry]
QED

Theorem compile_copy_dynarray_typed_entry:
  !cenv dst dt cap src st s. image_entry s /\ (!b. ~tail_alloc b s.cs_current_insts) ==>
  image_entry (SND (compile_copy_dynarray_typed cenv dst dt cap src st s)) /\
  (!b. ~tail_alloc b (SND (compile_copy_dynarray_typed cenv dst dt cap src st s)).cs_current_insts)
Proof
  metis_tac[typed_copy_memory_entry]
QED

Theorem compile_struct_typed_copy_entry:
  !cenv dst src dfs sfs doff soff s.
  image_entry s /\ (!b. ~tail_alloc b s.cs_current_insts) ==>
  image_entry (SND (compile_struct_typed_copy cenv dst src dfs sfs doff soff s)) /\
  (!b. ~tail_alloc b (SND (compile_struct_typed_copy cenv dst src dfs sfs doff soff s)).cs_current_insts)
Proof
  metis_tac[typed_copy_memory_entry]
QED

Theorem compile_store_memory_entry:
  !cenv src dst dt st s. image_entry s /\ (!b. ~tail_alloc b s.cs_current_insts) ==>
  image_entry (SND (compile_store_memory cenv src dst dt st s)) /\
  (!b. ~tail_alloc b (SND (compile_store_memory cenv src dst dt st s)).cs_current_insts)
Proof
  rpt gen_tac >> strip_tac >> simp[compile_store_memory_def] >>
  rpt (IF_CASES_TAC >> simp[memory_entry_emit_void, compile_store_bytestring_entry,
    compile_store_memory_typed_entry, compile_copy_memory_entry])
QED
