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
