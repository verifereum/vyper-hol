Theory bodyPtrIfExpStorageSingle
Ancestors bodyPtrIfExpMaterializeSingle bodyPtrIfExpStorageSupplier
  bodyPtrIfExpStorageAllocation bodyPtrIfExpStorageSource pred_set
  context compileEnv emitHelper fragExec loweringHalt

(* One-slot representations need not be word types.  Use source decoding
   and translated taint, exactly as for the nonsingleton loop. *)
Theorem ifexp_storage_single_robust:
  type_slot_size ty = 1 /\ well_formed_type_value ty /\
  slots_in_range st (w2n p) ty /\ decode_value st (w2n p) ty = SOME v /\
  storage_range_agree st rt p ty /\
  u = mstore b (lookup_storage p rt) s /\
  dest_taint = (old_taint DIFF {i | b <= i /\ i < b+32}) UNION
    {b+i | i IN key_taint source_taint p} /\
  (!k j. w2n p <= w2n k /\ w2n k < w2n p+type_slot_size ty /\
    j < 32 /\ (k,j) IN source_taint ==> dead_bytes rt (w2n p) ty (w2n k) j) ==>
  !m. mem_agree_outside dest_taint u.vs_memory m ==> val_in_memory ty v b m
Proof
  rpt strip_tac >> irule ifexp_range_storage_decode_robust >>
  conj_tac >- simp[] >>
  qexistsl_tac [`dest_taint`, `u.vs_memory`, `rt`, `source_taint`, `st`, `p`] >>
  simp[valueEncodingPropsTheory.mstore_mem_word_at_same,
       ptrDisciplineTheory.key_taint_def] >>
  simp[wordsTheory.WORD_ADD_0] >> metis_tac[]
QED

Theorem ifexp_storage_single_code:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_ensure_in_memory src loc bytes 1 ctor imm sb = (dst,sd) /\
  fn_has_code sb sd fn ==>
  ?buf cs.
    compile_alloc_buffer bytes sb = (buf,cs) /\ dst = buf.buf_operand /\
    (do loaded <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
        emit_void MSTORE [buf.buf_operand;loaded] od) cs = ((),sd) /\
    fn_has_code sb cs fn /\ fn_has_code cs sd fn /\
    sb.cs_next_var <= cs.cs_next_var /\ sb.cs_next_id <= cs.cs_next_id
Proof
  strip_tac >>
  drule_at (Pat `compile_ensure_in_memory _ _ _ _ _ _ _ = _`) ifexp_ensure_single_stages >>
  simp[] >> strip_tac >>
  rename1 `compile_alloc_buffer bytes sb = (buf,cs)` >>
  `cs_extends cs sd` by
    (gvs[compileEnvTheory.cs_extends_def,
      emit_op_def, emit_void_def,
      comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_var_def,
      fresh_id_def, emit_def] >> simp[rich_listTheory.IS_PREFIX_APPEND]) >>
  drule compile_alloc_buffer_extends >> strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  qexistsl_tac [`buf`, `cs`] >> simp[]
QED
