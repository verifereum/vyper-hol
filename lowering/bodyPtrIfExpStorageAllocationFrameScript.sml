Theory bodyPtrIfExpStorageAllocationFrame
Ancestors bodyPtrIfExpStorageInvariant bodyPtrIfExpAllocSource bodyPtrIfExpAllocFrame decoderGhostFramePtr
  slotCopyExecution loweringHalt exprLoweringProps venomMemProps valueEncodingProps compileEnv loweringStateRelDefs venomState finite_map words arithmetic

Theorem ifexp_alloca_data_frame:
  n < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
  u.vs_data_section = s.vs_data_section
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- (drule step_alloca_fresh >> disch_then (qspec_then `n` mp_tac) >>
      simp[] >> disch_then (qspec_then `out` assume_tac) >> gvs[update_var_def]) >>
  rename1 `SOME site` >> PairCases_on `site` >>
  drule reused_alloca_memory_effects >>
  disch_then (qspecl_then [`n`, `out`, `tn`] strip_assume_tac) >>
  gvs[update_var_def]
QED

Theorem ifexp_storage_allocation_frame:
  stmt_state_rel ctx fn ce cx ee s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce sb /\
  compile_alloc_buffer (32*n) sb = (buf,cs) /\ fn_has_code sb cs fn /\
  buf.buf_operand = Var out /\ 32*n < dimword (:256) /\
  step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w (32*n))] [out]) s = OK u /\
  ifexp_copy_ptr_inv ce cx rty es sa s0 G0 tn0 ee cs load src dst
    (u with vs_inst_idx := SUC s.vs_inst_idx) Gb tb p d n X i t H tt ==>
  (!x. not_fresh_at sb x ==> lookup_var x t = lookup_var x s) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP t.vs_allocas aid = SOME entry) /\
  (!b len. b+len <= w2n d \/ w2n d+32*n <= b ==>
    mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
  t.vs_accounts = s.vs_accounts /\ t.vs_call_ctx = s.vs_call_ctx /\
  t.vs_transient = s.vs_transient /\ t.vs_data_section = s.vs_data_section /\
  LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  strip_tac >> drule_all compile_alloc_buffer_raw_resources >> strip_tac >>
  drule_all alloca_step_contracts >> strip_tac >>
  drule_all ifexp_alloca_data_frame >> strip_tac >>
  drule_all ifexp_copy_ptr_ordinary_frame >> strip_tac >>
  `sb.cs_next_var <= cs.cs_next_var` by
    (drule compile_alloc_buffer_parts >> strip_tac >> decide_tac) >>
  `!x. not_fresh_at sb x ==> slot_copy_external cs (Var x)` by
    (rpt strip_tac >> irule ifexp_copy_not_fresh_external >>
     fs[not_fresh_at_def] >> first_x_assum drule >> decide_tac) >>
  qpat_x_assum `ifexp_copy_ptr_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    mp_tac >>
  simp[ifexp_copy_ptr_inv_def, slot_copy_inv_def] >> strip_tac >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!op. slot_copy_external cs op ==> _`
        (qspec_then `Var x` mp_tac) >> simp[eval_operand_def, lookup_var_def]) >>
  gvs[] >> metis_tac[]
QED

Theorem ifexp_storage_single_allocation_frame:
  stmt_state_rel ctx fn ce cx ee s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce sb /\
  compile_alloc_buffer 32 sb = (buf,cs) /\ fn_has_code sb cs fn /\
  buf.buf_operand = Var out /\
  step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit 32w] [out]) s = OK u /\
  (!x. not_fresh_at sb x ==> x <> tmp) /\
  t = (mstore (w2n d) w (update_var tmp w (u with vs_inst_idx := j))) with vs_inst_idx := k ==>
  (!x. not_fresh_at sb x ==> lookup_var x t = lookup_var x s) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP t.vs_allocas aid = SOME entry) /\
  (!b len. b+len <= w2n d \/ w2n d+32 <= b ==>
    mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
  t.vs_accounts = s.vs_accounts /\ t.vs_call_ctx = s.vs_call_ctx /\
  t.vs_transient = s.vs_transient /\ t.vs_data_section = s.vs_data_section /\
  LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  strip_tac >>
  `32 < dimword (:256)` by simp[dimword_def] >>
  drule_all (SRULE [] (Q.INST [`n` |-> `32`] compile_alloc_buffer_raw_resources)) >> strip_tac >>
  drule_all (SRULE [] (Q.INST [`n` |-> `32`] alloca_step_contracts)) >> strip_tac >>
  drule_all (SRULE [] (Q.INST [`n` |-> `32`] ifexp_alloca_data_frame)) >> strip_tac >>
  gvs[] >> conj_tac
  >- (rpt strip_tac >> simp[lookup_var_def, mstore_def, update_var_def, FLOOKUP_UPDATE] >>
      metis_tac[lookup_var_def]) >>
  simp[mstore_def, update_var_def] >> conj_tac
  >- (rpt strip_tac >>
      `mem_bytes_at b len (mstore (w2n d) w u).vs_memory = mem_bytes_at b len u.vs_memory` by
        (irule mstore_mem_bytes_at_disjoint >> simp[]) >>
      gvs[mstore_def]) >>
  mp_tac (Q.SPECL [`w2n d`, `w`, `s`] LENGTH_mstore_eq) >>
  simp[mstore_def]
QED

Theorem ifexp_single_copy_frame:
  (!x. not_fresh_at cs x ==> x <> tmp) /\
  t = (mstore b w (update_var tmp w (u with vs_inst_idx := j))) with vs_inst_idx := k ==>
  copy_static t = copy_static u /\
  (!x. not_fresh_at cs x ==> lookup_var x t = lookup_var x u) /\
  LENGTH u.vs_memory <= LENGTH t.vs_memory /\
  (!off len. off+len <= b \/ b+32 <= off ==>
    mem_bytes_at off len t.vs_memory = mem_bytes_at off len u.vs_memory)
Proof
  strip_tac >> gvs[] >>
  conj_tac
  >- simp[exprSimStorageCopyTheory.copy_static_def, mstore_def, update_var_def] >>
  conj_tac
  >- (rpt strip_tac >> simp[lookup_var_def, mstore_def, update_var_def, FLOOKUP_UPDATE] >>
      metis_tac[lookup_var_def]) >>
  conj_tac
  >- (mp_tac (Q.SPECL [`b`, `w`, `u`] LENGTH_mstore_eq) >> simp[mstore_def, update_var_def]) >>
  rpt strip_tac >>
  mp_tac (Q.SPECL [`off`, `len`, `b`, `w`, `u`] mstore_mem_bytes_at_disjoint) >>
  simp[mstore_def, update_var_def]
QED
