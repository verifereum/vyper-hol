Theory bodyIntCallJointWrite
Ancestors
  list finite_map exprSimAlloc exprSimHash exprLoweringProps compileEnv vyperState
  venomState venomExecSemantics exprSimProps context venomInst words valueCopy

(* All windows are framed at the same concrete bounded-write endpoint. *)
Theorem joint_alloca_write_frame:
  stmt_state_rel ctx func ce cx es s /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  b <= a /\ a + 32 <= b + sz /\
  (!name lb len. local_region ce es.scopes s name lb len ==>
     regions_disjoint b sz lb len) /\
  EVERY (\(off,len). regions_disjoint b sz off len) hs ==>
  stmt_state_rel ctx func ce cx es (mstore a w s) /\
  EVERY (\(off,len).
    mem_bytes_at off len (mstore a w s).vs_memory =
    mem_bytes_at off len s.vs_memory) hs /\
  (ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
      NONE => FEMPTY | SOME imms => get_source_immutables ce.ce_module imms)
      name = SOME (tv,v) ==>
    mem_bytes_at off (type_memory_size tv) (mstore a w s).vs_memory =
    mem_bytes_at off (type_memory_size tv) s.vs_memory)
Proof
  strip_tac >> conj_tac
  >- (irule literal_mstore_state_rel >> simp[] >>
      qexistsl_tac [`b`, `inst`, `sz`] >>
      gvs[regions_disjoint_def] >> metis_tac[]) >>
  conj_tac
  >- (gvs[EVERY_MEM] >> rpt strip_tac >>
      PairCases_on `e` >> gvs[] >>
      irule mstore_region_frame >>
      qexistsl_tac [`b`, `sz`] >> simp[] >>
      first_x_assum drule >> simp[]) >>
  rpt strip_tac >>
  irule mstore_region_frame >> qexistsl_tac [`b`, `sz`] >>
  simp[] >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
  simp[stmt_state_rel_def, immutable_alloca_sep_def] >>
  rpt strip_tac >>
  first_x_assum drule_all >>
  simp[regions_disjoint_def] >> metis_tac[]
QED

(* Uses the actual allocation endpoint, including reused allocation entries. *)
Theorem joint_alloc_buffer_write:
  compile_alloc_buffer sz sa = (buf,sm) /\ fn_has_code sa sm func /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ sz < dimword (:256) /\ k + 32 <= sz /\
  EVERY (\(off,len).
    (?aid p n. aid < sa.cs_next_id /\
      FLOOKUP s.vs_allocas aid = SOME (p,n) /\
      p <= off /\ off + len <= p+n) \/
    (?name p n. local_region ce es.scopes s name p n /\
      p <= off /\ off + len <= p+n)) hs ==>
  ?t wbuf.
    run_inst_seq (emitted_insts sa sm) s = OK t /\
    eval_operand buf.buf_operand t = SOME wbuf /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n wbuf,sz) /\
    w2n wbuf + sz < dimword (:256) /\
    stmt_state_rel ctx func ce cx es (mstore (w2n wbuf+k) w t) /\
    EVERY (\(off,len).
      mem_bytes_at off len (mstore (w2n wbuf+k) w t).vs_memory =
      mem_bytes_at off len s.vs_memory) hs /\
    (ce.ce_is_ctor ==> !name tv v off.
      FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
        NONE => FEMPTY | SOME imms => get_source_immutables ce.ce_module imms)
        name = SOME (tv,v) ==>
      mem_bytes_at off (type_memory_size tv)
        (mstore (w2n wbuf+k) w t).vs_memory =
      mem_bytes_at off (type_memory_size tv) s.vs_memory)
Proof
  strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  `!name p n. local_region ce es.scopes s name p n ==>
      local_region ce es.scopes t name p n` by
    (rpt strip_tac >> irule local_region_frame_fwd >>
     qexistsl_tac [`s`, `sa`, `es.scopes`] >> simp[]) >>
  `EVERY (\(off,len). regions_disjoint (w2n w') sz off len) hs` by
    (gvs[EVERY_MEM] >> rpt strip_tac >>
     PairCases_on `e` >>
     qpat_x_assum `!e. MEM e hs ==> _` drule >> simp[] >>
     strip_tac
     >- (qpat_x_assum `!aid b len. _ ==> regions_disjoint _ _ _ _`
           drule_all >> simp[regions_disjoint_def] >> decide_tac) >>
     qpat_x_assum `!name p n. local_region _ _ s _ _ _ ==> _`
       drule >> strip_tac >>
     qpat_x_assum `!name b len. local_region _ _ t _ _ _ ==> _`
       drule >> simp[regions_disjoint_def] >> decide_tac) >>
  qexistsl_tac [`t`, `w'`] >> simp[] >>
  qpat_x_assum `t.vs_memory = s.vs_memory`
    (fn th => rewrite_tac[GSYM th]) >>
  irule joint_alloca_write_frame >> simp[] >>
  qexistsl_tac [`w2n w'`,
    `mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString sa.cs_next_var)]`, `sz`] >>
  simp[mk_inst_def] >> metis_tac[]
QED

Theorem joint_compile_store_word_run:
  compile_store_memory ce src dst dst_ty src_ty sa = ((),sb) /\
  is_word_type dst_ty /\
  eval_operand dst s = SOME d /\ eval_operand src s = SOME w /\
  stmt_state_rel ctx func ce cx es s /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  b <= w2n d /\ w2n d + 32 <= b + sz /\
  (!name lb len. local_region ce es.scopes s name lb len ==>
     regions_disjoint b sz lb len) /\
  EVERY (\(off,len). regions_disjoint b sz off len) hs ==>
  run_inst_seq (emitted_insts sa sb) s = OK (mstore (w2n d) w s) /\
  same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
  sa.cs_next_id <= sb.cs_next_id /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  stmt_state_rel ctx func ce cx es (mstore (w2n d) w s) /\
  EVERY (\(off,len).
    mem_bytes_at off len (mstore (w2n d) w s).vs_memory =
    mem_bytes_at off len s.vs_memory) hs /\
  (ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
      NONE => FEMPTY | SOME imms => get_source_immutables ce.ce_module imms)
      name = SOME (tv,v) ==>
    mem_bytes_at off (type_memory_size tv) (mstore (w2n d) w s).vs_memory =
    mem_bytes_at off (type_memory_size tv) s.vs_memory)
Proof
  strip_tac >>
  qpat_x_assum `compile_store_memory _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_store_memory_def] >> strip_tac >>
  drule_all emit_mstore_run >> strip_tac >> simp[] >>
  irule joint_alloca_write_frame >> simp[] >>
  qexistsl_tac [`b`, `inst`, `sz`] >> simp[] >> metis_tac[]
QED
