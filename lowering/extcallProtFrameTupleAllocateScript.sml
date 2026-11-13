(* Allocation/fill composition, independent of the operational fold proof. *)
Theory extcallProtFrameTupleAllocate
Ancestors
  exprExtRequestPayload exprExtRequestTupleFold exprExtRequestAllocationEndpoint
  exprExtRequestHistory extcallProtFramePrefix extcallProtFramePath
  exprLoweringProps exprLowering compileEnv vyperInterpreter vyperState
  valueEncodingProps valueTypingMemoryProps gasSummary fragGasMode fragExec
  loweringHalt loweringStateRelDefs valueEncodingDefs

Theorem extcall_protframe_allocate_tuple_endpoint:
  (!cells off sm sb t eb cb tb buf w live tuple_base capacity.
    EVERY (extrequest_tuple_cell ctx func ce cx eb cb tb ee) cells /\
    compile_extcall_store_values ce
      (MAP (\(e,r,vv,ty,tv,v). (vv,ty)) cells) buf off sm = ((),sb) /\
    stmt_state_rel ctx func ce cx eb tb /\ stmt_state_rel ctx func ce cx ee t /\
    extrequest_history_frame ce cx eb cb tb ee sm t /\ cb.cs_next_id <= live /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\ ee.gas_obs = [] /\
    safe_operand sm buf /\ eval_operand buf t = SOME w /\
    FLOOKUP t.vs_allocas live = SOME (tuple_base,capacity) /\ live < sm.cs_next_id /\
    tuple_base <= w2n w + off /\
    w2n w + off + SUM (MAP (\(e,r,vv,ty,tv,v). type_memory_size tv) cells) <=
      tuple_base + capacity /\ tuple_base + capacity < dimword (:256) /\
    (!name b len. local_region ce ee.scopes t name b len ==>
      regions_disjoint tuple_base capacity b len) /\
    (ce.ce_is_ctor ==> !name itv iv io.
      FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
      FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
      regions_disjoint io (type_memory_size itv) tuple_base capacity) /\
    ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    (!pa pk. prot pa pk ==> pa + pk <= t.vs_alloca_next /\
      mem_bytes_at pa pk t.vs_memory = mem_bytes_at pa pk original /\
      !i b n. FLOOKUP t.vs_allocas i = SOME (b,n) ==>
        loweringStateRelDefs$regions_disjoint pa pk b n) ==>
    ?q. gas_marked_path F ctx func t 0 (OK q) /\
      stmt_state_rel ctx func ce cx ee q /\
      tuple_in_memory (MAP (\(e,r,vv,ty,tv,v). v) cells)
        (MAP (\(e,r,vv,ty,tv,v). tv) cells) (w2n w + off) q.vs_memory /\
      extrequest_history_frame ce cx eb cb tb ee sb q /\
      FLOOKUP q.vs_allocas live = SOME (tuple_base,capacity) /\
      (!a k. tuple_base <= a /\ a + k <= tuple_base + capacity /\
        regions_disjoint a k (w2n w + off)
          (SUM (MAP (\(e,r,vv,ty,tv,v). type_memory_size tv) cells)) ==>
        mem_bytes_at a k q.vs_memory = mem_bytes_at a k t.vs_memory) /\
      ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
      q.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (!x z. not_fresh_at sm x /\ lookup_var x t = SOME z ==>
        lookup_var x q = SOME z) /\
      (!aid p k. aid < sm.cs_next_id /\ aid <> live /\
        FLOOKUP t.vs_allocas aid = SOME (p,k) ==>
        mem_bytes_at p k q.vs_memory = mem_bytes_at p k t.vs_memory) /\
      (!pa pk. prot pa pk ==> pa + pk <= q.vs_alloca_next /\
        mem_bytes_at pa pk q.vs_memory = mem_bytes_at pa pk original /\
        !i b n. FLOOKUP q.vs_allocas i = SOME (b,n) ==>
          loweringStateRelDefs$regions_disjoint pa pk b n)) ==>
  EVERY (extrequest_tuple_cell ctx func ce cx ee sa s ee) cells /\
  sz = SUM (MAP (\(e,r,vv,ty,tv,v). type_memory_size tv) cells) /\
  compile_alloc_buffer sz sa = (buf,sm) /\
  compile_extcall_store_values ce
    (MAP (\(e,r,vv,ty,tv,v). (vv,ty)) cells) buf.buf_operand 0 sm = ((),sb) /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx ee s /\ local_ptrs_reserved ce sa /\
  ee.gas_obs = [] /\ sz < dimword (:256) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!pa pk. prot pa pk ==> pa + pk <= s.vs_alloca_next /\
    mem_bytes_at pa pk s.vs_memory = mem_bytes_at pa pk original /\
    !i b n. FLOOKUP s.vs_allocas i = SOME (b,n) ==>
      loweringStateRelDefs$regions_disjoint pa pk b n) ==>
  ?q w. gas_marked_path F ctx func s 0 (OK q) /\
    stmt_state_rel ctx func ce cx ee q /\
    extrequest_history_frame ce cx ee sa s ee sb q /\
    eval_operand buf.buf_operand q = SOME w /\
    tuple_in_memory (MAP (\(e,r,vv,ty,tv,v). v) cells)
      (MAP (\(e,r,vv,ty,tv,v). tv) cells) (w2n w) q.vs_memory /\
    FLOOKUP q.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    w2n w + sz < dimword (:256) /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\ local_ptrs_reserved ce sb /\
    (!aid p k. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (p,k) ==>
      mem_bytes_at p k q.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!pa pk. prot pa pk ==> pa + pk <= q.vs_alloca_next /\
      mem_bytes_at pa pk q.vs_memory = mem_bytes_at pa pk original /\
      !i b n. FLOOKUP q.vs_allocas i = SOME (b,n) ==>
        loweringStateRelDefs$regions_disjoint pa pk b n)
Proof
  disch_then (mk_asm "fold") >> strip_tac >>
  drule_all extrequest_allocation_endpoint >> strip_tac >>
  `!pa pk. prot pa pk ==> pa + pk <= u.vs_alloca_next /\
    mem_bytes_at pa pk u.vs_memory = mem_bytes_at pa pk original /\
    !i b n. FLOOKUP u.vs_allocas i = SOME (b,n) ==>
      loweringStateRelDefs$regions_disjoint pa pk b n` by
    (rpt gen_tac >> disch_tac >>
     `window_alloca_growth s u` by metis_tac[gas_marked_path_window_alloca_growth] >>
     `!i r. FLOOKUP s.vs_allocas i = SOME r ==> FLOOKUP u.vs_allocas i = SOME r` by
       metis_tac[gas_marked_path_allocas_preserved] >>
     `pa + pk <= u.vs_alloca_next /\
      !i b n. FLOOKUP u.vs_allocas i = SOME (b,n) ==>
        loweringStateRelDefs$regions_disjoint pa pk b n` by
       (irule extcall_protframe_growth_geometry >> qexists_tac `s` >>
        asm_rewrite_tac[] >> metis_tac[]) >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  suspend "fill"
QED

Resume extcall_protframe_allocate_tuple_endpoint[fill]:
  `safe_operand sm buf.buf_operand` by
    (gvs[exprSafeOperandTheory.safe_operand_def] >> metis_tac[]) >>
  `sa.cs_next_id < sm.cs_next_id` by
    (drule compile_alloc_buffer_parts >> simp[]) >>
  `!name tv v off.
    ce.ce_is_ctor /\
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    regions_disjoint off (type_memory_size tv) (w2n w) sz` by
    (rpt strip_tac >> qpat_x_assum `ce.ce_is_ctor ==> _` drule >>
     disch_then drule >> simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    regions_disjoint off (type_memory_size tv) (w2n w) sz` by metis_tac[] >>
  asm "fold" (drule_at (Pat `EVERY _ _`)) >>
  disch_then (drule_at (Pat `compile_extcall_store_values _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `extrequest_history_frame _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME (_,_)`)) >>
  simp[] >> disch_then (qspec_then `sa.cs_next_id` mp_tac) >>
  simp[] >> (impl_tac >- (gvs[] >> metis_tac[])) >> strip_tac >>
  `eval_operand buf.buf_operand q = SOME w` by
    (simp[venomStateTheory.eval_operand_def] >> first_x_assum irule >> gvs[venomStateTheory.eval_operand_def]) >>
  `gas_marked_path F ctx func s 0 (OK q)` by
    (drule_all gas_marked_path_then >> simp[]) >>
  `!aid p k. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (p,k) ==>
     mem_bytes_at p k q.vs_memory = mem_bytes_at p k s.vs_memory` by
    (map_every qx_gen_tac [`aid`, `old_base`, `old_size`] >> strip_tac >>
     `aid < sm.cs_next_id /\ aid <> sa.cs_next_id` by decide_tac >>
     `FLOOKUP u.vs_allocas aid = SOME (old_base,old_size)` by metis_tac[] >>
     metis_tac[]) >>
  qexistsl_tac [`q`, `w`] >> simp[] >>
  gvs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >> metis_tac[]
QED

Finalise extcall_protframe_allocate_tuple_endpoint
