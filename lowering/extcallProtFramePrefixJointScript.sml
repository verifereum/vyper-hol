Theory extcallProtFramePrefixJoint
Ancestors
  extcallProtFramePrefixCompose extcallProtFrameTupleFold extcallProtFrameTupleCell
  extcallProtFrameJointUnwrap exprExtRequestTupleFold compileEnv loweringStateRelDefs valueEncodingDefs

Theorem extcall_protframe_tuple_fold_joint:
  !cells off sm sb s.
  EVERY (extrequest_tuple_cell ctx func ce cx eb cb tb ee) cells /\
  compile_extcall_store_values ce
    (MAP (\(e,r,vv,ty,tv,v). (vv,ty)) cells) buf off sm = ((),sb) /\
  stmt_state_rel ctx func ce cx eb tb /\ stmt_state_rel ctx func ce cx ee s /\
  extrequest_history_frame ce cx eb cb tb ee sm s /\ cb.cs_next_id <= live /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\ ee.gas_obs = [] /\
  safe_operand sm buf /\ eval_operand buf s = SOME w /\
  FLOOKUP s.vs_allocas live = SOME (tuple_base,capacity) /\ live < sm.cs_next_id /\
  tuple_base <= w2n w + off /\
  w2n w + off + SUM (MAP (\(e,r,vv,ty,tv,v). type_memory_size tv) cells) <=
    tuple_base + capacity /\ tuple_base + capacity < dimword (:256) /\
  (!name b len. local_region ce ee.scopes s name b len ==>
    regions_disjoint tuple_base capacity b len) /\
  (ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) tuple_base capacity) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!pa pk. prot pa pk ==> pa + pk <= s.vs_alloca_next /\
    mem_bytes_at pa pk s.vs_memory = mem_bytes_at pa pk original /\
    !i b n. FLOOKUP s.vs_allocas i = SOME (b,n) ==>
      loweringStateRelDefs$regions_disjoint pa pk b n) ==>
  ?q. gas_marked_path F ctx func s 0 (OK q) /\
    stmt_state_rel ctx func ce cx ee q /\
    tuple_in_memory (MAP (\(e,r,vv,ty,tv,v). v) cells)
      (MAP (\(e,r,vv,ty,tv,v). tv) cells) (w2n w + off) q.vs_memory /\
    extrequest_history_frame ce cx eb cb tb ee sb q /\
    FLOOKUP q.vs_allocas live = SOME (tuple_base,capacity) /\
    (!a k. tuple_base <= a /\ a + k <= tuple_base + capacity /\
      regions_disjoint a k (w2n w + off)
        (SUM (MAP (\(e,r,vv,ty,tv,v). type_memory_size tv) cells)) ==>
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x z. not_fresh_at sm x /\ lookup_var x s = SOME z ==>
      lookup_var x q = SOME z) /\
    (!aid p k. aid < sm.cs_next_id /\ aid <> live /\
      FLOOKUP s.vs_allocas aid = SOME (p,k) ==>
      mem_bytes_at p k q.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!pa pk. prot pa pk ==> pa + pk <= q.vs_alloca_next /\
      mem_bytes_at pa pk q.vs_memory = mem_bytes_at pa pk original /\
      !i b n. FLOOKUP q.vs_allocas i = SOME (b,n) ==>
        loweringStateRelDefs$regions_disjoint pa pk b n)
Proof
  mp_tac (Q.INST [`cenv` |-> `ce`, `sz` |-> `capacity`]
    extcall_tuple_store_fold_protected) >>
  (impl_tac >- (rpt gen_tac >> strip_tac >>
    irule extcall_tuple_cell_store_protected >> goal_assum (drule_at Any) >> simp[] >> metis_tac[])) >>
  simp[]
QED

Theorem extcall_protframe_prefix_empty_joint:
  extrequest_compile_prefix ce [] tys memsz abisz (ce.ce_method_id fname tys)
    retsz ei sa = ((bufop,offset,len),sp) /\
  fn_has_code sa sp func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx ee s /\ expr_sim_inv ce cx env ee /\
  local_ptrs_reserved ce sa /\ MAX abisz retsz + 32 < dimword (:256) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!pa pk. prot pa pk ==> pa + pk <= s.vs_alloca_next /\
    mem_bytes_at pa pk s.vs_memory = mem_bytes_at pa pk original /\
    !i b n. FLOOKUP s.vs_allocas i = SOME (b,n) ==>
      loweringStateRelDefs$regions_disjoint pa pk b n) ==>
  ?t (w:bytes32). gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func ce cx ee t /\
    extrequest_history_frame ce cx ee sa s ee sp t /\
    eval_operand offset t = SOME (n2w (w2n w+28)) /\
    eval_operand len t = SOME 4w /\
    read_memory (w2n w+28) 4 t =
      function_selector fname (vyper_to_abi_types (get_tenv cx) tys) /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,MAX abisz retsz+32) /\
    w2n w + retsz < dimword (:256) /\
    ~t.vs_halted /\ t.vs_current_bb = sp.cs_current_bb /\
    t.vs_inst_idx = LENGTH sp.cs_current_insts /\
    local_ptrs_reserved ce sp /\ safe_operand sp offset /\
    wb_frame ce ee ee sa s t /\ eval_operand bufop t = SOME w /\
    safe_operand sp bufop /\ safe_operand sp len /\
    (!pa pk. prot pa pk ==> pa + pk <= t.vs_alloca_next /\
      mem_bytes_at pa pk t.vs_memory = mem_bytes_at pa pk original /\
      !i b n. FLOOKUP t.vs_allocas i = SOME (b,n) ==>
        loweringStateRelDefs$regions_disjoint pa pk b n)
Proof
  MATCH_ACCEPT_TAC extcall_protframe_empty_prefix_endpoint
QED

Theorem extcall_protframe_prefix_tuple_joint:
  EVERY (extrequest_tuple_cell ctx func ce cx ee sa s ee) cells /\
  vals = MAP (\(e,r,vv,ty,tv,v). vv) cells /\ vals <> [] /\
  tys = MAP (\(e,r,vv,ty,tv,v). ty) cells /\
  tvs = MAP (\(e,r,vv,ty,tv,v). tv) cells /\
  vs = MAP (\(e,r,vv,ty,tv,v). v) cells /\
  sz = SUM (MAP (\(e,r,vv,ty,tv,v). type_memory_size tv) cells) /\
  assignable_type (get_tenv cx) (TupleT tys) /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) /\
  type_memory_size (TupleTV tvs) <= sz /\
  vyper_to_abi (get_tenv cx) (TupleT tys) (ArrayV (TupleV vs)) = SOME av /\
  ei = type_to_abi_enc_info ce.ce_struct_fields ce (TupleT tys) /\
  extrequest_compile_prefix ce vals tys sz abisz (ce.ce_method_id fname ats)
    retsz ei sa = ((bufop,offset,len),sp) /\
  32 + LENGTH (enc (vyper_to_abi_type (get_tenv cx) (TupleT tys)) av) <=
    MAX abisz retsz + 32 /\
  fn_has_code sa sp func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx ee s /\ expr_sim_inv ce cx env ee /\
  local_ptrs_reserved ce sa /\ ee.gas_obs = [] /\
  sz < dimword (:256) /\ MAX abisz retsz + 32 < dimword (:256) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!pa pk. prot pa pk ==> pa + pk <= s.vs_alloca_next /\
    mem_bytes_at pa pk s.vs_memory = mem_bytes_at pa pk original /\
    !i b n. FLOOKUP s.vs_allocas i = SOME (b,n) ==>
      loweringStateRelDefs$regions_disjoint pa pk b n) ==>
  ?t (w:bytes32). gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func ce cx ee t /\
    ~t.vs_halted /\ t.vs_current_bb = sp.cs_current_bb /\
    t.vs_inst_idx = LENGTH sp.cs_current_insts /\
    eval_operand len t = SOME
      (n2w (4+LENGTH (enc (vyper_to_abi_type (get_tenv cx) (TupleT tys)) av))) /\
    eval_operand offset t = SOME (n2w (w2n w+28)) /\
    read_memory (w2n w+28)
      (4+LENGTH (enc (vyper_to_abi_type (get_tenv cx) (TupleT tys)) av)) t =
      function_selector fname (vyper_to_abi_types (get_tenv cx) ats) ++
        enc (vyper_to_abi_type (get_tenv cx) (TupleT tys)) av /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,MAX abisz retsz+32) /\
    w2n w + retsz < dimword (:256) /\
    local_ptrs_reserved ce sp /\ safe_operand sp len /\ safe_operand sp offset /\
    eval_operand bufop t = SOME w /\
    (!x z. not_fresh_at sa x /\ lookup_var x s = SOME z ==>
       lookup_var x t = SOME z) /\
    (!name p k. local_region ce ee.scopes s name p k ==>
       mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (ce.ce_is_ctor ==> !name tv v p.
       FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc p) /\
       FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
         | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
       mem_bytes_at p (type_memory_size tv) t.vs_memory =
         mem_bytes_at p (type_memory_size tv) s.vs_memory) /\
    (!aid p k. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (p,k) ==>
       FLOOKUP t.vs_allocas aid = SOME (p,k)) /\
    extrequest_history_frame ce cx ee sa s ee sp t /\
    wb_frame ce ee ee sa s t /\ safe_operand sp bufop /\
    (!pa pk. prot pa pk ==> pa + pk <= t.vs_alloca_next /\
      mem_bytes_at pa pk t.vs_memory = mem_bytes_at pa pk original /\
      !i b n. FLOOKUP t.vs_allocas i = SOME (b,n) ==>
        loweringStateRelDefs$regions_disjoint pa pk b n)
Proof
  mp_tac extcall_protframe_tuple_prefix_endpoint >>
  (impl_tac >- (rpt gen_tac >> strip_tac >>
    irule extcall_protframe_tuple_fold_joint >> goal_assum (drule_at Any) >> simp[] >> metis_tac[])) >>
  simp[]
QED
