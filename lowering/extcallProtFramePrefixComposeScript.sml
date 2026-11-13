(* Same-witness protected concrete request-prefix boundaries. *)
Theory extcallProtFramePrefixCompose
Ancestors
  extcallProtFrameTupleAllocate extcallProtFrameTuplePayload
  extcallProtFramePrefix exprExtRequestPrefix exprExtRequestPrefixOps
  exprExtRequestAllocationEndpoint exprExtRequestJointUnwrap
  exprExtRequestPayload exprExtRequestHistoryCompose extcallProtFramePath
  compileEnv emitHelperProps exprLoweringProps exprSimAlloc venomInst venomExecSemantics venomState
  valueEncoding valueEncodingProofs valueEncodingProps exprSafeOperand
  emitHelper exprExtRequestHistory exprExtRequestReconstruct loweringHalt
  fragExec fragGasMode finite_map list arithmetic loweringStateRelDefs valueEncodingDefs

Theorem extcall_protframe_alloc_selector_endpoint:
  compile_alloc_buffer sz sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand; Lit wd] sm = ((),sb) /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  stmt_state_rel ctx func cenv cx ee s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ 32 <= sz /\ sz < dimword (:256) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!pa pk. prot pa pk ==>
    pa + pk <= s.vs_alloca_next /\
    mem_bytes_at pa pk s.vs_memory = mem_bytes_at pa pk original /\
    !i b n. FLOOKUP s.vs_allocas i = SOME (b,n) ==>
      loweringStateRelDefs$regions_disjoint pa pk b n) ==>
  ?t w. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx ee t /\
    extrequest_history_frame cenv cx ee sa s ee sb t /\
    eval_operand buf.buf_operand t = SOME w /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    w2n w + sz < dimword (:256) /\
    mem_bytes_at (w2n w) 32 t.vs_memory = word_to_bytes wd T /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    local_ptrs_reserved cenv sb /\
    (!name b len. local_region cenv ee.scopes t name b len ==>
       regions_disjoint (w2n w) sz b len) /\
    (cenv.ce_is_ctor ==> !name tv v off.
       FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
       FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
         | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
       regions_disjoint (w2n w) sz off (type_memory_size tv)) /\
    (!pa pk. prot pa pk ==>
      pa + pk <= t.vs_alloca_next /\
      mem_bytes_at pa pk t.vs_memory = mem_bytes_at pa pk original /\
      !i b n. FLOOKUP t.vs_allocas i = SOME (b,n) ==>
        loweringStateRelDefs$regions_disjoint pa pk b n)
Proof
  strip_tac >> drule_all extrequest_allocation_endpoint >> strip_tac >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
        [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
    metis_tac[buffer_alloc_code] >>
  `lookup_var p u = SOME w` by gvs[eval_operand_def] >>
  `?t. gas_marked_path F ctx func u 0 (OK t) /\
    stmt_state_rel ctx func cenv cx ee t /\
    (t with <|vs_memory := u.vs_memory; vs_inst_idx := u.vs_inst_idx|>) = u /\
    t.vs_memory = (mstore (w2n w) wd u).vs_memory /\
    (!op. eval_operand op t = eval_operand op u) /\
    (!a k. regions_disjoint (w2n w) sz a k ==>
       mem_bytes_at a k t.vs_memory = mem_bytes_at a k u.vs_memory) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (irule extrequest_mstore_endpoint >> simp[] >>
     conj_tac >- metis_tac[] >> conj_tac
     >- (qexists_tac `mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
          [STRING #"%" (toString sa.cs_next_var)]` >> simp[mk_inst_def]) >>
     qexistsl_tac [`p`, `sm`] >> metis_tac[]) >>
  `t.vs_allocas = u.vs_allocas /\ t.vs_alloca_next = u.vs_alloca_next` by
    (qpat_assum `(t with <|vs_memory := _; vs_inst_idx := _|>) = u` mp_tac >>
     simp[venom_state_component_equality]) >>
  suspend "protection"
QED

Resume extcall_protframe_alloc_selector_endpoint[protection]:
  `!pa pk. prot pa pk ==>
    pa + pk <= u.vs_alloca_next /\
    !i b n. FLOOKUP u.vs_allocas i = SOME (b,n) ==>
      loweringStateRelDefs$regions_disjoint pa pk b n` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!pa pk. prot pa pk ==> _` drule >> strip_tac >>
     `window_alloca_growth s u` by
       (qpat_assum `gas_marked_path F ctx func s 0 (OK u)`
         (mp_then Any ACCEPT_TAC gas_marked_path_window_alloca_growth)) >>
     irule extcall_protframe_growth_geometry >> qexists_tac `s` >>
     asm_rewrite_tac[]) >>
  `!pa pk. prot pa pk ==>
     mem_bytes_at pa pk t.vs_memory = mem_bytes_at pa pk original` by
    (rpt gen_tac >> disch_tac >>
     `loweringStateRelDefs$regions_disjoint pa pk (w2n w) sz` by metis_tac[] >>
     `regions_disjoint (w2n w) sz pa pk` by
       (fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
     qpat_assum `!a k. regions_disjoint (w2n w) sz a k ==> _` drule >>
     qpat_assum `!pa pk. prot pa pk ==> _ /\ _ /\ _` drule >> simp[]) >>
  drule emitted_insts_emit_void >> strip_tac >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sm` >> simp[]) >>
  `!name b len. local_region cenv ee.scopes t name b len <=>
      local_region cenv ee.scopes u name b len` by
    (qpat_assum `(t with <|vs_memory := _; vs_inst_idx := _|>) = u` mp_tac >>
     simp[venom_state_component_equality] >> strip_tac >>
     simp[local_region_def, lookup_var_def]) >>
  `extrequest_history_frame cenv cx ee sa s ee sb t` by
    (`!x. lookup_var x t = lookup_var x u` by
       (rpt gen_tac >> qpat_assum `!op. _` (qspec_then `Var x` mp_tac) >>
        simp[eval_operand_def]) >>
     irule extrequest_copy_history >> simp[] >>
     qexistsl_tac [`sz`, `w2n w`, `sm`, `u`] >> simp[] >> metis_tac[]) >>
  `gas_marked_path F ctx func s 0 (OK t)` by
    (qpat_assum `gas_marked_path F ctx func s 0 (OK u)`
       (mp_then Any mp_tac gas_marked_path_then) >>
     disch_then (qspecl_then [`OK t`, `0`] mp_tac) >> simp[]) >>
  qexistsl_tac [`t`, `w`] >> simp[mem_bytes_at_mstore_same] >>
  metis_tac[]
QED

Finalise extcall_protframe_alloc_selector_endpoint

Theorem extcall_protframe_empty_payload_endpoint:
  compile_alloc_buffer sz sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand; Lit (n2w (ce.ce_method_id fname tys))]
    sm = ((),sn) /\
  emit_op ADD [buf.buf_operand;Lit 28w] sn = (offset,sb) /\
  fn_has_code sa sm func /\ fn_has_code sm sn func /\
  fn_has_code sn sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx ee s /\ expr_sim_inv ce cx env ee /\
  local_ptrs_reserved ce sa /\ 32 <= sz /\ sz < dimword (:256) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!pa pk. prot pa pk ==>
    pa + pk <= s.vs_alloca_next /\
    mem_bytes_at pa pk s.vs_memory = mem_bytes_at pa pk original /\
    !i b n. FLOOKUP s.vs_allocas i = SOME (b,n) ==>
      loweringStateRelDefs$regions_disjoint pa pk b n) ==>
  ?t (w:bytes32). gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func ce cx ee t /\
    extrequest_history_frame ce cx ee sa s ee sb t /\
    eval_operand offset t = SOME (n2w (w2n w+28)) /\
    read_memory (w2n w+28) 4 t =
      function_selector fname (vyper_to_abi_types (get_tenv cx) tys) /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    w2n w + sz < dimword (:256) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    local_ptrs_reserved ce sb /\ safe_operand sb offset /\
    eval_operand buf.buf_operand t = SOME w /\
    (!pa pk. prot pa pk ==>
      pa + pk <= t.vs_alloca_next /\
      mem_bytes_at pa pk t.vs_memory = mem_bytes_at pa pk original /\
      !i b n. FLOOKUP t.vs_allocas i = SOME (b,n) ==>
        loweringStateRelDefs$regions_disjoint pa pk b n)
Proof
  strip_tac >> drule_all extcall_protframe_alloc_selector_endpoint >> strip_tac >>
  rename1 `gas_marked_path F ctx func s 0 (OK u)` >>
  `read_memory (w2n w+28) 4 u =
    function_selector fname (vyper_to_abi_types (get_tenv cx) tys)` by
    (irule (SRULE [mem_bytes_at_def]
       (Q.INST [`payload` |-> `([]:byte list)`] extrequest_calldata_window)) >>
     metis_tac[mem_bytes_at_def]) >>
  `eval_operand buf.buf_operand u = SOME (n2w (w2n w))` by simp[] >>
  `eval_operand (Lit 4w) u = SOME (n2w 4) /\ safe_operand sn (Lit 4w)` by
    simp[eval_operand_def, safe_operand_def] >>
  `w2n w+28 < dimword (:256)` by decide_tac >>
  `4 < dimword (:256)` by simp[] >>
  drule_all extrequest_offset_endpoint >> strip_tac >>
  `extrequest_history_frame ce cx ee sa s ee sb t` by
    (drule_all extrequest_history_frame_trans >> simp[]) >>
  `gas_marked_path F ctx func s 0 (OK t)` by
    (qpat_assum `gas_marked_path F ctx func s 0 (OK u)`
       (mp_then Any mp_tac gas_marked_path_then) >>
     disch_then (qspecl_then [`OK t`, `0`] mp_tac) >> simp[]) >>
  `safe_operand sn buf.buf_operand` by
    (drule compile_alloc_buffer_parts >> strip_tac >>
     qpat_assum `emit_void MSTORE _ sm = ((),sn)`
       (mp_then Any mp_tac emitted_insts_emit_void) >> strip_tac >>
     simp[safe_operand_def] >> rpt strip_tac >>
     irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sm` >> simp[]) >>
  `eval_operand buf.buf_operand t = SOME w` by
    (drule_all extrequest_history_operand >> simp[]) >>
  qexistsl_tac [`t`, `w`] >> simp[] >> metis_tac[]
QED

Theorem extcall_protframe_empty_prefix_endpoint:
  extrequest_compile_prefix ce [] tys memsz abisz (ce.ce_method_id fname tys)
    retsz ei sa = ((bufop,offset,len),sp) /\
  fn_has_code sa sp func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx ee s /\ expr_sim_inv ce cx env ee /\
  local_ptrs_reserved ce sa /\ MAX abisz retsz + 32 < dimword (:256) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!pa pk. prot pa pk ==>
    pa + pk <= s.vs_alloca_next /\
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
    (!pa pk. prot pa pk ==>
      pa + pk <= t.vs_alloca_next /\
      mem_bytes_at pa pk t.vs_memory = mem_bytes_at pa pk original /\
      !i b n. FLOOKUP t.vs_allocas i = SOME (b,n) ==>
        loweringStateRelDefs$regions_disjoint pa pk b n)
Proof
  strip_tac >> drule extrequest_prefix_split >> simp[] >> strip_tac >> gvs[] >>
  `ci_mono sa sm` by
    (mp_tac (Q.SPECL [`MAX abisz retsz+32`, `sa`] ci_mono_compile_alloc_buffer) >> simp[]) >>
  `ci_mono sm sn` by
    (mp_tac (Q.SPECL [`MSTORE`, `[buf.buf_operand;Lit (n2w (ce.ce_method_id fname tys))]`,
       `sm`] ci_mono_emit_void) >> simp[]) >>
  `ci_mono sn sp` by
    (mp_tac (Q.SPECL [`ADD`, `[buf.buf_operand;Lit 28w]`, `sn`] ci_mono_emit_op) >> simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sn func /\ fn_has_code sn sp func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split, cs_extends_trans]) >>
  `32 <= MAX abisz retsz + 32` by decide_tac >>
  drule_all extcall_protframe_empty_payload_endpoint >> strip_tac >>
  `wb_frame ce ee ee sa s t` by metis_tac[extrequest_history_writeback] >>
  `safe_operand sp buf.buf_operand` by
    (drule compile_alloc_buffer_parts >> strip_tac >>
     simp[safe_operand_def] >> rpt strip_tac >>
     irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sm` >>
     fs[ci_mono_def] >> decide_tac) >>
  qexistsl_tac [`t`, `w`] >> simp[eval_operand_def, safe_operand_def] >>
  conj_tac >- (fs[arithmeticTheory.MAX_DEF] >> rw[] >> decide_tac) >>
  metis_tac[]
QED

(* The remaining operational hypothesis is precisely the joint tuple fold. *)
Theorem extcall_protframe_tuple_prefix_endpoint:
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
  disch_then (mk_asm "fold") >> strip_tac >>
  drule extrequest_prefix_split >> strip_tac >> gvs[] >>
  `ZIP (MAP (\(e,r,vv,ty,tv,v). vv) cells,
        MAP (\(e,r,vv,ty,tv,v). ty) cells) =
    MAP (\(e,r,vv,ty,tv,v). (vv,ty)) cells` by
    (simp[rich_listTheory.ZIP_MAP_MAP] >> irule MAP_CONG >> simp[] >>
     rpt strip_tac >> PairCases_on `x` >> simp[]) >>
  drule_all extrequest_tuple_prefix_code >> strip_tac >>
  `32 <= MAX abisz retsz + 32` by decide_tac >>
  drule_all extcall_protframe_alloc_selector_endpoint >> strip_tac >>
  rename1 `gas_marked_path F ctx func s 0 (OK q)` >>
  `EVERY (extrequest_tuple_cell ctx func ce cx ee sn q ee) cells` by
    (drule_all extrequest_tuple_cells_history >> simp[]) >>
  suspend "payload"
QED

Resume extcall_protframe_tuple_prefix_endpoint[payload]:
  markerLib.RESUME_TAC >>
  `safe_operand sn buf.buf_operand /\ sa.cs_next_id < sn.cs_next_id` by
    (qpat_assum `compile_alloc_buffer _ sa = (buf,sm)`
       (mp_then Any mp_tac compile_alloc_buffer_parts) >> strip_tac >>
     qpat_assum `emit_void MSTORE _ sm = ((),sn)`
       (mp_then Any mp_tac emitted_insts_emit_void) >> strip_tac >>
     simp[safe_operand_def] >> rpt strip_tac >>
     irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sm` >> fs[ci_mono_def]) >>
  `eval_operand buf.buf_operand q = SOME (n2w (w2n w))` by simp[] >>
  `32 + LENGTH (enc (vyper_to_abi_type (get_tenv cx)
      (TupleT (MAP (\(e,r,vv,ty,tv,v). ty) cells))) av) <= MAX abisz retsz+32` by
    fs[arithmeticTheory.MAX_DEF] >>
  qpat_x_assum `compile_extcall_store_values _ _ _ _ sq = ((),sr)` mp_tac >>
  asm_rewrite_tac[] >> disch_tac >>
  asm "fold" (mp_then Any mp_tac extcall_protframe_allocate_tuple_endpoint) >>
  disch_then (mk_asm "allocate") >>
  qpat_assum `EVERY (extrequest_tuple_cell ctx func ce cx ee sn q ee) cells`
    (mp_then Any (fn th =>
      qpat_assum `emit_op ADD [buf.buf_operand; Lit 32w] sr = (dst,st)`
        (mp_then Any (fn th =>
          qpat_assum `FLOOKUP q.vs_allocas sa.cs_next_id = SOME _`
            (mp_then Any (fn th =>
              qpat_assum `compile_alloc_buffer _ sn = (src,sq)`
                (mp_then Any (fn th =>
                  qpat_assum `compile_abi_encode_to_buf _ _ _ st = (out,en)`
                    (mp_then Any (fn th =>
                      qpat_assum `emit_op ADD [out; Lit 4w] en = (len,sl)`
                        (mp_then Any (fn th =>
                          qpat_assum `emit_op ADD [buf.buf_operand; Lit 28w] sl = (offset,sp)`
                            (mp_then Any mp_tac th)) th)) th)) th)) th)) th))
      (Q.INST [`prot` |-> `prot`, `original` |-> `original`,
               `fname` |-> `fname`, `env` |-> `env`, `ats` |-> `ats`]
        extcall_protframe_tuple_payload_endpoint)) >>
  disch_then (qspecl_then
    [`MAP (\(e,r,vv,ty,tv,v). v) cells`,
     `MAP (\(e,r,vv,ty,tv,v). ty) cells`,
     `MAP (\(e,r,vv,ty,tv,v). tv) cells`, `prot`, `original`] mp_tac) >>
  disch_then (qspecl_then [`fname`, `env`, `av`, `ats`] mp_tac) >>
  (impl_tac >-
    (conj_tac >-
      (rpt gen_tac >> strip_tac >> asm "allocate" irule >> simp[] >>
       rpt strip_tac >> metis_tac[]) >>
     simp[vyperABITheory.vyper_to_abi_def] >> rpt strip_tac >> metis_tac[])) >>
  strip_tac >>
  rename1 `gas_marked_path F ctx func q 0 (OK t)` >>
  suspend "finish"
QED

Resume extcall_protframe_tuple_prefix_endpoint[finish]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `allocate :- _` kall_tac >>
  qpat_x_assum `fold :- _` kall_tac >>
  `gas_marked_path F ctx func s 0 (OK t)` by
    (qpat_assum `gas_marked_path F ctx func s 0 (OK q)`
       (mp_then Any mp_tac gas_marked_path_then) >>
     disch_then (qspecl_then [`OK t`, `0`] mp_tac) >> simp[]) >>
  `!x z. not_fresh_at sa x /\ lookup_var x s = SOME z ==>
      lookup_var x t = SOME z` by
    (rpt strip_tac >>
     `lookup_var x q = SOME z` by
       (fs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >> metis_tac[]) >>
     `not_fresh_at sn x` by
       (fs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >>
        metis_tac[freshWritesTheory.not_fresh_at_mono]) >> metis_tac[]) >>
  `w2n w + retsz < dimword (:256)` by
    (fs[arithmeticTheory.MAX_DEF] >> rw[] >> decide_tac) >>
  suspend "history"
QED

Resume extcall_protframe_tuple_prefix_endpoint[history]:
  markerLib.RESUME_TAC >> (
  `sn.cs_next_var <= sp.cs_next_var /\ sn.cs_next_id <= sp.cs_next_id` by
    (fs[ci_mono_def] >> decide_tac) >>
  `safe_operand sp buf.buf_operand` by metis_tac[safe_operand_mono] >>
  `!aid p k. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (p,k) ==>
     loweringStateRelDefs$regions_disjoint (w2n w) (MAX abisz retsz+32) p k` by
    (rpt strip_tac >>
     `FLOOKUP q.vs_allocas aid = SOME (p,k)` by
       (fs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >> metis_tac[]) >>
     `allocas_non_overlapping q` by
       fs[stmt_state_rel_def, state_rel_def, venomMemDefsTheory.alloca_inv_def] >>
     fs[venomMemDefsTheory.allocas_non_overlapping_def, regions_disjoint_def] >>
     first_x_assum (qspecl_then [`sa.cs_next_id`, `aid`, `w2n w`,
       `MAX abisz retsz+32`, `p`, `k`] mp_tac) >> simp[]) >>
  `extrequest_history_frame ce cx ee sa s ee sp t` by
    (rewrite_tac[exprExtRequestHistoryTheory.extrequest_history_frame_def] >>
     rpt conj_tac
     >- simp[exprExtRequestReadProbeTheory.extrequest_read_frame_def]
     >- (fs[ci_mono_def] >> decide_tac)
     >- (fs[ci_mono_def] >> decide_tac)
     >- simp[]
     >- simp[]
     >- first_assum MATCH_ACCEPT_TAC
     >- (rpt strip_tac >>
         `FLOOKUP q.vs_allocas aid = SOME b` by
           (fs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >> metis_tac[]) >>
         metis_tac[])
     >- (rpt strip_tac >>
         `local_region ce ee.scopes q n b sz` by
           metis_tac[exprExtRequestHistoryTheory.extrequest_history_local_regions] >>
         fs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >> metis_tac[])
     >- (rpt strip_tac >>
         `aid < sn.cs_next_id /\ FLOOKUP q.vs_allocas aid = SOME (b,sz)` by
           (fs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >> metis_tac[]) >>
         `loweringStateRelDefs$regions_disjoint (w2n w) (MAX abisz retsz+32) b sz` by
           metis_tac[] >>
         `mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz q.vs_memory` by
           metis_tac[] >>
         fs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >> metis_tac[])
     >> (rpt strip_tac >>
         fs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >> metis_tac[])) >>
  `wb_frame ce ee ee sa s t` by metis_tac[extrequest_history_writeback] >>
  qexistsl_tac [`t`, `w`] >> simp[vyperABITheory.vyper_to_abi_def] >>
  fs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >>
  rpt strip_tac >> metis_tac[])
QED

Finalise extcall_protframe_tuple_prefix_endpoint
