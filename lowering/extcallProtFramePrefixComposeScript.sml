(* Same-witness protected concrete request-prefix boundaries. *)
Theory extcallProtFramePrefixCompose
Ancestors
  extcallProtFramePrefix exprExtRequestPrefix exprExtRequestPrefixOps
  exprExtRequestAllocationEndpoint exprExtRequestJointUnwrap
  exprExtRequestPayload exprExtRequestHistoryCompose extcallProtFramePath
  compileEnv emitHelperProps exprLoweringProps exprSimAlloc venomInst venomExecSemantics venomState
  valueEncoding valueEncodingProofs valueEncodingProps exprSafeOperand
  emitHelper exprExtRequestHistory exprExtRequestReconstruct loweringHalt
  fragExec fragGasMode finite_map list arithmetic

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
      compileEnv$regions_disjoint pa pk b n) ==>
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
        compileEnv$regions_disjoint pa pk b n)
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
      compileEnv$regions_disjoint pa pk b n` by
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
     `compileEnv$regions_disjoint pa pk (w2n w) sz` by metis_tac[] >>
     `regions_disjoint (w2n w) sz pa pk` by
       (fs[compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
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
      compileEnv$regions_disjoint pa pk b n) ==>
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
        compileEnv$regions_disjoint pa pk b n)
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
      compileEnv$regions_disjoint pa pk b n) ==>
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
    wb_frame ce ee sa s t /\ eval_operand bufop t = SOME w /\
    safe_operand sp bufop /\ safe_operand sp len /\
    (!pa pk. prot pa pk ==>
      pa + pk <= t.vs_alloca_next /\
      mem_bytes_at pa pk t.vs_memory = mem_bytes_at pa pk original /\
      !i b n. FLOOKUP t.vs_allocas i = SOME (b,n) ==>
        compileEnv$regions_disjoint pa pk b n)
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
  `wb_frame ce ee sa s t` by metis_tac[extrequest_history_writeback] >>
  `safe_operand sp buf.buf_operand` by
    (drule compile_alloc_buffer_parts >> strip_tac >>
     simp[safe_operand_def] >> rpt strip_tac >>
     irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sm` >>
     fs[ci_mono_def] >> decide_tac) >>
  qexistsl_tac [`t`, `w`] >> simp[eval_operand_def, safe_operand_def] >>
  conj_tac >- (fs[arithmeticTheory.MAX_DEF] >> rw[] >> decide_tac) >>
  metis_tac[]
QED
