(* Prefix composition consumes the store interface, not its implementation. *)
Theory exprExtRequestSnapshotStorePrefix
Ancestors
  exprExtRequestSnapshotStoreInterface exprExtRequestPrefix
  exprExtRequestPayload exprExtRequestAllocationEndpoint exprExtRequestHistoryCompose
  exprLoweringProps emitHelperProps compileEnv loweringStateRelDefs
  exprSafeOperand fragGasMode venomExecSemantics venomState list
  loweringHalt exprExtRequestTupleFold exprExtRequestPrefixOps
  exprExtRequestTupleWindow exprExtRequestReconstruct

Theorem extrequest_snapshot_allocate_tuple[local]:
  extrequest_snapshot_store_contract ctx func ce cx /\
  EVERY (extrequest_snapshot_cell ctx func ce cx ee sa s) cells /\
  sz = SUM (MAP (\(vv,ty,tv,v). type_memory_size tv) cells) /\
  compile_alloc_buffer sz sa = (buf,sm) /\
  compile_extcall_store_values ce
    (MAP (\(vv,ty,tv,v). (vv,ty)) cells) buf.buf_operand 0 sm = ((),sb) /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx ee s /\ local_ptrs_reserved ce sa /\
  ee.gas_obs = [] /\ sz < dimword (:256) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?q w. gas_marked_path F ctx func s 0 (OK q) /\
    stmt_state_rel ctx func ce cx ee q /\
    extrequest_history_frame ce cx ee sa s ee sb q /\
    eval_operand buf.buf_operand q = SOME w /\
    tuple_in_memory (MAP (\(vv,ty,tv,v). v) cells)
      (MAP (\(vv,ty,tv,v). tv) cells) (w2n w) q.vs_memory /\
    FLOOKUP q.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    w2n w + sz < dimword (:256) /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\ local_ptrs_reserved ce sb /\
    (!aid p k. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (p,k) ==>
       mem_bytes_at p k q.vs_memory = mem_bytes_at p k s.vs_memory)
Proof
  strip_tac >> drule_all extrequest_allocation_endpoint >> strip_tac >>
  `safe_operand sm buf.buf_operand` by
    (gvs[safe_operand_def] >> metis_tac[]) >>
  `sa.cs_next_id < sm.cs_next_id` by
    (drule compile_alloc_buffer_parts >> simp[]) >>
  `ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    regions_disjoint off (type_memory_size tv) (w2n w) sz` by
    (rpt strip_tac >> qpat_x_assum `ce.ce_is_ctor ==> _` drule >>
     disch_then drule >> simp[regions_disjoint_def] >> decide_tac) >>
  qpat_x_assum `extrequest_snapshot_store_contract _ _ _ _` mp_tac >>
  simp[extrequest_snapshot_store_contract_def] >>
  disch_then (drule_at (Pat `EVERY _ _`)) >>
  disch_then (drule_at (Pat `compile_extcall_store_values _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `extrequest_history_frame _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME (_,_)`)) >>
  simp[] >> disch_then (qspec_then `sa.cs_next_id` mp_tac) >>
  simp[] >> (impl_tac >- gvs[]) >> strip_tac >>
  `eval_operand buf.buf_operand q = SOME w` by
    (simp[eval_operand_def] >> first_x_assum irule >> gvs[eval_operand_def]) >>
  `gas_marked_path F ctx func s 0 (OK q)` by
    (drule_all gas_marked_path_then >> simp[]) >>
  `local_ptrs_reserved ce sb` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     fs[exprExtRequestHistoryTheory.extrequest_history_frame_def]) >>
  `!aid p k. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (p,k) ==>
     mem_bytes_at p k q.vs_memory = mem_bytes_at p k s.vs_memory` by
    (map_every qx_gen_tac [`aid`, `old_base`, `old_size`] >> strip_tac >>
     `aid < sm.cs_next_id /\ aid <> sa.cs_next_id` by decide_tac >>
     `FLOOKUP u.vs_allocas aid = SOME (old_base,old_size)` by metis_tac[] >>
     metis_tac[]) >>
  qexistsl_tac [`q`, `w`] >> gvs[] >> metis_tac[]
QED

(* Independent of the representation used to fill the registered source tuple. *)
Theorem extrequest_poststore_payload_endpoint[local]:
  assignable_type (get_tenv cx) (TupleT tys) /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) /\
  type_memory_size (TupleTV tvs) <= sz /\
  vyper_to_abi (get_tenv cx) (TupleT tys) (ArrayV (TupleV vs)) = SOME av /\
  ei = type_to_abi_enc_info ce.ce_struct_fields ce (TupleT tys) /\
  tuple_in_memory vs tvs source_base s.vs_memory /\
  FLOOKUP s.vs_allocas source_id = SOME (source_base,sz) /\
  source_id < sn.cs_next_id /\ source_id <> live /\
  eval_operand srcop s = SOME (n2w source_base) /\ safe_operand sn srcop /\
  emit_op ADD [buf;Lit 32w] sn = (dst,st) /\
  compile_abi_encode_to_buf dst srcop ei st = (out,en) /\
  emit_op ADD [out;Lit 4w] en = (len,sl) /\
  emit_op ADD [buf;Lit 28w] sl = (offset,sp) /\
  fn_has_code en sl func /\ fn_has_code sl sp func /\
  fn_has_code sn st func /\ fn_has_code st en func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx ee s /\ expr_sim_inv ce cx env ee /\
  local_ptrs_reserved ce sn /\ ee.gas_obs = [] /\ sz < dimword (:256) /\
  live < sn.cs_next_id /\ FLOOKUP s.vs_allocas live = SOME (b,cap) /\
  b + cap < dimword (:256) /\
  32 + LENGTH (enc (vyper_to_abi_type (get_tenv cx) (TupleT tys)) av) <= cap /\
  eval_operand buf s = SOME (n2w b) /\ safe_operand sn buf /\
  mem_bytes_at b 32 s.vs_memory =
    word_to_bytes (n2w (ce.ce_method_id fname ats):bytes32) T /\
  (!name p k. local_region ce ee.scopes s name p k ==>
    loweringStateRelDefs$regions_disjoint b cap p k) /\
  (ce.ce_is_ctor ==> !name tv v p.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc p) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    loweringStateRelDefs$regions_disjoint b cap p (type_memory_size tv)) /\
  ~s.vs_halted /\ s.vs_current_bb = sn.cs_current_bb /\
  s.vs_inst_idx = LENGTH sn.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func ce cx ee t /\
    ~t.vs_halted /\ t.vs_current_bb = sp.cs_current_bb /\
    t.vs_inst_idx = LENGTH sp.cs_current_insts /\
    eval_operand len t = SOME
      (n2w (4+LENGTH (enc (vyper_to_abi_type (get_tenv cx) (TupleT tys)) av))) /\
    eval_operand offset t = SOME (n2w (b+28)) /\
    safe_operand sp len /\ safe_operand sp offset /\
    read_memory (b+28)
      (4+LENGTH (enc (vyper_to_abi_type (get_tenv cx) (TupleT tys)) av)) t =
      function_selector fname (vyper_to_abi_types (get_tenv cx) ats) ++
        enc (vyper_to_abi_type (get_tenv cx) (TupleT tys)) av /\
    FLOOKUP t.vs_allocas live = SOME (b,cap) /\
    local_ptrs_reserved ce sp /\ eval_operand buf t = SOME (n2w b) /\
    (!aid r. FLOOKUP s.vs_allocas aid = SOME r ==>
       FLOOKUP t.vs_allocas aid = SOME r) /\
    (!x z. not_fresh_at sn x /\ lookup_var x s = SOME z ==>
       lookup_var x t = SOME z) /\
    (!name p k. local_region ce ee.scopes s name p k ==>
       mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (ce.ce_is_ctor ==> !name tv v p.
       FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc p) /\
       FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
         | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
       mem_bytes_at p (type_memory_size tv) t.vs_memory =
         mem_bytes_at p (type_memory_size tv) s.vs_memory) /\
    (!aid p k. aid < sn.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (p,k) ==>
       FLOOKUP t.vs_allocas aid = SOME (p,k) /\
       (loweringStateRelDefs$regions_disjoint b cap p k ==>
        mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory))
Proof
  strip_tac >>
  `eval_operand (Lit 32w) s = SOME 32w` by simp[eval_operand_def] >>
  drule_all exprExtRequestPrefixOpsTheory.extrequest_add_endpoint >> strip_tac >>
  rename1 `gas_marked_path F ctx func s 0 (OK u)` >>
  `u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `(u with <|vs_vars := _; vs_inst_idx := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `eval_operand srcop u = SOME (n2w source_base)` by
    metis_tac[extrequest_history_operand] >>
  `ci_mono sn st` by
    (qspecl_then [`ADD`, `[buf;Lit 32w]`, `sn`] mp_tac ci_mono_emit_op >> simp[]) >>
  `safe_operand st srcop` by
    (irule safe_operand_mono >> qexists_tac `sn` >> fs[ci_mono_def]) >>
  `!x. srcop = Var x \/ dst = Var x ==> not_fresh_at st x` by
    (qpat_assum `emit_op ADD [buf;Lit 32w] sn = (dst,st)`
       (mp_then Any mp_tac emitted_insts_emit_op) >> strip_tac >>
     fs[safe_operand_def] >> metis_tac[]) >>
  `eval_operand dst u = SOME (n2w (b+32))` by
    simp[wordsTheory.word_add_n2w] >>
  `?at rv. enc at rv = enc (vyper_to_abi_type (get_tenv cx) (TupleT tys)) av /\
     abi_encoder_window_pre ctx func st en dst srcop ei at rv
       source_base (type_memory_size (TupleTV tvs)) (b+32) u` by
    (irule exprExtRequestTupleWindowTheory.extrequest_tuple_window_entry >> simp[] >>
     conj_tac >- metis_tac[] >>
     conj_tac
     >- (qexistsl_tac [`b`, `live`, `cap`, `source_id`, `sz`] >>
         gvs[ci_mono_def] >> decide_tac) >>
     conj_tac >- (qexists_tac `vs` >> gvs[]) >>
     qexistsl_tac [`ce`, `ee`, `env`] >> simp[]) >>
  suspend "encoder"
QED

Resume extrequest_poststore_payload_endpoint[encoder]:
  `!name p k. local_region ce ee.scopes u name p k ==>
    loweringStateRelDefs$regions_disjoint b cap p k` by
    (rpt strip_tac >>
     `local_region ce ee.scopes s name p k` by
       metis_tac[exprExtRequestHistoryTheory.extrequest_history_local_regions] >>
     metis_tac[]) >>
  `32 + LENGTH (enc at rv) <= cap` by metis_tac[] >>
  `mem_bytes_at b 32 u.vs_memory =
     word_to_bytes (n2w (ce.ce_method_id fname ats):bytes32) T` by metis_tac[] >>
  `live < st.cs_next_id /\ FLOOKUP u.vs_allocas live = SOME (b,cap)` by
    (gvs[ci_mono_def] >> decide_tac) >>
  drule_all extrequest_encoder_calldata_endpoint >> strip_tac >>
  `gas_marked_path F ctx func s 0 (OK t)` by
    (qpat_assum `gas_marked_path F ctx func s 0 (OK u)`
       (mp_then Any mp_tac gas_marked_path_then) >>
     disch_then (qspecl_then [`OK t`, `0`] mp_tac) >> simp[]) >>
  `ci_mono st en` by
    (mp_tac (cj 2 ci_mono_compile_abi_encode) >>
     disch_then (qspecl_then [`dst`, `srcop`, `ei`, `st`] mp_tac) >> simp[]) >>
  `local_ptrs_reserved ce en` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `st` >> fs[ci_mono_def]) >>
  `!x z. not_fresh_at sn x /\ lookup_var x s = SOME z ==>
      lookup_var x t = SOME z` by
    (rpt strip_tac >>
     `lookup_var x u = SOME z` by
       (fs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >> metis_tac[]) >>
     `not_fresh_at st x` by
       (fs[ci_mono_def] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
     metis_tac[]) >>
  `eval_operand buf t = SOME (n2w b)` by
    (Cases_on `buf` >> gvs[eval_operand_def, safe_operand_def] >> metis_tac[]) >>
  `safe_operand en buf` by
    (irule safe_operand_mono >> qexists_tac `sn` >> fs[ci_mono_def] >> decide_tac) >>
  `b+28 < dimword (:256) /\ 4+LENGTH (enc at rv) < dimword (:256)` by decide_tac >>
  drule_all extrequest_payload_suffix_endpoint >> strip_tac >>
  rename1 `gas_marked_path F ctx func t 0 (OK r)` >>
  `gas_marked_path F ctx func s 0 (OK r)` by
    (qpat_assum `gas_marked_path F ctx func s 0 (OK t)`
       (mp_then Any mp_tac gas_marked_path_then) >>
     disch_then (qspecl_then [`OK r`, `0`] mp_tac) >> simp[]) >>
  `eval_operand buf r = SOME (n2w b)` by
    (drule_all extrequest_history_operand >> simp[]) >>
  suspend "frames"
QED

Resume extrequest_poststore_payload_endpoint[frames]:
  `!x z. not_fresh_at sn x /\ lookup_var x s = SOME z ==>
      lookup_var x r = SOME z` by
    (rpt strip_tac >>
     `lookup_var x t = SOME z` by metis_tac[] >>
     `not_fresh_at en x` by
       (fs[ci_mono_def] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
     fs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >> metis_tac[]) >>
  `!aid z. FLOOKUP s.vs_allocas aid = SOME z ==>
      FLOOKUP r.vs_allocas aid = SOME z` by metis_tac[] >>
  qexists_tac `r` >> gvs[] >>
  conj_tac
  >- (rpt strip_tac >>
      `local_region ce ee.scopes u name p k` by
        metis_tac[exprExtRequestHistoryTheory.extrequest_history_local_regions] >>
      fs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      fs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `aid < st.cs_next_id /\ FLOOKUP u.vs_allocas aid = SOME (p,k)` by
    (gvs[ci_mono_def] >> decide_tac) >>
  qpat_x_assum `!aid p k. aid < st.cs_next_id /\ _ ==> _`
    (qspecl_then [`aid`, `p`, `k`] mp_tac) >>
  simp[] >> strip_tac >> strip_tac >>
  `venomMemDefs$regions_disjoint (p,k)
    (b+32,LENGTH (enc (Tuple (vyper_to_abi_types (get_tenv cx) tys)) av))` by
    (fs[loweringStateRelDefsTheory.regions_disjoint_def,
        venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  first_x_assum irule >> simp[arithmeticTheory.ADD_COMM]
QED

Finalise extrequest_poststore_payload_endpoint[local]

Theorem extrequest_snapshot_tuple_prefix_from_store:
  extrequest_snapshot_store_contract ctx func ce cx ==>
  EVERY (extrequest_snapshot_cell ctx func ce cx ee sa s) cells /\
  vals = MAP (\(vv,ty,tv,v). vv) cells /\ vals <> [] /\
  tys = MAP (\(vv,ty,tv,v). ty) cells /\
  tvs = MAP (\(vv,ty,tv,v). tv) cells /\
  vs = MAP (\(vv,ty,tv,v). v) cells /\
  sz = SUM (MAP (\(vv,ty,tv,v). type_memory_size tv) cells) /\
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
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
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
    wb_frame ce ee ee sa s t /\ safe_operand sp bufop
Proof
  strip_tac >> strip_tac >>
  drule extrequest_prefix_split >> strip_tac >> gvs[] >>
  `ZIP (MAP (\(vv,ty,tv,v). vv) cells, MAP (\(vv,ty,tv,v). ty) cells) =
    MAP (\(vv,ty,tv,v). (vv,ty)) cells` by
    (simp[rich_listTheory.ZIP_MAP_MAP] >> irule MAP_CONG >> simp[] >>
     rpt strip_tac >> PairCases_on `x` >> simp[]) >>
  drule_all extrequest_tuple_prefix_code >> strip_tac >>
  `32 <= MAX abisz retsz + 32` by decide_tac >>
  drule_all extrequest_alloc_selector_endpoint >> strip_tac >>
  rename1 `gas_marked_path F ctx func s 0 (OK q)` >>
  `EVERY (extrequest_snapshot_cell ctx func ce cx ee sn q) cells` by
    (fs[EVERY_MEM] >> rpt strip_tac >>
     irule extrequest_snapshot_cell_history >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  suspend "tuple"
QED

Resume extrequest_snapshot_tuple_prefix_from_store[tuple]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `compile_extcall_store_values _ _ _ _ sq = _` mp_tac >>
  asm_rewrite_tac[] >> disch_tac >>
  qpat_assum `EVERY (extrequest_snapshot_cell ctx func ce cx ee sn q) cells`
    (mp_then Any mp_tac extrequest_snapshot_allocate_tuple) >>
  simp[] >> strip_tac >>
  rename1 `gas_marked_path F ctx func q 0 (OK u)` >>
  `sa.cs_next_id < sn.cs_next_id /\ sn.cs_next_id < sr.cs_next_id` by
    (qpat_assum `compile_alloc_buffer _ sa = _`
       (mp_then Any mp_tac compile_alloc_buffer_parts) >> strip_tac >>
     qpat_assum `compile_alloc_buffer _ sn = _`
       (mp_then Any mp_tac compile_alloc_buffer_parts) >> strip_tac >>
     fs[ci_mono_def] >> decide_tac) >>
  `safe_operand sr src.buf_operand /\ safe_operand sr buf.buf_operand` by
    (qpat_assum `compile_alloc_buffer _ sa = _`
       (mp_then Any mp_tac compile_alloc_buffer_parts) >> strip_tac >>
     qpat_assum `compile_alloc_buffer _ sn = _`
       (mp_then Any mp_tac compile_alloc_buffer_parts) >> strip_tac >>
     fs[safe_operand_def, ci_mono_def] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `safe_operand sn buf.buf_operand` by
    (qpat_assum `compile_alloc_buffer _ sa = _`
       (mp_then Any mp_tac compile_alloc_buffer_parts) >> strip_tac >>
     simp[safe_operand_def] >> rpt strip_tac >>
     irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sm` >>
     fs[ci_mono_def]) >>
  `eval_operand buf.buf_operand u = SOME w` by
    metis_tac[extrequest_history_operand] >>
  `FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,MAX abisz retsz+32)` by
    (fs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >> metis_tac[]) >>
  `mem_bytes_at (w2n w) 32 u.vs_memory =
      word_to_bytes (n2w (ce.ce_method_id fname ats):bytes32) T` by
    (qpat_x_assum `!aid p k. aid < sn.cs_next_id /\ _ ==> _` drule_all >>
     simp[] >> strip_tac >>
     drule valueEncodingPropsTheory.mem_bytes_at_translated_window >>
     disch_then (qspecl_then [`0`, `32`] mp_tac) >> simp[]) >>
  `!name p k. local_region ce ee.scopes u name p k ==>
    regions_disjoint (w2n w) (MAX abisz retsz+32) p k` by
    (rpt strip_tac >>
     `local_region ce ee.scopes q name p k` by
       metis_tac[exprExtRequestHistoryTheory.extrequest_history_local_regions] >>
     metis_tac[]) >>
  qpat_assum `assignable_type _ _`
    (mp_then Any mp_tac extrequest_poststore_payload_endpoint) >>
  disch_then (fn th => qpat_assum `compile_abi_encode_to_buf _ _ _ st = _`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `emit_op ADD _ sr = _`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `tuple_in_memory _ _ _ u.vs_memory`
    (mp_then Any mp_tac th)) >>
  simp[vyperABITheory.vyper_to_abi_def] >>
  disch_then (fn th => qpat_assum `FLOOKUP u.vs_allocas sa.cs_next_id = _`
    (mp_then Any mp_tac th)) >> simp[] >>
  disch_then (fn th => qpat_assum `stmt_state_rel ctx func ce cx ee u`
    (mp_then Any mp_tac th)) >> simp[] >>
  disch_then (fn th => qpat_assum `FLOOKUP u.vs_allocas sn.cs_next_id = _`
    (mp_then Any mp_tac th)) >> simp[] >>
  disch_then (qspecl_then [`fname`, `env`, `ats`] mp_tac) >> simp[] >>
  (impl_tac >- (conj_tac >> first_assum MATCH_ACCEPT_TAC)) >> strip_tac >>
  rename1 `gas_marked_path F ctx func u 0 (OK t)` >>
  `gas_marked_path F ctx func s 0 (OK u)` by
    (qpat_assum `gas_marked_path F ctx func s 0 (OK q)`
       (mp_then Any mp_tac gas_marked_path_then) >>
     disch_then (qspecl_then [`OK u`, `0`] mp_tac) >> simp[]) >>
  `gas_marked_path F ctx func s 0 (OK t)` by
    (qpat_assum `gas_marked_path F ctx func s 0 (OK u)`
       (mp_then Any mp_tac gas_marked_path_then) >>
     disch_then (qspecl_then [`OK t`, `0`] mp_tac) >> simp[]) >>
  `extrequest_history_frame ce cx ee sa s ee sr u` by
    metis_tac[exprExtRequestHistoryComposeTheory.extrequest_history_frame_trans] >>
  `!x z. not_fresh_at sa x /\ lookup_var x s = SOME z ==>
      lookup_var x t = SOME z` by
    (rpt strip_tac >>
     `lookup_var x u = SOME z` by
       (fs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >> metis_tac[]) >>
     `not_fresh_at sr x` by
       (fs[ci_mono_def] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
     metis_tac[]) >>
  `w2n w + retsz < dimword (:256)` by
    (fs[arithmeticTheory.MAX_DEF] >> rw[] >> decide_tac) >>
  qexistsl_tac [`t`, `w`] >> simp[] >> suspend "frames"
QED

Resume extrequest_snapshot_tuple_prefix_from_store[frames]:
  markerLib.RESUME_TAC >> (
  conj_tac
  >- (rpt strip_tac >>
      `local_region ce ee.scopes u name p k` by
        metis_tac[exprExtRequestHistoryTheory.extrequest_history_local_regions] >>
      fs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `mem_bytes_at p (type_memory_size tv) t.vs_memory =
       mem_bytes_at p (type_memory_size tv) u.vs_memory` by metis_tac[] >>
      qpat_assum `extrequest_history_frame ce cx ee sa s ee sr u`
        (strip_assume_tac o REWRITE_RULE
          [exprExtRequestHistoryTheory.extrequest_history_frame_def]) >>
      fs[Once exprExtRequestHistoryTheory.extrequest_history_frame_def] >>
      qpat_x_assum `!name tv v off. _ ==> mem_bytes_at off _ u.vs_memory = _`
        (qspecl_then [`name`, `tv`, `v`, `p`] mp_tac) >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `FLOOKUP u.vs_allocas aid = SOME (p,k)` by
        (fs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >> metis_tac[]) >>
      metis_tac[]) >>
  suspend "history")
QED

Resume extrequest_snapshot_tuple_prefix_from_store[history]:
  markerLib.RESUME_TAC >> (
  `safe_operand sp buf.buf_operand` by
    (irule safe_operand_mono >> qexists_tac `sr` >> simp[] >>
     fs[ci_mono_def] >> decide_tac) >>
  `!aid p k. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (p,k) ==>
     regions_disjoint (w2n w) (MAX abisz retsz+32) p k` by
    (rpt strip_tac >>
     `FLOOKUP u.vs_allocas aid = SOME (p,k)` by
       (fs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >> metis_tac[]) >>
     `allocas_non_overlapping u` by
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
         `FLOOKUP u.vs_allocas aid = SOME b` by
           (fs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >> metis_tac[]) >>
         metis_tac[])
     >- (rpt strip_tac >>
         `local_region ce ee.scopes u n b sz` by
           metis_tac[exprExtRequestHistoryTheory.extrequest_history_local_regions] >>
         fs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >> metis_tac[])
     >- (rpt strip_tac >>
         `aid < sr.cs_next_id /\ FLOOKUP u.vs_allocas aid = SOME (b,sz)` by
           (fs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >> metis_tac[]) >>
         `regions_disjoint (w2n w) (MAX abisz retsz+32) b sz` by metis_tac[] >>
         `mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz u.vs_memory` by metis_tac[] >>
         qpat_assum `extrequest_history_frame ce cx ee sa s ee sr u`
           (strip_assume_tac o REWRITE_RULE
             [exprExtRequestHistoryTheory.extrequest_history_frame_def]) >>
         metis_tac[])
     >> (rpt strip_tac >>
         `mem_bytes_at off (type_memory_size tv) t.vs_memory =
          mem_bytes_at off (type_memory_size tv) u.vs_memory` by metis_tac[] >>
         qpat_assum `extrequest_history_frame ce cx ee sa s ee sr u`
           (strip_assume_tac o REWRITE_RULE
             [exprExtRequestHistoryTheory.extrequest_history_frame_def]) >>
         fs[Once exprExtRequestHistoryTheory.extrequest_history_frame_def] >>
         qpat_x_assum `!name tv v off. _ ==> mem_bytes_at off _ u.vs_memory = _`
           (qspecl_then [`name`, `tv`, `v`, `off`] mp_tac) >> simp[])) >>
  simp[] >> drule extrequest_history_writeback >> simp[])

QED

Finalise extrequest_snapshot_tuple_prefix_from_store
