(* Calldata bytes at the request buffer's selector/payload boundary. *)
Theory exprExtRequestPayload
Ancestors
  exprExtRequestPrefixOps exprExtRequestEncoderState exprExtRequestTupleWindow
  exprExtRequestReconstruct exprExtRequestHistoryCompose exprSafeOperand fragGasMode
  exprExtRequestTupleFold exprExtRequestAllocationEndpoint loweringHalt
  compileEnv loweringStateRelDefs emitHelperProps exprLoweringProps
  valueEncoding valueEncodingDefs valueEncodingProps valueEncodingProofs venomState venomExecSemantics
  vyperABI selectorDispatch list arithmetic

Theorem extrequest_calldata_window:
  expr_sim_inv ce cx env ee /\
  mem_bytes_at b 32 s.vs_memory =
    word_to_bytes (n2w (ce.ce_method_id fname tys):bytes32) T /\
  mem_bytes_at (b+32) (LENGTH payload) s.vs_memory = payload ==>
  read_memory (b+28) (4+LENGTH payload) s =
    function_selector fname (vyper_to_abi_types (get_tenv cx) tys) ++ payload
Proof
  strip_tac >>
  `mem_bytes_at (b+28) 4 s.vs_memory =
    function_selector fname (vyper_to_abi_types (get_tenv cx) tys)` by
    (irule extrequest_selector_window >> metis_tac[]) >>
  rewrite_tac[read_memory_def, GSYM mem_bytes_at_def] >>
  `mem_bytes_at (b+28) (4+LENGTH payload) s.vs_memory =
    mem_bytes_at (b+28) 4 s.vs_memory ++
    mem_bytes_at (b+32) (LENGTH payload) s.vs_memory` by
    (mp_tac (Q.SPECL [`b+28`, `4`, `LENGTH (payload:byte list)`, `s.vs_memory`]
       mem_bytes_at_split_padded) >> simp[]) >>
  fs[]
QED

Theorem extrequest_offset_endpoint:
  emit_op ADD [buf;Lit 28w] sa = (offset,sb) /\
  eval_operand buf s = SOME (n2w b) /\
  eval_operand len s = SOME (n2w n) /\ safe_operand sa len /\
  read_memory (b+28) n s = calldata /\
  b+28 < dimword (:256) /\ n < dimword (:256) /\
  fn_has_code sa sb func /\ local_ptrs_reserved ce sa /\
  stmt_state_rel ctx func ce cx ee s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func ce cx ee t /\
    extrequest_history_frame ce cx ee sa s ee sb t /\
    eval_operand offset t = SOME (n2w (b+28)) /\
    eval_operand len t = SOME (n2w n) /\
    read_memory (b+28) n t = calldata /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    local_ptrs_reserved ce sb /\ safe_operand sb offset /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_memory = s.vs_memory
Proof
  strip_tac >>
  `eval_operand (Lit 28w) s = SOME 28w` by simp[eval_operand_def] >>
  drule_all extrequest_add_endpoint >> strip_tac >>
  `eval_operand len t = SOME (n2w n)` by
    (drule_all extrequest_history_operand >> simp[]) >>
  `t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
   t.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `(t with <|vs_vars := _; vs_inst_idx := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  qexists_tac `t` >> fs[read_memory_def, wordsTheory.word_add_n2w]
QED

Theorem extrequest_empty_payload_endpoint:
  compile_alloc_buffer sz sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand; Lit (n2w (ce.ce_method_id fname tys))]
    sm = ((),sn) /\
  emit_op ADD [buf.buf_operand;Lit 28w] sn = (offset,sb) /\
  fn_has_code sa sm func /\ fn_has_code sm sn func /\
  fn_has_code sn sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx ee s /\ expr_sim_inv ce cx env ee /\
  local_ptrs_reserved ce sa /\ 32 <= sz /\ sz < dimword (:256) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
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
    eval_operand buf.buf_operand t = SOME w
Proof
  strip_tac >> drule_all extrequest_alloc_selector_endpoint >> strip_tac >>
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
  qexistsl_tac [`t`, `w`] >> simp[]
QED

(* Protect the selector within the very allocation used for the payload. *)
Theorem extrequest_encoder_calldata_endpoint:
  compile_abi_encode_to_buf dst src ei st = (out,en) /\
  abi_encoder_window_pre ctx func st en dst src ei at av source source_cap
    (b+32) s /\
  stmt_state_rel ctx func ce cx ee s /\ local_ptrs_reserved ce st /\
  expr_sim_inv ce cx env ee /\
  live < st.cs_next_id /\ FLOOKUP s.vs_allocas live = SOME (b,sz) /\
  32 + LENGTH (enc at av) <= sz /\
  mem_bytes_at b 32 s.vs_memory =
    word_to_bytes (n2w (ce.ce_method_id fname tys):bytes32) T /\
  (!name p k. local_region ce ee.scopes s name p k ==>
    loweringStateRelDefs$regions_disjoint b sz p k) /\
  (ce.ce_is_ctor ==> !name tv v p.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc p) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    loweringStateRelDefs$regions_disjoint b sz p (type_memory_size tv)) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func ce cx ee t /\
    ~t.vs_halted /\ t.vs_current_bb = en.cs_current_bb /\
    t.vs_inst_idx = LENGTH en.cs_current_insts /\
    eval_operand out t = SOME (n2w (LENGTH (enc at av))) /\
    read_memory (b+28) (4+LENGTH (enc at av)) t =
      function_selector fname (vyper_to_abi_types (get_tenv cx) tys) ++ enc at av /\
    FLOOKUP t.vs_allocas live = SOME (b,sz) /\
    (!x w. not_fresh_at st x /\ lookup_var x s = SOME w ==>
      lookup_var x t = SOME w) /\
    abi_encoder_registered_effect (window_alloca_sites func (frag_ids st en))
      [(b+32,LENGTH (enc at av))] s t /\ window_alloca_growth s t /\
    t.vs_labels = s.vs_labels /\ t.vs_fmp = s.vs_fmp /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
    t.vs_outcomes = s.vs_outcomes /\ t.vs_immutables = s.vs_immutables /\
    (!name p k. local_region ce ee.scopes s name p k ==>
      mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (ce.ce_is_ctor ==> !name tv v p.
      FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc p) /\
      FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
      mem_bytes_at p (type_memory_size tv) t.vs_memory =
        mem_bytes_at p (type_memory_size tv) s.vs_memory) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    (!aid r. FLOOKUP s.vs_allocas aid = SOME r ==>
       FLOOKUP t.vs_allocas aid = SOME r) /\
    (!aid p k. aid < st.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (p,k) ==>
      FLOOKUP t.vs_allocas aid = SOME (p,k) /\
      (!a n. p <= a /\ a + n <= p + k /\
        venomMemDefs$regions_disjoint (a,n) (b+32,LENGTH (enc at av)) ==>
        mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory))
Proof
  strip_tac >>
  `venomMemDefs$regions_disjoint (b,32) (b+32,LENGTH (enc at av))` by
    simp[venomMemDefsTheory.regions_disjoint_def] >>
  `!name p k. local_region ce ee.scopes s name p k ==>
    venomMemDefs$regions_disjoint (p,k) (b+32,LENGTH (enc at av))` by
    (rpt strip_tac >> first_x_assum drule >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def,
       venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `ce.ce_is_ctor ==> !name tv v p.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc p) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    venomMemDefs$regions_disjoint (p,type_memory_size tv)
      (b+32,LENGTH (enc at av))` by
    (rpt strip_tac >> qpat_x_assum `ce.ce_is_ctor ==> _` drule >>
     disch_then drule >> simp[loweringStateRelDefsTheory.regions_disjoint_def,
       venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `b <= b /\ b + 32 <= b + sz` by decide_tac >>
  drule_all extrequest_encoder_run_state >> strip_tac >>
  `read_memory (b+28) (4+LENGTH (enc at av)) t =
    function_selector fname (vyper_to_abi_types (get_tenv cx) tys) ++ enc at av` by
    (irule extrequest_calldata_window >> metis_tac[]) >>
  `fn_has_code st en func /\ fn_inst_ids_distinct func /\
   alloca_inv s /\ local_ptrs_rel func ce ee.scopes s /\
   immutable_alloca_sep func ce cx ee s` by
    fs[abiEncoderWindowContractTheory.abi_encoder_window_pre_def,
       stmt_state_rel_def, state_rel_def] >>
  `!name p k. local_region ce ee.scopes s name p k ==>
    mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory` by
    (rpt strip_tac >>
     irule exprExtRequestEncoderWindowsTheory.extrequest_encoder_local_window >>
     qpat_assum `abi_encoder_registered_effect _ _ s t` (irule_at Any) >>
     simp[] >> metis_tac[]) >>
  `ce.ce_is_ctor ==> !name tv v p.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc p) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    mem_bytes_at p (type_memory_size tv) t.vs_memory =
      mem_bytes_at p (type_memory_size tv) s.vs_memory` by
    (rpt strip_tac >>
     irule exprExtRequestEncoderWindowsTheory.extrequest_encoder_immutable_window >>
     qpat_assum `abi_encoder_registered_effect _ _ s t` (irule_at Any) >>
     simp[] >> metis_tac[]) >>
  `!aid r. FLOOKUP s.vs_allocas aid = SOME r ==>
     FLOOKUP t.vs_allocas aid = SOME r` by
    (fs[abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_def]) >>
  qexists_tac `t` >> simp[] >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >>
  rpt strip_tac >> qpat_x_assum `!aid q k. _` drule_all >>
  strip_tac >> first_x_assum irule >> simp[ADD_COMM]
QED

(* Capture root is immediately before the tuple allocation, after selector. *)
Theorem extrequest_allocate_tuple_endpoint:
  EVERY (extrequest_tuple_cell ctx func ce cx ee sa s ee) cells /\
  sz = SUM (MAP (\(e,r,vv,ty,tv,v). type_memory_size tv) cells) /\
  compile_alloc_buffer sz sa = (buf,sm) /\
  compile_extcall_store_values ce
    (MAP (\(e,r,vv,ty,tv,v). (vv,ty)) cells) buf.buf_operand 0 sm = ((),sb) /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx ee s /\ local_ptrs_reserved ce sa /\
  ee.gas_obs = [] /\ sz < dimword (:256) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
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
       mem_bytes_at p k q.vs_memory = mem_bytes_at p k s.vs_memory)
Proof
  strip_tac >> drule_all extrequest_allocation_endpoint >> strip_tac >>
  `safe_operand sm buf.buf_operand` by
    (gvs[safe_operand_def] >> metis_tac[]) >>
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
  `sa.cs_next_id <= sa.cs_next_id /\ w2n w <= w2n w /\
   w2n w + SUM (MAP (\(e,r,vv,ty,tv,v). type_memory_size tv) cells) <= w2n w + sz` by simp[] >>
  `ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    regions_disjoint off (type_memory_size tv) (w2n w) sz` by metis_tac[] >>
  drule_at (Pat `EVERY _ _`) extrequest_tuple_store_fold >>
  disch_then (drule_at (Pat `compile_extcall_store_values _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `extrequest_history_frame _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME (_,_)`)) >>
  simp[] >> disch_then (qspec_then `sa.cs_next_id` mp_tac) >>
  simp[] >> (impl_tac >- gvs[]) >> strip_tac >>
  `eval_operand buf.buf_operand q = SOME w` by
    (simp[eval_operand_def] >> first_x_assum irule >> gvs[eval_operand_def]) >>
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

(* The two fixed ADDs following a nonempty encoded payload. *)
Theorem extrequest_payload_suffix_endpoint:
  emit_op ADD [out;Lit 4w] en = (len,sl) /\
  emit_op ADD [buf;Lit 28w] sl = (offset,sp) /\
  fn_has_code en sl func /\ fn_has_code sl sp func /\
  stmt_state_rel ctx func ce cx ee s /\ local_ptrs_reserved ce en /\
  eval_operand out s = SOME (n2w n) /\
  eval_operand buf s = SOME (n2w b) /\ safe_operand en buf /\
  read_memory (b+28) (4+n) s = calldata /\
  b+28 < dimword (:256) /\ 4+n < dimword (:256) /\
  ~s.vs_halted /\ s.vs_current_bb = en.cs_current_bb /\
  s.vs_inst_idx = LENGTH en.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func ce cx ee t /\
    extrequest_history_frame ce cx ee en s ee sp t /\
    eval_operand len t = SOME (n2w (4+n)) /\
    eval_operand offset t = SOME (n2w (b+28)) /\
    read_memory (b+28) (4+n) t = calldata /\
    ~t.vs_halted /\ t.vs_current_bb = sp.cs_current_bb /\
    t.vs_inst_idx = LENGTH sp.cs_current_insts /\
    local_ptrs_reserved ce sp /\ safe_operand sp offset /\
    safe_operand sp len /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_memory = s.vs_memory
Proof
  strip_tac >>
  `eval_operand (Lit 4w) s = SOME 4w` by simp[eval_operand_def] >>
  drule_all extrequest_add_endpoint >> strip_tac >>
  rename1 `gas_marked_path F ctx func s 0 (OK u)` >>
  `eval_operand buf u = SOME (n2w b)` by
    (drule_all extrequest_history_operand >> simp[]) >>
  `u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
   u.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `(u with <|vs_vars := _; vs_inst_idx := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `eval_operand len u = SOME (n2w (4+n))` by
    simp[wordsTheory.word_add_n2w, ADD_COMM] >>
  `read_memory (b+28) (4+n) u = calldata` by fs[read_memory_def] >>
  drule_all extrequest_offset_endpoint >> strip_tac >>
  `extrequest_history_frame ce cx ee en s ee sp t` by
    (drule_all extrequest_history_frame_trans >> simp[]) >>
  `safe_operand sp len` by
    (irule safe_operand_mono >> qexists_tac `sl` >>
     drule emitted_insts_emit_op >> simp[ci_mono_def]) >>
  `gas_marked_path F ctx func s 0 (OK t)` by
    (qpat_assum `gas_marked_path F ctx func s 0 (OK u)`
       (mp_then Any mp_tac gas_marked_path_then) >>
     disch_then (qspecl_then [`OK t`, `0`] mp_tac) >> simp[]) >>
  qexists_tac `t` >> gvs[]
QED

(* Nonempty payload: allocate and fill the tuple, then enter the encoder at
   the actual destination ADD.  The destination row predates the captures. *)
Theorem extrequest_tuple_payload_endpoint:
  EVERY (extrequest_tuple_cell ctx func ce cx ee sa s ee) cells /\
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
  compile_alloc_buffer sz sa = (src,sm) /\
  compile_extcall_store_values ce
    (MAP (\(e,r,vv,ty,tv,v). (vv,ty)) cells) src.buf_operand 0 sm = ((),sn) /\
  emit_op ADD [buf;Lit 32w] sn = (dst,st) /\
  compile_abi_encode_to_buf dst src.buf_operand ei st = (out,en) /\
  emit_op ADD [out;Lit 4w] en = (len,sl) /\
  emit_op ADD [buf;Lit 28w] sl = (offset,sp) /\
  fn_has_code en sl func /\ fn_has_code sl sp func /\
  fn_has_code sa sm func /\ fn_has_code sm sn func /\
  fn_has_code sn st func /\ fn_has_code st en func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx ee s /\ expr_sim_inv ce cx env ee /\
  local_ptrs_reserved ce sa /\ ee.gas_obs = [] /\ sz < dimword (:256) /\
  live < sa.cs_next_id /\ FLOOKUP s.vs_allocas live = SOME (b,cap) /\
  b + cap < dimword (:256) /\
  32 + LENGTH (enc (vyper_to_abi_type (get_tenv cx) (TupleT tys)) av) <= cap /\
  eval_operand buf s = SOME (n2w b) /\ safe_operand sa buf /\
  mem_bytes_at b 32 s.vs_memory =
    word_to_bytes (n2w (ce.ce_method_id fname ats):bytes32) T /\
  (!name p k. local_region ce ee.scopes s name p k ==>
    loweringStateRelDefs$regions_disjoint b cap p k) /\
  (ce.ce_is_ctor ==> !name tv v p.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc p) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    loweringStateRelDefs$regions_disjoint b cap p (type_memory_size tv)) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
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
    local_ptrs_reserved ce sp /\
    eval_operand buf t = SOME (n2w b) /\ 
    (!aid r. FLOOKUP s.vs_allocas aid = SOME r ==>
       FLOOKUP t.vs_allocas aid = SOME r) /\
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
       FLOOKUP t.vs_allocas aid = SOME (p,k) /\
       (loweringStateRelDefs$regions_disjoint b cap p k ==>
        mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory))
Proof
  strip_tac >> drule_all extrequest_allocate_tuple_endpoint >> strip_tac >>
  rename1 `gas_marked_path F ctx func s 0 (OK q)` >>
  `eval_operand buf q = SOME (n2w b)` by
    (drule_all extrequest_history_operand >> simp[]) >>
  `eval_operand (Lit 32w) q = SOME 32w` by simp[eval_operand_def] >>
  drule_all extrequest_add_endpoint >> strip_tac >>
  rename1 `gas_marked_path F ctx func q 0 (OK u)` >>
  `extrequest_history_frame ce cx ee sa s ee st u` by
    (drule_all extrequest_history_frame_trans >> simp[]) >>
  suspend "entry"
QED

Resume extrequest_tuple_payload_endpoint[entry]:
  `ci_mono sm sn` by
    (qspecl_then [`MAP (\(e,r,vv,ty,tv,v). (vv,ty)) cells`, `0`, `sm`] mp_tac
       (Q.INST [`cenv` |-> `ce`, `buf` |-> `src.buf_operand`]
         extrequest_store_values_mono) >> simp[]) >>
  `safe_operand sn src.buf_operand` by
    (drule compile_alloc_buffer_parts >> strip_tac >>
     simp[safe_operand_def] >> rpt strip_tac >>
     irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sm` >> gvs[ci_mono_def]) >>
  `eval_operand src.buf_operand u = SOME w` by
    metis_tac[extrequest_history_operand] >>
  `u.vs_memory = q.vs_memory /\ u.vs_allocas = q.vs_allocas` by
    (qpat_x_assum `(u with <|vs_vars := _; vs_inst_idx := _|>) = q` mp_tac >>
     simp[venom_state_component_equality]) >>
  `tuple_in_memory vs tvs (w2n w) u.vs_memory` by metis_tac[] >>
  `FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,sz)` by simp[] >>
  `FLOOKUP u.vs_allocas live = SOME (b,cap)` by
    (fs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >> metis_tac[]) >>
  `sa.cs_next_id < st.cs_next_id` by
    (drule compile_alloc_buffer_parts >>
     qpat_assum `emit_op ADD [buf;Lit 32w] sn = (dst,st)`
       (mp_then Any mp_tac emitted_insts_emit_op) >>
     gvs[ci_mono_def] >> decide_tac) >>
  `live < st.cs_next_id /\ sa.cs_next_id <> live` by decide_tac >>
  `eval_operand dst u = SOME (n2w (b+32))` by
    simp[wordsTheory.word_add_n2w] >>
  `!x. src.buf_operand = Var x \/ dst = Var x ==> not_fresh_at st x` by
    (qpat_assum `emit_op ADD [buf;Lit 32w] sn = (dst,st)`
       (mp_then Any mp_tac emitted_insts_emit_op) >> strip_tac >>
     `safe_operand st src.buf_operand` by
       (irule safe_operand_mono >> qexists_tac `sn` >> simp[]) >>
     fs[safe_operand_def] >> metis_tac[]) >>
  `?at rv. enc at rv = enc (vyper_to_abi_type (get_tenv cx) (TupleT tys)) av /\
     abi_encoder_window_pre ctx func st en dst src.buf_operand ei at rv
       (w2n w) (type_memory_size (TupleTV tvs)) (b+32) u` by
    (irule extrequest_tuple_window_entry >> simp[] >>
     conj_tac >- metis_tac[] >>
     conj_tac
     >- (qexistsl_tac [`b`, `live`, `cap`, `sa.cs_next_id`, `sz`] >>
         gvs[]) >>
     conj_tac
     >- (qexists_tac `vs` >> gvs[]) >>
     qexistsl_tac [`ce`, `ee`, `env`] >> simp[]) >>
  suspend "encoder"
QED

Resume extrequest_tuple_payload_endpoint[encoder]:
  `mem_bytes_at b 32 u.vs_memory = mem_bytes_at b 32 s.vs_memory` by
    (irule extrequest_history_alloc_window >>
     qpat_assum `extrequest_history_frame ce cx ee sa s ee st u`
       (irule_at Any) >>
     goal_assum (drule_at Any) >> simp[] >>
     fs[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[ADD_COMM]) >>
  `!name p k. local_region ce ee.scopes u name p k ==>
    loweringStateRelDefs$regions_disjoint b cap p k` by
    (rpt strip_tac >>
     `local_region ce ee.scopes s name p k` by
       metis_tac[exprExtRequestHistoryTheory.extrequest_history_local_regions] >>
     metis_tac[]) >>
  `32 + LENGTH (enc at rv) <= cap` by metis_tac[] >>
  `mem_bytes_at b 32 u.vs_memory =
     word_to_bytes (n2w (ce.ce_method_id fname ats):bytes32) T` by metis_tac[] >>
  drule_all extrequest_encoder_calldata_endpoint >> strip_tac >>
  `gas_marked_path F ctx func s 0 (OK u)` by
    (qpat_assum `gas_marked_path F ctx func s 0 (OK q)`
      (mp_then Any mp_tac gas_marked_path_then) >>
     disch_then (qspecl_then [`OK u`, `0`] mp_tac) >> simp[]) >>
  `gas_marked_path F ctx func s 0 (OK t)` by
    (qpat_assum `gas_marked_path F ctx func s 0 (OK u)`
      (mp_then Any mp_tac gas_marked_path_then) >>
     disch_then (qspecl_then [`OK t`, `0`] mp_tac) >> simp[]) >>
  `ci_mono st en` by
    (mp_tac (cj 2 ci_mono_compile_abi_encode) >>
     disch_then (qspecl_then [`dst`, `src.buf_operand`, `ei`, `st`] mp_tac) >>
     simp[]) >>
  `local_ptrs_reserved ce en` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `st` >>
     fs[ci_mono_def]) >>
  `!x z. not_fresh_at sa x /\ lookup_var x s = SOME z ==>
      lookup_var x t = SOME z` by
    (rpt strip_tac >>
     `lookup_var x u = SOME z` by
       (fs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >> metis_tac[]) >>
     `not_fresh_at st x` by
       (fs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >>
        metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
     metis_tac[]) >>
  `eval_operand buf t = SOME (n2w b)` by
    (Cases_on `buf` >> gvs[eval_operand_def, safe_operand_def] >> metis_tac[]) >>
  `safe_operand en buf` by
    (irule safe_operand_mono >> qexists_tac `st` >>
     fs[ci_mono_def] >>
     irule safe_operand_mono >> qexists_tac `sa` >>
     fs[exprExtRequestHistoryTheory.extrequest_history_frame_def]) >>
  `b+28 < dimword (:256) /\ 4+LENGTH (enc at rv) < dimword (:256)` by decide_tac >>
  drule_all extrequest_payload_suffix_endpoint >> strip_tac >>
  rename1 `gas_marked_path F ctx func t 0 (OK r)` >>
  `gas_marked_path F ctx func s 0 (OK r)` by
    (qpat_assum `gas_marked_path F ctx func s 0 (OK t)`
       (mp_then Any mp_tac gas_marked_path_then) >>
     disch_then (qspecl_then [`OK r`, `0`] mp_tac) >> simp[]) >>
  `eval_operand buf r = SOME (n2w b)` by
    (drule_all extrequest_history_operand >> simp[]) >>
  `!x z. not_fresh_at sa x /\ lookup_var x s = SOME z ==>
      lookup_var x r = SOME z` by
    (rpt strip_tac >>
     `lookup_var x t = SOME z` by metis_tac[] >>
     `not_fresh_at en x` by
       (fs[exprExtRequestHistoryTheory.extrequest_history_frame_def, ci_mono_def] >>
        metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
     fs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >> metis_tac[]) >>
  `!aid z. FLOOKUP s.vs_allocas aid = SOME z ==>
      FLOOKUP r.vs_allocas aid = SOME z` by
    (rpt strip_tac >>
     `FLOOKUP u.vs_allocas aid = SOME z` by
       (fs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >> metis_tac[]) >>
     `FLOOKUP t.vs_allocas aid = SOME z` by metis_tac[] >> simp[]) >>
  qexists_tac `r` >> gvs[] >> suspend "frames"
QED

Resume extrequest_tuple_payload_endpoint[frames]:
  conj_tac
  >- (rpt strip_tac >>
      `local_region ce ee.scopes u name p k` by
        metis_tac[exprExtRequestHistoryTheory.extrequest_history_local_regions] >>
      fs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      fs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `aid < st.cs_next_id /\ FLOOKUP q.vs_allocas aid = SOME (p,k)` by
    (fs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >> metis_tac[]) >>
  `FLOOKUP t.vs_allocas aid = SOME (p,k)` by metis_tac[] >>
  qpat_x_assum `!aid p k. aid < st.cs_next_id /\ _ ==> _`
    (qspecl_then [`aid`, `p`, `k`] mp_tac) >>
  simp[] >> strip_tac >> strip_tac >>
  `venomMemDefs$regions_disjoint (p,k)
    (b+32,LENGTH (enc (vyper_to_abi_type (get_tenv cx)
      (TupleT (MAP (\(e,r,vv,ty,tv,v). ty) cells))) av))` by
    (fs[loweringStateRelDefsTheory.regions_disjoint_def,
        venomMemDefsTheory.regions_disjoint_def, vyperABITheory.vyper_to_abi_type_def] >>
     decide_tac) >>
  `mem_bytes_at p k t.vs_memory = mem_bytes_at p k q.vs_memory` by
    (first_x_assum irule >> simp[ADD_COMM] >>
     qpat_x_assum `venomMemDefs$regions_disjoint (p,k) _` mp_tac >>
     pure_rewrite_tac[vyperABITheory.vyper_to_abi_type_def] >> simp[]) >>
  `mem_bytes_at p k q.vs_memory = mem_bytes_at p k s.vs_memory` by
    (qpat_assum `!aid p k. aid < sa.cs_next_id /\ _ ==> _` drule_all >> simp[]) >>
  metis_tac[]
QED

Finalise extrequest_tuple_payload_endpoint

