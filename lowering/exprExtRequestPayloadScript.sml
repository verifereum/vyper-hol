(* Calldata bytes at the request buffer's selector/payload boundary. *)
Theory exprExtRequestPayload
Ancestors
  exprExtRequestPrefixOps exprExtRequestEncoderState exprExtRequestTupleWindow
  exprExtRequestReconstruct exprExtRequestHistoryCompose exprSafeOperand fragGasMode
  valueEncoding valueEncodingProps valueEncodingProofs venomState venomExecSemantics
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
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
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
    local_ptrs_reserved ce sb /\ safe_operand sb offset
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
    compileEnv$regions_disjoint b sz p k) /\
  (ce.ce_is_ctor ==> !name tv v p.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc p) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    compileEnv$regions_disjoint b sz p (type_memory_size tv)) ==>
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
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
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
     simp[compileEnvTheory.regions_disjoint_def,
       venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `ce.ce_is_ctor ==> !name tv v p.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc p) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    venomMemDefs$regions_disjoint (p,type_memory_size tv)
      (b+32,LENGTH (enc at av))` by
    (rpt strip_tac >> qpat_x_assum `ce.ce_is_ctor ==> _` drule >>
     disch_then drule >> simp[compileEnvTheory.regions_disjoint_def,
       venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `b <= b /\ b + 32 <= b + sz` by decide_tac >>
  drule_all extrequest_encoder_run_state >> strip_tac >>
  `read_memory (b+28) (4+LENGTH (enc at av)) t =
    function_selector fname (vyper_to_abi_types (get_tenv cx) tys) ++ enc at av` by
    (irule extrequest_calldata_window >> metis_tac[]) >>
  qexists_tac `t` >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!aid q k. _` drule_all >>
  strip_tac >> first_x_assum irule >> simp[ADD_COMM]
QED
