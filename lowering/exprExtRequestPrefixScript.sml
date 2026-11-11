(* Compiler stage boundary for the full request prefix. *)
Theory exprExtRequestPrefix
Ancestors
  exprExtRequestShape exprExtRequestPayload exprExtRequestHistoryCompose
  exprExtRequestTupleFold loweringHalt exprSafeOperand fragGasMode
  exprLoweringProps emitHelperProps compileEnv loweringStateRelDefs list fragExec venomExecSemantics venomState
  abiEncoderInputFrame loweringPosts

Theorem extrequest_prefix_split:
  extrequest_compile_prefix ce vals tys memsz abisz mid retsz ei sa =
    ((bufop,offset,len),sp) ==>
  ?buf sm sn.
    compile_alloc_buffer (MAX abisz retsz + 32) sa = (buf,sm) /\
    emit_void MSTORE [buf.buf_operand;Lit (n2w mid)] sm = ((),sn) /\
    bufop = buf.buf_operand /\
    ((vals = [] /\ len = Lit 4w /\
      emit_op ADD [buf.buf_operand;Lit 28w] sn = (offset,sp)) \/
     (vals <> [] /\ ?src sq sr dst st out en sl.
       compile_alloc_buffer memsz sn = (src,sq) /\
       compile_extcall_store_values ce (ZIP (vals,tys)) src.buf_operand 0 sq =
         ((),sr) /\
       emit_op ADD [buf.buf_operand;Lit 32w] sr = (dst,st) /\
       compile_abi_encode_to_buf dst src.buf_operand ei st = (out,en) /\
       emit_op ADD [out;Lit 4w] en = (len,sl) /\
       emit_op ADD [buf.buf_operand;Lit 28w] sl = (offset,sp)))
Proof
  simp[extrequest_compile_prefix_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, arithmeticTheory.MAX_DEF] >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `vals = []` >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[comp_return_def] >> strip_tac >> gvs[] >>
  `((if abisz > retsz then abisz else retsz) + 32) =
   ((if abisz < retsz then retsz else abisz) + 32)` by
    (rw[] >> decide_tac) >>
  gvs[] >> goal_assum (drule_at Any) >> simp[] >>
  fs[comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt (goal_assum (drule_at Any) >> simp[])
QED

Theorem extrequest_history_writeback:
  extrequest_history_frame ce cx ec sa s ee sp t ==>
  wb_frame ce ec sa s t
Proof
  strip_tac >> simp[wb_frame_def] >> rpt conj_tac
  >- (fs[exprExtRequestHistoryTheory.extrequest_history_frame_def])
  >- (fs[exprExtRequestHistoryTheory.extrequest_history_frame_def])
  >- (rpt strip_tac >>
      fs[exprExtRequestHistoryTheory.extrequest_history_frame_def,
         loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
  rewrite_tac[locals_kept_def] >> rpt strip_tac >>
  `mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory` by
    (fs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >> metis_tac[]) >>
  `off = b + (off-b) /\ off-b+len <= sz` by decide_tac >>
  drule abi_encoder_window_slice >>
  disch_then (qspecl_then [`off-b`, `len`] mp_tac) >> simp[]
QED

Theorem extrequest_empty_prefix_endpoint:
  extrequest_compile_prefix ce [] tys memsz abisz (ce.ce_method_id fname tys)
    retsz ei sa = ((bufop,offset,len),sp) /\
  fn_has_code sa sp func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx ee s /\ expr_sim_inv ce cx env ee /\
  local_ptrs_reserved ce sa /\ MAX abisz retsz + 32 < dimword (:256) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
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
    safe_operand sp bufop /\ safe_operand sp len
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
  drule_all extrequest_empty_payload_endpoint >> strip_tac >>
  `wb_frame ce ee sa s t` by metis_tac[extrequest_history_writeback] >>
  `safe_operand sp buf.buf_operand` by
    (drule compile_alloc_buffer_parts >> strip_tac >>
     simp[safe_operand_def] >> rpt strip_tac >>
     irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sm` >>
     fs[ci_mono_def] >> decide_tac) >>
  qexistsl_tac [`t`, `w`] >> simp[eval_operand_def, safe_operand_def] >>
  fs[arithmeticTheory.MAX_DEF] >> rw[] >> decide_tac
QED

Theorem extrequest_tuple_prefix_code:
  compile_alloc_buffer cap sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand;Lit wd] sm = ((),sn) /\
  compile_alloc_buffer sz sn = (src,sq) /\
  compile_extcall_store_values ce cells src.buf_operand 0 sq = ((),sr) /\
  emit_op ADD [buf.buf_operand;Lit 32w] sr = (dst,st) /\
  compile_abi_encode_to_buf dst src.buf_operand ei st = (out,en) /\
  emit_op ADD [out;Lit 4w] en = (len,sl) /\
  emit_op ADD [buf.buf_operand;Lit 28w] sl = (offset,sp) /\
  fn_has_code sa sp func ==>
  ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn sq /\ ci_mono sq sr /\
  ci_mono sr st /\ ci_mono st en /\ ci_mono en sl /\ ci_mono sl sp /\
  fn_has_code sa sm func /\ fn_has_code sm sn func /\
  fn_has_code sn sq func /\ fn_has_code sq sr func /\
  fn_has_code sr st func /\ fn_has_code st en func /\
  fn_has_code en sl func /\ fn_has_code sl sp func
Proof
  strip_tac >>
  `ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn sq /\ ci_mono sq sr /\
   ci_mono sr st /\ ci_mono st en /\ ci_mono en sl /\ ci_mono sl sp` by
    (rpt conj_tac
     >- metis_tac[ci_mono_compile_alloc_buffer, pairTheory.SND]
     >- metis_tac[ci_mono_emit_void, pairTheory.SND]
     >- metis_tac[ci_mono_compile_alloc_buffer, pairTheory.SND]
     >- metis_tac[extrequest_store_values_mono, pairTheory.SND]
     >- metis_tac[ci_mono_emit_op, pairTheory.SND]
     >- metis_tac[cj 2 ci_mono_compile_abi_encode, pairTheory.SND]
     >- metis_tac[ci_mono_emit_op, pairTheory.SND]
     >> metis_tac[ci_mono_emit_op, pairTheory.SND]) >>
  simp[] >> fs[ci_mono_def] >>
  `cs_extends sl sp` by simp[] >>
  `cs_extends en sp` by metis_tac[cs_extends_trans] >>
  `cs_extends st sp` by metis_tac[cs_extends_trans] >>
  `cs_extends sr sp` by metis_tac[cs_extends_trans] >>
  `cs_extends sq sp` by metis_tac[cs_extends_trans] >>
  `cs_extends sn sp` by metis_tac[cs_extends_trans] >>
  `cs_extends sm sp` by metis_tac[cs_extends_trans] >>
  map_every (fn (a,b) =>
    mp_tac (Q.SPECL [a,b,`sp`,`func`] fn_has_code_split) >>
    simp[] >> strip_tac)
    [(`sa`,`sm`), (`sm`,`sn`), (`sn`,`sq`), (`sq`,`sr`),
     (`sr`,`st`), (`st`,`en`), (`en`,`sl`)] >> simp[]
QED

Theorem extrequest_tuple_cells_history:
  EVERY (extrequest_tuple_cell ctx func ce cx ee sa s ef) cells /\
  extrequest_history_frame ce cx ee sa s ee sb t ==>
  EVERY (extrequest_tuple_cell ctx func ce cx ee sb t ef) cells
Proof
  simp[EVERY_MEM] >> strip_tac >> rpt strip_tac >>
  first_x_assum drule >>
  PairCases_on `e` >> simp[extrequest_tuple_cell_def] >> strip_tac >>
  drule_all extrequest_strong_capture_history >> simp[]
QED

Theorem extrequest_tuple_prefix_endpoint:
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
    wb_frame ce ee sa s t /\ safe_operand sp bufop
Proof
  strip_tac >> drule extrequest_prefix_split >> strip_tac >> gvs[] >>
  `ZIP (MAP (\(e,r,vv,ty,tv,v). vv) cells,
        MAP (\(e,r,vv,ty,tv,v). ty) cells) =
    MAP (\(e,r,vv,ty,tv,v). (vv,ty)) cells` by
    (simp[rich_listTheory.ZIP_MAP_MAP] >> irule MAP_CONG >> simp[] >>
     rpt strip_tac >> PairCases_on `x` >> simp[]) >>
  drule_all extrequest_tuple_prefix_code >> strip_tac >>
  `32 <= MAX abisz retsz + 32` by decide_tac >>
  drule_all exprExtRequestPrefixOpsTheory.extrequest_alloc_selector_endpoint >> strip_tac >>
  rename1 `gas_marked_path F ctx func s 0 (OK q)` >>
  `EVERY (extrequest_tuple_cell ctx func ce cx ee sn q ee) cells` by
    (drule_all extrequest_tuple_cells_history >> simp[]) >>
  suspend "payload"
QED

Resume extrequest_tuple_prefix_endpoint[payload]:
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
  qpat_assum `EVERY (extrequest_tuple_cell ctx func ce cx ee sn q ee) cells`
    (mp_then Any mp_tac extrequest_tuple_payload_endpoint) >>
  simp[vyperABITheory.vyper_to_abi_def] >>
  disch_then (fn th =>
    qpat_assum `emit_op ADD [buf.buf_operand; Lit 32w] sr = (dst,st)`
      (mp_then Any mp_tac th)) >>
  simp[] >>
  disch_then (fn th =>
    qpat_assum `FLOOKUP q.vs_allocas sa.cs_next_id = SOME _`
      (mp_then Any mp_tac th)) >>
  simp[] >>
  disch_then (qspecl_then [`fname`, `env`, `ats`] mp_tac) >>
  simp[] >>
  (impl_tac >- (conj_tac >> first_assum MATCH_ACCEPT_TAC)) >> strip_tac >>
  rename1 `gas_marked_path F ctx func q 0 (OK t)` >>
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
  qexistsl_tac [`t`, `w`] >> simp[] >> suspend "frames"
QED

Resume extrequest_tuple_prefix_endpoint[frames]:
  markerLib.RESUME_TAC >> (
  conj_tac
  >- (rpt strip_tac >>
      `local_region ce ee.scopes q name p k` by
        (drule_all exprExtRequestHistoryTheory.extrequest_history_local_regions >>
         disch_then (qspecl_then [`k`, `name`, `p`] mp_tac) >> simp[]) >>
      fs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      fs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `aid < sn.cs_next_id /\ FLOOKUP q.vs_allocas aid = SOME (p,k)` by
        (fs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >> metis_tac[]) >>
      metis_tac[]) >>
  suspend "history")
QED

Resume extrequest_tuple_prefix_endpoint[history]:
  markerLib.RESUME_TAC >>
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
  simp[] >> drule extrequest_history_writeback >> simp[]
QED

Finalise extrequest_tuple_prefix_endpoint
