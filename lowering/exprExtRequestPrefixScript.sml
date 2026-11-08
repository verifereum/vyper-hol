(* Compiler stage boundary for the full request prefix. *)
Theory exprExtRequestPrefix
Ancestors
  exprExtRequestShape exprExtRequestPayload exprExtRequestHistoryCompose
  exprExtRequestTupleFold
  exprLoweringProps emitHelperProps compileEnv list fragExec venomExecSemantics venomState

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
    local_ptrs_reserved ce sp /\ safe_operand sp offset
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
  qexistsl_tac [`t`, `w`] >> simp[eval_operand_def] >>
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
