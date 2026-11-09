(* Output-buffer allocation and the continuing tuple encoder's write footprint. *)
Theory bodyIntCallFamStmtLogSuffixAllocated
Ancestors
  bodyIntCallFamStmtLogSuffixEncodeRun stmtSimLogStoreEncode stmtSimLogAllocate
  stmtSimLogSuffixActual stmtSimLogEncodeFields abiEncoderCounters abiEncoderInput
  abiBuiltinAllocation abiBuiltinEncodeStagedEffect abiDecoderFrame
  exprLoweringProps compileEnv emitHelperProps venomExecSemantics venomState
  localPtrsProps finite_map words list arithmetic

Theorem intcall_allocate_keeps_rows[local]:
  FLOOKUP s.vs_allocas aid = SOME r ==>
  FLOOKUP (abi_builtin_allocate_state site n s).vs_allocas aid = SOME r
Proof
  strip_tac >> simp[abi_builtin_allocate_state_def] >>
  Cases_on `FLOOKUP s.vs_allocas site = NONE` >> simp[FLOOKUP_UPDATE] >>
  Cases_on `site = aid` >> gvs[]
QED

Theorem intcall_log_allocated_tuple_footprint:
  compile_alloc_buffer outcap st = (dst,prepared) /\ fn_has_code st prepared func /\
  compile_abi_encode_to_buf dst.buf_operand src ei prepared = (out,end_st) /\
  fn_has_code prepared end_st func /\
  FLOOKUP initial.vs_allocas srcid = SOME (sb,srccap) /\
  srcid < st.cs_next_id /\ cap <= srccap /\ sb+srccap < dimword (:256) /\
  outcap < dimword (:256) /\
  abi_encoder_input ei (Tuple ats) (ListV avs) sb cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\
  abi_decoder_operand_live st.cs_next_var src /\
  stmt_state_rel ctx func ce cx es initial /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce st /\
  LENGTH (enc (Tuple ats) (ListV avs)) <= outcap /\
  ((?n. ei = AbiCopy n /\ n < dimword (:256)) \/
   (?infos. ei = AbiComplex infos /\ EXISTS (\(_,_,_,dyn). dyn) infos /\
      EVERY (\(child,asz,mz,dyn). log_scalar_enc_info child) infos)) ==>
  ?actual db p.
    run_inst_seq (emitted_insts st end_st) initial = OK actual /\
    inst_extends st end_st /\
    eval_operand dst.buf_operand actual = SOME (n2w db) /\
    mem_bytes_at db (LENGTH (enc (Tuple ats) (ListV avs))) actual.vs_memory =
      enc (Tuple ats) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Tuple ats) (ListV avs)))) /\
    stmt_state_rel ctx func ce cx es actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w) /\
    db < dimword (:256) /\
    abi_decode_footprint_frame
      ((db,outcap)::(if (?infos. ei = AbiComplex infos) then [(p,32)] else [])) initial actual /\
    FLOOKUP actual.vs_allocas st.cs_next_id = SOME (db,outcap) /\
    ((?infos. ei = AbiComplex infos) ==>
      FLOOKUP actual.vs_allocas prepared.cs_next_id = SOME (p,32)) /\
    (!aid r. FLOOKUP initial.vs_allocas aid = SOME r ==>
      FLOOKUP actual.vs_allocas aid = SOME r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qspecl_then [`initial`,`end_st`] strip_assume_tac log_fresh_limit_exists >>
  drule_all log_output_buffer_shape >> strip_tac >>
  drule_all abi_encoder_counters >> strip_tac >>
  `prepared.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all log_buffer_allocate >>
  disch_then (qx_choose_then `ready` (qx_choose_then `d` strip_assume_tac)) >>
  `!aid r. FLOOKUP initial.vs_allocas aid = SOME r ==>
      FLOOKUP ready.vs_allocas aid = SOME r` by
    (qpat_assum `abi_builtin_allocation_frame _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE[abi_builtin_allocation_frame_def]) >>
     simp[] >> rpt strip_tac >> irule intcall_allocate_keeps_rows >> simp[]) >>
  `FLOOKUP ready.vs_allocas srcid = SOME (sb,srccap)` by metis_tac[] >>
  `eval_operand src ready = SOME (n2w sb)` by metis_tac[] >>
  `abi_encoder_input ei (Tuple ats) (ListV avs) sb cap ready.vs_memory` by simp[] >>
  `abi_decoder_operand_live prepared.cs_next_var src` by
    (irule abiDecoderReentryTheory.abi_decoder_operand_live_mono >>
     qexists_tac `st.cs_next_var` >> simp[]) >>
  `sb+cap <= d \/ d+outcap <= sb` by
    (first_x_assum (qspecl_then [`srcid`,`sb`,`srccap`] mp_tac) >> simp[] >> decide_tac) >>
  drule_at (Pat `abi_encoder_input _ _ _ _ _ _`) intcall_log_tuple_execution_footprint >>
  disch_then drule >>
  disch_then (drule_at (Pat `eval_operand dst.buf_operand _ = _`)) >>
  disch_then (drule_at (Pat `compile_abi_encode_to_buf _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ srcid = _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `encoded` (qx_choose_then `p` strip_assume_tac)) >>
  `inst_extends prepared end_st` by
    (qpat_x_assum `(?n. ei = AbiCopy n /\ _) \/ _` strip_assume_tac >>
     gvs[] >> metis_tac[log_encode_copy_safe, log_encode_dynamic_safe]) >>
  `run_inst_seq (emitted_insts st end_st) initial = OK encoded` by
    (irule run_emitted_compose2 >> qexistsl_tac [`ready`,`prepared`] >>
     fs[inst_extends_def]) >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ ready` kall_tac >>
  drule_all log_allocated_tuple_encode_continue_bounded >>
  disch_then (qx_choose_then `actual` (qx_choose_then `db` strip_assume_tac)) >>
  `actual = encoded` by gvs[] >>
  qpat_x_assum `actual = encoded` SUBST_ALL_TAC >>
  `eval_operand dst.buf_operand encoded = SOME (n2w d)` by metis_tac[] >>
  `ready.vs_call_ctx = initial.vs_call_ctx /\
   ready.vs_data_section = initial.vs_data_section` by
    (qpat_assum `abi_builtin_allocation_frame _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE[abi_builtin_allocation_frame_def]) >>
     simp[abi_builtin_allocate_state_def]) >>
  `d < dimword (:256)` by decide_tac >>
  (qexistsl_tac [`encoded`,`d`,`p`] >>
  simp[] >> conj_tac
  >- (qpat_x_assum `abi_decode_footprint_frame _ ready encoded` mp_tac >>
      simp[abi_decode_footprint_frame_def]) >>
  Cases_on `?infos. ei = AbiComplex infos` >>
  simp[intcall_allocate_keeps_rows] >>
  rpt strip_tac >> first_x_assum irule >> simp[])
QED
