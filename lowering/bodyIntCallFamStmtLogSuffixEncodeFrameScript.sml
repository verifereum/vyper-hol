(* Memory footprint retained from the scalar event encoder. *)
Theory bodyIntCallFamStmtLogSuffixEncodeFrame
Ancestors
  stmtSimLogStoreEncode stmtSimLogScalarEncode stmtSimLogSuffixActual
  stmtSimLogAllocate stmtSimLogAllocResource abiBuiltinAllocation
  abiDecoderFrame abiEncoderInput abiEncoderCounters localPtrsProps
  exprLoweringProps compileEnv venomExecSemantics venomState venomInst
  finite_map words list arithmetic

Theorem intcall_log_tuple_footprint:
  compile_alloc_buffer outcap st = (dst,prepared) /\
  compile_abi_encode_to_buf dst.buf_operand src ei prepared = (out,end_st) /\
  fn_has_code prepared end_st func /\
  FLOOKUP initial.vs_allocas srcid = SOME (sb,srccap) /\
  FLOOKUP initial.vs_allocas st.cs_next_id = SOME (db,outcap) /\
  srcid < st.cs_next_id /\ cap <= srccap /\ sb+srccap < dimword (:256) /\
  db+outcap < dimword (:256) /\ (sb+cap <= db \/ db+outcap <= sb) /\
  abi_encoder_input ei (Tuple ats) (ListV avs) sb cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\
  eval_operand dst.buf_operand initial = SOME (n2w db) /\
  abi_decoder_operand_live prepared.cs_next_var src /\
  stmt_state_rel ctx func ce cx es initial /\
  LENGTH (enc (Tuple ats) (ListV avs)) <= outcap /\
  ((?n. ei = AbiCopy n /\ n < dimword (:256)) \/
   (?infos. ei = AbiComplex infos /\ EXISTS (\(_,_,_,dyn). dyn) infos /\
      EVERY (\(child,asz,mz,dyn). log_scalar_enc_info child) infos)) ==>
  ?actual p.
    run_inst_seq (emitted_insts prepared end_st) initial = OK actual /\
    abi_decode_footprint_frame
      ((db,outcap)::(if (?infos. ei = AbiComplex infos) then [(p,32)] else [])) initial actual /\
    actual.vs_allocas =
      (if (?infos. ei = AbiComplex infos) then
        abi_builtin_allocate_state prepared.cs_next_id 32 initial else initial).vs_allocas /\
    actual.vs_alloca_next =
      (if (?infos. ei = AbiComplex infos) then
        abi_builtin_allocate_state prepared.cs_next_id 32 initial else initial).vs_alloca_next /\
    ((?infos. ei = AbiComplex infos) ==>
      FLOOKUP actual.vs_allocas prepared.cs_next_id = SOME (p,32))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule log_output_buffer_shape >> strip_tac >>
  `sb+cap < dimword (:256)` by decide_tac >>
  qspecl_then [`initial`,`end_st`] strip_assume_tac log_fresh_limit_exists >>
  Cases_on `?infos. ei = AbiComplex infos`
  >- (pop_assum strip_assume_tac >> gvs[] >>
      drule_all log_encoder_cursor_code >> strip_tac >>
      qmatch_asmsub_abbrev_tac `MEM inst (fn_insts func)` >>
      `inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit (n2w 32)]` by
        simp[Abbr `inst`, mk_inst_def] >>
      `32 < dimword (:256)` by
        (CONV_TAC (RAND_CONV wordsLib.SIZES_CONV) >> decide_tac) >>
      drule_all log_event_buffer_resource >> strip_tac >>
      `inst.inst_id = prepared.cs_next_id` by simp[Abbr `inst`, mk_inst_def] >>
      `srcid <> inst.inst_id /\ st.cs_next_id <> inst.inst_id` by decide_tac >>
      `sb+cap <= p \/ p+32 <= sb` by
        (first_x_assum (qspec_then `srcid` mp_tac) >> simp[] >> decide_tac) >>
      `db+outcap <= p \/ p+32 <= db` by
        (first_x_assum (qspec_then `st.cs_next_id` mp_tac) >> simp[] >> decide_tac) >>
      drule_at (Pat `abi_encoder_input _ _ _ _ _ _`) log_scalar_tuple_run >>
      disch_then drule >>
      disch_then (drule_at (Pat `eval_operand dst.buf_operand _ = _`)) >>
      disch_then (qspecl_then [`p`,`outcap`,`limit_st`] mp_tac) >>
      (impl_tac >- (fs[] >> decide_tac)) >>
      disch_then (qx_choose_then `actual` (map_every assume_tac o CONJUNCTS)) >>
      qexists_tac `actual` >> qexists_tac `p` >>
      gvs[abi_builtin_allocate_state_def, FLOOKUP_UPDATE]) >>
  drule_at (Pat `abi_encoder_input _ _ _ _ _ _`) log_scalar_tuple_run >>
  disch_then drule >>
  disch_then (drule_at (Pat `eval_operand dst.buf_operand _ = _`)) >>
  disch_then (qspecl_then [`0`,`outcap`,`limit_st`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexistsl_tac [`actual`,`0`] >> gvs[]
QED
