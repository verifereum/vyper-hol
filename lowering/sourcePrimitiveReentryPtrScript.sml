(* Source-valued primitive replay; physical and ghost observations share a run. *)
Theory sourcePrimitiveReentryPtr
Ancestors
  primitiveDecoderReentry sourcePrimitiveMemberPtr calldataDynOwned abiDecoderReentry
  sourceWordDecoderPtr sourceBytesRepresentation calldataTypedRobustPtr
  calldataWordPtr calldataDecodePtr abiDecoderContract abiDecoderBytes
  abiDecoderCoherence abiDecoderWordTyped abiCanonicalBytes
  bodyPtrDefs compileEnv venomState venomExecSemantics instIdxIndep
  vyperABI vyperTyping exprLowering valueEncoding valueEncodingProofs
  abiDecoderClamp ptrDiscipline fragExec finite_map words arithmetic list pred_set
  entryDecodeProps abiCanonicalHeadSize byte valueEncodingProps abiDecoderWordCopy abiStaticAggregateProps
  abiDecoderBytesTyped exprSimMemoryTransport exprSim

Theorem source_primitive_decoder_reentry_ptr:
  compile_abi_decode_to_buf (Var p) src CALLDATALOAD (Lit 0w) (Lit 0w) ei sa = ((),sb) /\
  abi_decoder_coherent ce env sf ty tv /\ type_to_abi_dec_info sf ce ty = ei /\
  value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
  ((?clamp. ei = DecPrimWord clamp /\ is_word_type ty /\ C = 32) \/
   (?m. ei = DecBytestring m /\ C = abi_decode_bytes_copy_size m /\ m < dimword (:256))) /\
  C < dimword (:256) /\
  eval_operand (Var p) s = SOME (n2w d) /\ d < dimword (:256) /\
  eval_operand src s = SOME (n2w srcpos) /\ srcpos < dimword (:256) /\
  mem_bytes_at srcpos (LENGTH (enc (vyper_to_abi_type env ty) av))
    s.vs_call_ctx.cc_calldata = enc (vyper_to_abi_type env ty) av /\
  fresh_vars_wrt limit s /\ sb.cs_next_var <= limit.cs_next_var /\
  not_fresh_at sa p /\ (!x. src = Var x ==> not_fresh_at sa x) /\
  ptr_covers G tn p s C /\ op_taint tn src = {} /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\ allocas_from lo s /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t H u.
    run_inst_seq (emitted_insts sa sb) s = OK (t with vs_inst_idx := s.vs_inst_idx) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ptr_covers H u p t C /\
    val_in_memory tv v d t.vs_memory /\
    (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==> val_in_memory tv v d mem) /\
    abi_decode_frame d C s t /\ fresh_vars_wrt limit t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!op w. (!x. op = Var x ==> not_fresh_at sa x) /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w) /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint u (Var x) = op_taint tn (Var x)) /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >- suspend "word" >> suspend "bytes"
QED

Resume source_primitive_decoder_reentry_ptr[word]:
  gvs[] >>
  `evaluate_type env ty = SOME tv` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  `abi_decoder_clamp_valid clamp (abi_decode_load CALLDATALOAD (n2w srcpos : bytes32) s)` by
    (irule coherent_source_word_clamp >> simp[abi_decode_source_def] >> metis_tac[]) >>
  `abi_decoder_operand_live sa.cs_next_var src /\
    abi_decoder_operand_live sa.cs_next_var (Var p)` by
    (Cases_on `src` >> gvs[calldata_operand_live_not_fresh, abi_decoder_operand_live_def]) >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all clamped_word_reentry_sequence >> strip_tac >>
  drule_all calldata_word_overwrite_prefix_uniform >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  gvs[] >>
  `abi_decode_load CALLDATALOAD (n2w srcpos : bytes32) s = typed_val_to_w256 tv v` by
    (drule_all vyper_to_abi_word_enc >> strip_tac >> gvs[] >>
     simp[abi_decode_load_bytes, abi_decode_source_def,
       LENGTH_word_to_bytes, word_of_bytes_word_to_bytes]) >>
  `val_in_memory tv v d t.vs_memory` by metis_tac[val_in_memory_word] >>
  `!op w. (!x. op = Var x ==> not_fresh_at sa x) /\ eval_operand op s = SOME w ==>
     eval_operand op t = SOME w` by
    (rpt strip_tac >> first_x_assum irule >> simp[] >>
     Cases_on `op` >> gvs[abi_decoder_operand_live_def, calldata_operand_live_not_fresh]) >>
  `!mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==> val_in_memory tv v d mem` by
    (rpt strip_tac >>
     `mem_bytes_at d 32 t.vs_memory = mem_bytes_at d 32 mem` by
       (irule LIST_EQ >> simp[] >> rpt strip_tac >> rename1 `j < 32` >>
        `d+j NOTIN tn'.t_mem` by (first_x_assum irule >> decide_tac) >>
        `mem_bytes_at (d+j) 1 t.vs_memory = mem_bytes_at (d+j) 1 mem` by
          (fs[mem_agree_outside_def] >> first_x_assum irule >> simp[]) >>
        pop_assum mp_tac >> simp[LIST_EQ_REWRITE, EL_mem_bytes_at]) >>
     metis_tac[val_in_memory_word, mem_word_at_bytes]) >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sb.cs_current_insts`,`G'`,`tn'`] >>
  fs[abi_decode_frame_def, fresh_vars_wrt_def, eval_operand_def, lookup_var_def,
    ptr_covers_def] >> gvs[]
QED

Resume source_primitive_decoder_reentry_ptr[bytes]:
  gvs[] >>
  `evaluate_type env ty = SOME tv` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  drule_all coherent_source_bytes_representation >> strip_tac >>
  `m + 32 <= abi_decode_bytes_copy_size m /\
    type_memory_size (BaseTV (BytesT (Dynamic m))) = abi_decode_bytes_copy_size m` by
    metis_tac[abi_decoder_bytes_copy_size] >>
  `mem_bytes_at srcpos (LENGTH (enc (contractABI$Bytes NONE) (contractABI$BytesV bs)))
    (abi_decode_source CALLDATALOAD s) = enc (contractABI$Bytes NONE) (contractABI$BytesV bs)` by
    gvs[abi_decode_source_def] >>
  `abi_decode_load CALLDATALOAD (n2w srcpos : bytes32) s = n2w (LENGTH bs)` by
    (irule canonical_bytes_count_load >> simp[]) >>
  `abi_decoder_operand_live sa.cs_next_var src /\
    abi_decoder_operand_live sa.cs_next_var (Var p)` by
    (Cases_on `src` >> gvs[calldata_operand_live_not_fresh, abi_decoder_operand_live_def]) >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all bytestring_sentinel_reentry_sequence >> strip_tac >>
  drule_all (SRULE [GSYM abi_decode_bytes_copy_size_def]
    (Q.INST [`C` |-> `abi_decode_bytes_copy_size m`]
      calldata_bytestring_overwrite_endpoint_core_uniform)) >>
  disch_then (qspec_then `PG` strip_assume_tac) >> gvs[] >>
  `val_in_memory (BaseTV (BytesT (Dynamic m))) (vyperValue$BytesV bs) d s'.vs_memory` by
    (irule canonical_bytes_copied_layout >> simp[] >>
     reverse conj_tac >- (simp[val_wf_def] >> decide_tac) >>
     qexistsl_tac [`abi_decode_bytes_copy_size m`,`srcpos`,`abi_decode_source CALLDATALOAD s`] >>
     gvs[GSYM (cj 2 abi_decoder_bytes_copy_size)]) >>
  `val_wf (BaseTV (BytesT (Dynamic m))) (vyperValue$BytesV bs)` by
    (simp[val_wf_def] >> decide_tac) >>
  `val_footprint (BaseTV (BytesT (Dynamic m))) (vyperValue$BytesV bs) <=
    abi_decode_bytes_copy_size m` by
    (simp[val_footprint_def] >> mp_tac (Q.SPEC `m` abi_decoder_bytes_copy_size) >> decide_tac) >>
  `!mem. mem_agree_outside tn'.t_mem s'.vs_memory mem ==>
    val_in_memory (BaseTV (BytesT (Dynamic m))) (vyperValue$BytesV bs) d mem` by
    (rpt strip_tac >> irule clean_footprint_val_in_memory_robust >>
     conj_tac >- simp[] >>
     qexistsl_tac [`s'.vs_memory`,`tn'.t_mem`] >> simp[] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  `!op w. (!x. op = Var x ==> not_fresh_at sa x) /\ eval_operand op s = SOME w ==>
     eval_operand op s' = SOME w` by
    (rpt strip_tac >> first_x_assum irule >> simp[] >>
     Cases_on `op` >> gvs[abi_decoder_operand_live_def, calldata_operand_live_not_fresh]) >>
  qexistsl_tac [`s'`,`G'`,`tn'`] >>
  fs[abi_decode_frame_def, fresh_vars_wrt_def] >> gvs[]
QED

Finalise source_primitive_decoder_reentry_ptr
