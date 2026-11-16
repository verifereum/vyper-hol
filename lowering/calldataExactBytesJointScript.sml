(* Exact bytes/string decoding with one source, runtime and ghost endpoint. *)
Theory calldataExactBytesJoint
Ancestors
  calldataBytesSourceExact defaultBytesDecodeExec calldataDecodePtr
  calldataFiniteTransport exprPtrCleanBufferPost abiDecoderFrameCompose
  abiDecoderCoherence abiDecoderReentry abiDecoderContract abiDecoderBytes
  abiDecoderBytesTyped abiDecoderString calldataSourceCorrespondence
  fragExecMem fragGasOriginPtr compileEnv loweringStateRelDefs
  venomExecSemantics venomState valueEncodingDefs valueEncoding
  vyperCalldata vyperValue vyperTyping exprLowering exprLoweringProps
  words arithmetic list finite_map

Theorem calldata_exact_bytes_shape[local]:
  abi_decoder_coherent ce env sf ty tv /\ is_bytestring_type ty ==>
  ?maxn. type_to_abi_dec_info sf ce ty = DecBytestring maxn /\
    type_memory_size tv = abi_decode_bytes_copy_size maxn /\
    (tv = BaseTV (BytesT (Dynamic maxn)) \/ tv = BaseTV (StringT maxn))
Proof
  strip_tac >> drule abi_decoder_coherent_header >>
  simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
  qpat_x_assum `evaluate_type env ty = SOME tv` mp_tac >>
  qpat_x_assum `is_bytestring_type ty` mp_tac >>
  rpt (pop_assum kall_tac) >>
  Cases_on `ty` >> simp[is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_bytestring_type_def] >>
  rpt strip_tac >> gvs[evaluate_type_def, is_bytestring_type_def, AllCaseEqs()] >>
  simp[type_to_abi_dec_info_def, type_memory_bytes_def, type_memory_size_def,
    abi_decode_bytes_copy_size_def, vfmConstantsTheory.word_size_def]
QED

Theorem calldata_exact_bytes_accepted_origin[local]:
  abi_decoder_coherent ce env sf ty tv /\ is_bytestring_type ty /\
  compile_abi_decode_to_buf (Var child) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) st = ((),last) /\
  fn_has_code st last fn /\ fn_inst_ids_distinct fn /\
  cd_decode F initial.vs_call_ctx.cc_calldata tv (w2n p) = SOME x /\
  eval_operand src initial = SOME p /\
  eval_operand (Var child) initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var child) /\
  ptr_covers G tn child initial (type_memory_size tv) /\ op_taint tn src = {} /\
  d+type_memory_size tv <= initial.vs_alloca_next /\
  d+type_memory_size tv < dimword (:256) /\
  allocas_from lower initial /\ ~ctx_has_dalloca ctx /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?v H u.
    run_inst_seq (emitted_insts st last) initial =
      OK (v with vs_inst_idx := initial.vs_inst_idx) /\
    ~v.vs_halted /\ v.vs_current_bb = last.cs_current_bb /\
    v.vs_inst_idx = LENGTH last.cs_current_insts /\
    value_has_type tv x /\ val_wf tv x /\ val_in_memory tv x d v.vs_memory /\
    (!mem. mem_agree_outside u.t_mem v.vs_memory mem ==>
      val_in_memory tv x d mem) /\
    v.vs_allocas = initial.vs_allocas /\
    v.vs_alloca_next = initial.vs_alloca_next /\
    ptr_covers H u child v (type_memory_size tv) /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!name. not_fresh_at st name ==>
      FLOOKUP H name = FLOOKUP G name /\
      op_taint u (Var name) = op_taint tn (Var name)) /\
    (!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,fn,PG)
      (initial,G,tn) [] (OK v,H,u))
Proof
  strip_tac >> drule_all calldata_exact_bytes_shape >> strip_tac >>
  `maxn < dimword (:256)` by
    (irule calldataBytesLiveTheory.abi_decode_bytes_extent_capacity_bound >> qexists `d` >> simp[]) >>
  `w2n (abi_decode_load CALLDATALOAD p initial) <= maxn` by
    (qpat_x_assum `cd_decode F _ _ _ = SOME x` mp_tac >>
     gvs[] >>
     simp[cd_decode_def, GSYM calldata_decode_load_word, AllCaseEqs()] >>
     rpt strip_tac >> gvs[]) >>
  drule_all default_bytes_decode_exact_sequence >> strip_tac >>
  `not_fresh_at st child /\ (!q. src = Var q ==> not_fresh_at st q)` by
    (gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       not_fresh_at_def] >> rpt strip_tac >> gvs[]) >>
  `type_memory_size tv = 32 + 32 * ((maxn+31) DIV 32)` by
    simp[abi_decode_bytes_copy_size_def] >>
  `type_memory_size tv < dimword (:256) /\ d < dimword (:256)` by
    decide_tac >>
  `abi_decode_load CALLDATALOAD p initial =
    n2w (w2n (abi_decode_load CALLDATALOAD p initial))` by simp[] >>
  `compile_abi_decode_to_buf (Var child) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecBytestring maxn) st = ((),last)` by metis_tac[] >>
  drule_all calldata_bytestring_overwrite_endpoint_core_uniform_origin_sequence >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `t = s' with vs_inst_idx := initial.vs_inst_idx` by metis_tac[exec_result_11] >>
  `val_in_memory tv x d s'.vs_memory` by fs[] >>
  gvs[wordsTheory.w2n_n2w] >>
  qexistsl [`s'`, `G'`, `tn'`] >> simp[] >>
  rpt strip_tac >> irule clean_window_value_robust >>
  (conj_tac >- fs[]) >>
  qexistsl [`tn'.t_mem`, `s'.vs_memory`, `abi_decode_bytes_copy_size maxn`] >>
  fs[wordsTheory.w2n_n2w]
QED
