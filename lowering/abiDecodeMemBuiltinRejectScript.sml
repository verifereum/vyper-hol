(* The builtin's invalid source-length branch precedes recursive decoding. *)
Theory abiDecodeMemBuiltinReject
Ancestors
  abiDecodeMemHeaderReject exprSimAbiDecodeBuiltin exprSimAbiDecodeBuiltinLayout
  abiBuiltinDecodeSetup abiBuiltinDecodeHeader abiBuiltinAllocation
  abiDecoderAppend abiDecoderCounters abiDecoderReentry abiDecoderContract actualDecoderSites
  freshVarLimit exprLoweringProps emitHelperProps fragExec
  valueEncodingDefs valueEncodingProps compileEnv venomExecSemantics venomState
  words list arithmetic

Theorem abi_decode_mem_builtin_reject:
  lower_abi_decode data (type_to_abi_dec_info sf ce ty)
    (abi_static_size sf ty) (abi_size_bound sf ty) (type_memory_bytes ce ty)
    st = (out,fin) /\
  abi_decoder_coherent ce env sf ty tv /\ fn_has_code st fin func /\
  abi_builtin_decode_site_resources ctx func st fin.cs_next_id
    (abi_static_size sf ty) (abi_size_bound sf ty) (type_memory_bytes ce ty)
    (LENGTH bs) p d s /\
  val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) p s.vs_memory /\
  eval_operand data s = SOME(n2w p) /\
  abi_decoder_operand_live st.cs_next_var data /\
  ~(abi_static_size sf ty <= LENGTH bs /\ LENGTH bs <= abi_size_bound sf ty) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  evaluate_abi_decode env ty bs = INR "abi_decode invalid" /\
  ?t. gas_marked_path T ctx func s 0 (Abort Revert_abort t)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `evaluate_abi_decode env ty bs = INR "abi_decode invalid"` by
    metis_tac[abi_decode_builtin_guard_reject] >> simp[] >>
  drule lower_abi_decode_bounded_setup >> strip_tac >>
  Cases_on `decoded` >> gvs[] >>
  drule abi_builtin_decode_setup_shape >> strip_tac >>
  `cs_extends st ready /\ cs_extends ready fin` by
    metis_tac[cs_extends_same_block, cs_extends_abi_decode] >>
  drule_all fn_has_code_split >> strip_tac >>
  `ready.cs_next_var <= fin.cs_next_var` by
    metis_tac[abi_decoder_variable_counter] >>
  drule abi_builtin_decode_setup_trace >> strip_tac >>
  drule abi_builtin_decode_header_shape >> strip_tac >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >>
  `cs_extends st header_st /\ cs_extends header_st ready` by
    (conj_tac >> irule cs_extends_same_block >> simp[]) >>
  `fn_has_code st header_st func` by metis_tac[fn_has_code_split] >>
  qspecl_then [`s`, `fin`] strip_assume_tac log_fresh_limit_exists >>
  `header_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `p+32+LENGTH bs <= s.vs_alloca_next /\
   abi_size_bound sf ty < dimword(:256) /\ decode_site_resources ctx func s` by
    fs[abi_builtin_decode_site_resources_def] >>
  `s.vs_alloca_next < dimword(:256)` by
    (irule alloca_room_next_lt >> metis_tac[decode_site_resources_def]) >>
  `p < dimword(:256) /\ LENGTH bs < dimword(:256) /\
   abi_static_size sf ty < dimword(:256)` by
    (`abi_static_size sf ty <= abi_size_bound sf ty` by
       simp[abi_decode_builtin_min_le_max] >> decide_tac) >>
  `mload (w2n (n2w p:bytes32)) s = n2w (LENGTH bs)` by
    fs[val_in_memory_def, mem_word_at_eq_mload, w2n_n2w] >>
  `w2n (n2w p:bytes32)+32 <= s.vs_alloca_next` by simp[w2n_n2w] >>
  `~(abi_static_size sf ty <= LENGTH bs /\ LENGTH bs <= abi_size_bound sf ty)` by
    simp[] >>
  drule_all abi_decode_header_reject_path_mem >> simp[]
QED
