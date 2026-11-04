(* Typed bytestring success from canonical input, without an assumed load value. *)
Theory abiDecoderBytesTyped
Ancestors
  venomMemProps
  abiDecoderBytes abiDecoderTypedContract abiCanonicalBytes abiCanonicalHeadSize
  abiDecoderContract abiDecoderFrame valueEncoding valueEncodingProps compileEnv
  vyperABI vyperTyping vyperValue contractABI vfmConstants words arithmetic
  abiEncoder emitHelper exprLoweringProps fragExec venomInst venomState rich_list

Theorem abi_decoder_bytes_copy_size:
  abi_decode_bytes_copy_size n = type_memory_bytes ce (BaseT (BytesT (Dynamic n))) /\
  abi_decode_bytes_copy_size n = type_memory_size (BaseTV (BytesT (Dynamic n))) /\
  n + 32 <= abi_decode_bytes_copy_size n
Proof
  pure_rewrite_tac[abi_decode_bytes_copy_size_def, type_memory_bytes_def,
    type_memory_size_def, word_size_def,
    Q.SPECL [`(n + 31) DIV 32`, `32`] MULT_COMM] >>
  simp[] >> irule (PURE_REWRITE_RULE [ceil32_def] le_ceil32)
QED

Theorem canonical_bytes_payload_length:
  32 + LENGTH bs <= LENGTH (enc (Bytes NONE) (contractABI$BytesV bs))
Proof
  pure_rewrite_tac[canonical_bytes_encoding] >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> simp[]
QED

Theorem abi_decoder_bytes_pre_facts:
  abi_decoder_pre ce env (BaseT (BytesT (Dynamic n))) (BaseTV (BytesT (Dynamic n)))
    (DecBytestring n) (contractABI$BytesV bs) (vyperValue$BytesV bs)
    st last src dst opc hi sb d b cap s ==>
  LENGTH bs <= n /\ n < dimword (:256) /\ sb < dimword (:256) /\ d < dimword (:256) /\
  abi_decode_bytes_copy_size n < dimword (:256) /\
  val_wf (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV bs) /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  fresh_vars_wrt st s /\ abi_decode_source_opcode opc /\
  (hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
                     sb + 32 + LENGTH bs <= h /\ h < dimword (:256)) /\
  mem_bytes_at sb (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)))
    (abi_decode_source opc s) = enc (Bytes NONE) (contractABI$BytesV bs)
Proof
  pure_rewrite_tac[abi_decoder_pre_def, abi_decoder_metadata_def, abi_decoder_ranges_def] >>
  strip_tac >>
  `n + 32 <= abi_decode_bytes_copy_size n` by
    (irule (cj 3 abi_decoder_bytes_copy_size)) >>
  `32 + LENGTH bs <= LENGTH (enc (Bytes NONE) (contractABI$BytesV bs))` by
    (irule canonical_bytes_payload_length) >>
  gvs[value_has_type_def, vyper_to_abi_type_def, vyper_base_to_abi_type_def,
      val_wf_def, type_memory_size_def, type_memory_bytes_def,
      abi_decode_bytes_copy_size_def, word_size_def] >>
  rpt strip_tac >> TRY (decide_tac) >>
  disj2_tac >> rename1 `eval_operand hi s = SOME (n2w hb)` >>
  qexists_tac `hb` >> simp[] >> decide_tac
QED

Theorem abi_decoder_typed_bytes_sequence:
  compile_abi_decode_to_buf dst src opc hi (DecBytestring n) st = ((),st') /\
  abi_decoder_pre ce env (BaseT (BytesT (Dynamic n))) (BaseTV (BytesT (Dynamic n)))
    (DecBytestring n) (contractABI$BytesV bs) (vyperValue$BytesV bs)
    st last src dst opc hi sb d b cap s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    abi_decoder_post (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV bs)
      st' d (abi_decode_bytes_copy_size n) b cap s t
Proof
  strip_tac >> drule abi_decoder_bytes_pre_facts >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_load opc (n2w sb : bytes32) s = n2w (LENGTH bs)` by
    (irule canonical_bytes_count_load >> asm_simp_tac bool_ss []) >>
  drule_all abi_decode_bytes_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') s = OK t` >>
  `val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV bs) d t.vs_memory` by
    (irule canonical_bytes_copied_layout >> asm_simp_tac bool_ss [] >>
     qexistsl_tac [`abi_decode_bytes_copy_size n`, `sb`, `abi_decode_source opc s`] >>
     asm_simp_tac bool_ss [GSYM (cj 2 abi_decoder_bytes_copy_size), LESS_EQ_REFL]) >>
  qexists_tac `t` >> simp[abi_decoder_post_def] >>
  irule abi_decoder_frame_from_output >> simp[]
QED

Theorem abi_decoder_post_inst_idx:
  abi_decoder_post tv v st' d outsz b cap s0 (t with vs_inst_idx := ix) <=>
  abi_decoder_post tv v st' d outsz b cap s0 t
Proof
  `!op. eval_operand op (t with vs_inst_idx := ix) = eval_operand op t` by
    (Cases >> simp[eval_operand_def, lookup_var_def]) >>
  simp[abi_decoder_post_def, fresh_vars_wrt_def,
       abi_decode_footprint_frame_def]
QED

Theorem abi_decoder_bytes_shape:
  compile_abi_decode_to_buf dst src opc hi (DecBytestring n) st = ((),st') /\
  abi_decode_source_opcode opc ==>
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts st'.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')
Proof
  strip_tac >> gvs[abi_decode_source_opcode_def] >> Cases_on `hi = Lit 0w` >>
  gvs[compile_abi_decode_to_buf_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
      fresh_id_def, emit_def, emitted_insts_def, IS_PREFIX_APPEND] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
  gvs[DROP_LENGTH_APPEND, is_terminator_def, mk_inst_def]
QED

Theorem abi_decoder_typed_bytes_fragment:
  compile_abi_decode_to_buf dst src opc hi (DecBytestring n) st = ((),st') ==>
  frag_exec ctx st st'
    (abi_decoder_pre ce env (BaseT (BytesT (Dynamic n))) (BaseTV (BytesT (Dynamic n)))
       (DecBytestring n) (contractABI$BytesV bs) (vyperValue$BytesV bs)
       st last src dst opc hi sb d b cap)
    (\t. ?s. abi_decoder_pre ce env (BaseT (BytesT (Dynamic n))) (BaseTV (BytesT (Dynamic n)))
       (DecBytestring n) (contractABI$BytesV bs) (vyperValue$BytesV bs)
       st last src dst opc hi sb d b cap s /\
       abi_decoder_post (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV bs)
         st' d (abi_decode_bytes_copy_size n) b cap s t)
    (K F)
Proof
  reverse (Cases_on `abi_decode_source_opcode opc`)
  >- simp[frag_exec_def, abi_decoder_pre_def, abi_decoder_ranges_def] >>
  strip_tac >> drule_all abi_decoder_bytes_shape >> strip_tac >>
  irule frag_exec_run_inst_seq >> simp[] >> rpt strip_tac >>
  drule_all abi_decoder_typed_bytes_sequence >> strip_tac >>
  qexists_tac `t` >> simp[abi_decoder_post_inst_idx] >> qexists_tac `s` >> simp[]
QED
