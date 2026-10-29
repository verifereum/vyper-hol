(* Shared leaf contracts use one concrete execution endpoint and its opcode certificate. *)
Theory abiEncoderSharedLeaves
Ancestors
  abiEncoderSharedLeafSequence abiEncoderLeafGlobals abiEncoderSharedContract
  abiEncoderOpenInput abiEncoderInput abiEncoderSequence abiEncoderReentryLeaves
  abiEncoderLeafCode abiEncoderAdmissible abiEncoderBytes abiEncoderBytesCode
  abiEncoderExtendSim abiEncoderRegisteredEffect abiScratchEncoderContract abiScratchLeafEffect
  abiDecoderContract abiDecoderAllocation abiDecoderLoop abiDecoderReentry
  abiEncoder compileEnv emitHelper venomState venomExecSemantics
  valueEncoding contractABI words list rich_list arithmetic

Theorem abi_encoder_open_word_typed:
  abi_encoder_open_input AbiPrimWord at av sb cap mem ==>
  abi_encoder_input AbiPrimWord at av sb cap mem
Proof
  simp[Once abi_encoder_open_input_cases, abi_encoder_input_word_iff]
QED

Theorem abi_encoder_open_copy_typed:
  abi_encoder_open_input (AbiCopy sz) at av sb cap mem ==>
  abi_encoder_input (AbiCopy sz) at av sb cap mem
Proof
  simp[Once abi_encoder_open_input_cases, abi_encoder_input_copy_iff]
QED

Theorem abi_encoder_open_bytes_typed:
  abi_encoder_open_input (AbiBytestring maxlen) at av sb cap mem ==>
  abi_encoder_input (AbiBytestring maxlen) at av sb cap mem
Proof
  simp[Once abi_encoder_open_input_cases, abi_encoder_input_bytes_iff] >>
  metis_tac[]
QED

Theorem abi_encoder_shared_word:
  abi_encoder_shared AbiPrimWord
Proof
  simp_tac bool_ss [abi_encoder_shared_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_shared_input _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_input_def]) >>
  drule abi_encoder_open_word_typed >> strip_tac >>
  `sb < dimword (:256) /\ d < dimword (:256)` by decide_tac >>
  drule_all abi_encoder_word_input_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts start end_st) initial = OK raw` >>
  `abi_encoder_sequence_post at av out start limit_st d initial raw` by
    asm_simp_tac bool_ss [abi_encoder_sequence_post_def] >>
  drule abi_encoder_word_global_code >> strip_tac >>
  drule_all abi_encoder_leaf_sequence_globals >> strip_tac >>
  mp_tac (Q.INST [`ei` |-> `AbiPrimWord`, `st` |-> `start`, `st'` |-> `end_st`]
    abi_encode_static_leaf_shape) >>
  (impl_tac >- simp[abi_encoder_static_leaf_def]) >> strip_tac >>
  qexists_tac `raw with vs_inst_idx := LENGTH end_st.cs_current_insts` >>
  irule abi_encoder_shared_leaf_sequence >> simp[]
QED

Theorem abi_encoder_shared_copy:
  abi_encoder_shared (AbiCopy sz)
Proof
  simp_tac bool_ss [abi_encoder_shared_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_shared_input _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_input_def]) >>
  drule abi_encoder_open_copy_typed >> strip_tac >>
  `LENGTH (enc at av) = sz` by
    (qpat_assum `abi_encoder_input _ _ _ _ _ _`
      (MAP_EVERY assume_tac o CONJUNCTS o REWRITE_RULE [abi_encoder_input_copy_iff]) >>
     drule_all (cj 1 enc_has_static_length) >> simp[]) >>
  `sb < dimword (:256) /\ d < dimword (:256) /\ sz < dimword (:256)` by decide_tac >>
  drule_all abi_encoder_copy_input_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts start end_st) initial = OK raw` >>
  `abi_encoder_sequence_post at av out start limit_st d initial raw` by
    asm_simp_tac bool_ss [abi_encoder_sequence_post_def] >>
  drule abi_encoder_copy_global_code >> strip_tac >>
  drule_all abi_encoder_leaf_sequence_globals >> strip_tac >>
  mp_tac (Q.INST [`ei` |-> `AbiCopy sz`, `st` |-> `start`, `st'` |-> `end_st`]
    abi_encode_static_leaf_shape) >>
  (impl_tac >- simp[abi_encoder_static_leaf_def]) >> strip_tac >>
  qexists_tac `raw with vs_inst_idx := LENGTH end_st.cs_current_insts` >>
  irule abi_encoder_shared_leaf_sequence >> simp[]
QED

Theorem abi_encoder_shared_bytes:
  abi_encoder_shared (AbiBytestring maxlen)
Proof
  simp_tac bool_ss [abi_encoder_shared_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_shared_input _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_input_def]) >>
  drule abi_encoder_open_bytes_typed >> strip_tac >>
  `sb < dimword (:256)` by decide_tac >>
  `sb + source_cap <= d \/ d + LENGTH (enc at av) <= sb` by
    (qpat_assum `abi_encoder_input _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [abi_encoder_input_bytes_iff]) >>
     `LENGTH (enc at av) = 32 + contractABI$ceil32 (LENGTH bs)` by
       simp[cj 2 abi_encoder_bytes_encoding, abi_encoder_bytes_padded_length] >>
     qpat_x_assum `venomMemDefs$regions_disjoint _ _` mp_tac >>
     pure_rewrite_tac [venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  drule_at (Pos (el 2)) abi_encoder_bytes_sequence >>
  disch_then drule >>
  disch_then (qspecl_then [`limit_st`, `d`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac []) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts start end_st) initial = OK raw` >>
  `abi_encoder_sequence_post at av out start limit_st d initial raw` by
    asm_simp_tac bool_ss [abi_encoder_sequence_post_def] >>
  drule abi_encoder_bytes_global_code >> strip_tac >>
  drule_all abi_encoder_leaf_sequence_globals >> strip_tac >>
  drule abi_encode_bytes_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts start end_st)` by fs[EVERY_CONJ] >>
  qexists_tac `raw with vs_inst_idx := LENGTH end_st.cs_current_insts` >>
  irule abi_encoder_shared_leaf_sequence >> simp[]
QED

Theorem abi_encoder_shared_empty:
  abi_encoder_shared (AbiComplex [])
Proof
  simp_tac bool_ss [abi_encoder_shared_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  gvs[Once compile_abi_encode_child_def, comp_return_def] >>
  qpat_assum `abi_encoder_shared_input _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_input_def]) >>
  `enc at av = []` by
    (fs[abi_encoder_open_complex_iff, abi_encoder_tuple_type_def,
       abi_encoder_member_span_def, enc_def, LET_THM, REV_DEF]) >>
  `abi_scratch_effect first last end_st.cs_next_id end_st.cs_next_id end_st.cs_next_var
    limit_st d (LENGTH (enc at av)) b cap initial initial` by
    (irule abi_scratch_leaf_effect >> simp[abi_decode_frame_def]) >>
  qexists_tac `initial` >>
  simp[abi_encoder_shared_endpoint_def, mem_bytes_at_def, eval_operand_def,
    abi_encoder_registered_effect_refl, abi_encoder_extend_sim_refl]
QED
