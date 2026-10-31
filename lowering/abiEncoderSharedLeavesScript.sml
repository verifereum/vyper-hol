Theory abiEncoderSharedLeaves
Ancestors
  abiEncoderSharedContract abiEncoderSequence abiScratchLeafEffect abiScratchEncoderContract
  abiEncoderExtendSim abiDecoderContract abiEncoderRegisteredEffect abiDecoderFrame venomMemDefs
  venomState venomExecSemantics instIdxIndep valueEncoding list arithmetic abiEncoderLeafGlobals
  abiEncoderOpenInput abiEncoderInput abiEncoderReentryLeaves abiEncoderLeafCode
  abiEncoderAdmissible abiEncoderBytes abiEncoderBytesCode abiDecoderAllocation abiDecoderLoop
  abiDecoderReentry abiEncoder compileEnv emitHelper contractABI words rich_list

(* Common straight-line endpoint: reuse the successful concrete execution. *)
Theorem abi_encoder_sequence_post_registered:
  abi_encoder_sequence_post at av out st limit_st d initial actual /\
  actual.vs_accounts = initial.vs_accounts /\ actual.vs_transient = initial.vs_transient /\
  actual.vs_logs = initial.vs_logs /\ actual.vs_requests = initial.vs_requests ==>
  abi_encoder_registered_effect ids [(d,LENGTH (enc at av))] initial actual
Proof
  simp_tac bool_ss [abi_encoder_sequence_post_def, abi_decode_frame_def,
    abi_encoder_registered_effect_def] >> strip_tac >>
  simp[] >> rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Theorem abi_encoder_sequence_post_alloca_inv:
  abi_encoder_sequence_post at av out st limit_st d initial actual /\
  alloca_inv initial ==> alloca_inv actual
Proof
  simp_tac bool_ss [abi_encoder_sequence_post_def] >> strip_tac >>
  fs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Theorem abi_encoder_shared_leaf_sequence:
  end_st.cs_blocks = start.cs_blocks /\ end_st.cs_current_bb = start.cs_current_bb /\
  inst_extends start end_st /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts start end_st) /\
  run_inst_seq (emitted_insts start end_st) initial = OK raw /\
  abi_encoder_sequence_post at av out start limit_st d initial raw /\
  raw.vs_accounts = initial.vs_accounts /\ raw.vs_transient = initial.vs_transient /\
  raw.vs_logs = initial.vs_logs /\ raw.vs_requests = initial.vs_requests /\
  fn_has_code start end_st func /\ abi_decoder_budget first last b cap initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  abi_encoder_shared_endpoint (ctx,func) (start,end_st,out,limit_st)
    (first,last,b,cap) (at,av,d) initial
    (raw with vs_inst_idx := LENGTH end_st.cs_current_insts)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_run_sequence_extend_sim >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule_all abi_encoder_run_sequence_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >> gvs[] >>
  `abi_scratch_effect first last start.cs_next_id end_st.cs_next_id start.cs_next_var
    limit_st d (LENGTH (enc at av)) b cap initial raw` by
    (irule abi_scratch_sequence_post_effect >> simp[] >> qexists_tac `out` >> simp[]) >>
  `abi_encoder_registered_effect (abi_decoder_ids start.cs_next_id end_st.cs_next_id)
    [(d,LENGTH (enc at av))] initial raw` by
    (irule abi_encoder_sequence_post_registered >> simp[] >>
     qexistsl_tac [`limit_st`, `out`, `start`] >> simp[]) >>
  `(alloca_inv initial ==> alloca_inv raw)` by
    (metis_tac[abi_encoder_sequence_post_alloca_inv]) >>
  fs[abi_encoder_shared_endpoint_def, abi_encoder_sequence_post_def,
    abi_scratch_effect_def, abi_encoder_registered_effect_def,
    eval_op_inst_idx, alloca_inv_def, allocas_non_overlapping_def,
    alloca_next_valid_def] >> metis_tac[]
QED

(* Shared leaf contracts use one concrete execution endpoint and its opcode certificate. *)
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
