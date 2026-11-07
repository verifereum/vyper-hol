Theory exprSimAbiEncodeFramedLeaves
Ancestors
  exprSimAbiEncodeExecFrame abiEncoderWindowLeaves
  abiEncoderWindowContract abiEncoderLeaves abiEncoderWrites
  abiEncoderReentryLeaves moduleLoweringProps abiEncoderMemory
  abiEncoder abiEncoderOpenInput abiEncoderInput contractABI valueEncoding
  abiEncoderPrimitiveEffect abiEncoderExtendSim abiEncoderWindow
  abiEncoderRegisteredEffect valueEncodingProofs valueEncodingProps
  emitHelperProps exprLoweringProps localPtrsProps
  emitHelper compileEnv venomState venomExecSemantics venomInst words list
  abiEncoderWindowLookup

Theorem abi_encode_framed_copy_observed:
  compile_abi_encode_to_buf dst src (AbiCopy sz) st = (out,st') /\
  abi_encoder_window_pre ctx func st st' dst src (AbiCopy sz) at av sb cap d s ==>
  ?t. window_strong_result ctx func st st' out at av d s t /\
      abi_encode_exec_frame func s t
Proof
  strip_tac >>
  `!i b n. i IN window_alloca_sites func (frag_ids st st') /\
     FLOOKUP s.vs_allocas i = SOME (b,n) ==> n = 32` by
    metis_tac[window_pre_sites] >>
  pop_assum (mk_asm "sizes") >>
  drule abi_encode_copy_code >> strip_tac >>
  qpat_x_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encoder_window_pre_def]) >>
  fs[abi_encoder_window_copy_iff] >>
  qpat_x_assum `!inst b sz. _ ==> _` kall_tac >>
  `LENGTH (enc at av) = sz` by metis_tac[LENGTH_mem_bytes_at_proof] >>
  `s.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
  `sb < dimword (:256) /\ d < dimword (:256) /\ sz < dimword (:256)` by decide_tac >>
  `eval_operand (Lit (n2w sz)) s = SOME (n2w sz)` by simp[eval_operand_def] >>
  drule_all window_emit_copy_run >> strip_tac >>
  `abi_encoder_extend_sim ctx func s
    ((mcopy d sb sz s) with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    (irule abi_encoder_run_sequence_extend_sim >>
     (conj_tac >- first_assum ACCEPT_TAC) >> qexists_tac `st` >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `abi_encoder_registered_effect (window_alloca_sites func (frag_ids st st'))
    [(d,sz)] s ((mcopy d sb sz s) with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    (irule abi_encoder_registered_effect_trans >> qexists_tac `mcopy d sb sz s` >>
     simp[abi_encoder_registered_output_copy, abi_encoder_registered_inst_idx]) >>
  `abi_encoder_registered_effect (frag_ids st st') [(d,sz)] s
    ((mcopy d sb sz s) with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl_tac [`window_alloca_sites func (frag_ids st st')`, `[(d,sz)]`] >>
     simp[window_alloca_sites_subset]) >>
  qexists_tac `(mcopy d sb sz s) with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  reverse conj_tac >- simp[] >>
  simp_tac bool_ss [window_strong_result_def, abi_encoder_window_result_def] >>
  simp[eval_operand_def, mcopy_mem_bytes_at_same, abi_encoder_extend_sim_sim] >>
  mp_tac (Q.INST [`d` |-> `d`, `sb` |-> `sb`, `n` |-> `sz`,
    `ix` |-> `LENGTH st'.cs_current_insts`] window_copy_state_resources) >>
  simp[] >> strip_tac >> conj_tac >- asm "sizes" ACCEPT_TAC >>
  simp[mcopy_def, write_memory_with_expansion_def]
QED

Theorem abi_encode_framed_copy_contract:
  abi_encode_framed_contract (AbiCopy sz)
Proof
  rw[abi_encode_framed_contract_def] >> metis_tac[abi_encode_framed_copy_observed]
QED

Theorem abi_encode_framed_empty_observed:
  compile_abi_encode_to_buf dst src (AbiComplex []) st = (out,st') /\
  abi_encoder_window_pre ctx func st st' dst src (AbiComplex []) at av sb cap d s ==>
  ?t. window_strong_result ctx func st st' out at av d s t /\
      abi_encode_exec_frame func s t
Proof
  strip_tac >>
  `!i b n. i IN window_alloca_sites func (frag_ids st st') /\
     FLOOKUP s.vs_allocas i = SOME (b,n) ==> n = 32` by
    metis_tac[window_pre_sites] >>
  pop_assum (mk_asm "sizes") >>
  qpat_x_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encoder_window_pre_def]) >>
  qpat_x_assum `!inst b sz. _ ==> _` kall_tac >>
  gvs[Once compile_abi_encode_child_def, comp_return_def] >>
  `enc at av = []` by
    (fs[abi_encoder_window_complex_iff, abi_encoder_tuple_type_def,
       abi_encoder_member_span_def, enc_def, LET_THM, REV_DEF]) >>
  qexists_tac `s` >> simp[] >>
  simp[window_strong_result_def, abi_encoder_window_result_def,
    mem_bytes_at_def, eval_operand_def, abi_encoder_registered_effect_refl,
    abi_encoder_extend_sim_refl, abi_encoder_extend_sim_sim,
    window_alloca_growth_def] >>
  (conj_tac >- metis_tac[optionTheory.NOT_SOME_NONE]) >>
  asm "sizes" ACCEPT_TAC
QED

Theorem abi_encode_framed_empty_contract:
  abi_encode_framed_contract (AbiComplex [])
Proof
  rw[abi_encode_framed_contract_def] >> metis_tac[abi_encode_framed_empty_observed]
QED
